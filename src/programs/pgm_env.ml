
open Why
open Util
open Ident
open Theory
open Term
open Ty
module E = Pgm_effect

(* types *)

type effect = E.t
type reference = Pgm_effect.reference

type pre = Term.fmla

type post_fmla = Term.vsymbol (* result *) * Term.fmla
type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla

type post = post_fmla * (Term.lsymbol * exn_post_fmla) list

type type_v = 
  | Tpure of Ty.ty
  | Tarrow of binder list * type_c

and type_c = 
  { c_result_type : type_v;
    c_effect      : effect;
    c_pre         : pre;
    c_post        : post; }

and binder = Term.vsymbol * type_v

(* environments *)

type env = {
  uc      : theory_uc;
(***
  globals : type_v Mls.t;
  locals  : type_v Mvs.t;
***)
  globals : (lsymbol * type_v) Mstr.t;
  exceptions : lsymbol Mstr.t;
  ts_arrow: tysymbol;
  ts_bool : tysymbol;
  ts_label: tysymbol;
  ts_ref: tysymbol;
  ts_exn: tysymbol;
  ts_unit : tysymbol;
  ls_at : lsymbol;
  ls_bang : lsymbol;
  ls_old : lsymbol;
  ls_True : lsymbol;
  ls_False: lsymbol;
  ls_andb : lsymbol;
  ls_orb  : lsymbol;
  ls_notb : lsymbol;
  ls_unit : lsymbol;
}


(* prelude *)

let find_ts uc = ns_find_ts (get_namespace uc)
let find_ls uc = ns_find_ls (get_namespace uc)

(* predefined lsymbols are memoized wrt the lsymbol for type "ref" *)
let memo_ls f =
  let h = Hts.create 17 in
  fun uc ->
    let ts_ref = find_ts uc ["ref"] in
    try Hts.find h ts_ref
    with Not_found -> let s = f uc ts_ref in Hts.add h ts_ref s; s

(* logic ref ('a) : 'a ref *)
let ls_ref = memo_ls 
  (fun _uc ts_ref ->
     let a = ty_var (create_tvsymbol (id_fresh "a")) in
     create_lsymbol (id_fresh "ref") [a] (Some (ty_app ts_ref [a])))

(* logic (:=)('a ref, 'a) : unit *)
let ls_assign = memo_ls
  (fun uc ts_ref ->
     let ty_unit = ty_app (find_ts uc ["unit"]) [] in
     let a = ty_var (create_tvsymbol (id_fresh "a")) in
     create_lsymbol (id_fresh "infix :=") [ty_app ts_ref [a]; a] (Some ty_unit))

let ls_Exit = memo_ls
  (fun uc _ ->
     let ty_exn = ty_app (find_ts uc ["exn"]) [] in
     create_lsymbol (id_fresh "%Exit") [] (Some ty_exn))
     

let v_result ty = create_vsymbol (id_fresh "result") ty

let add_type_v_ref uc m =
  let ts_ref = find_ts uc ["ref"] in
  let a = ty_var (create_tvsymbol (id_fresh "a")) in
  let x = create_vsymbol (id_fresh "x") a in
  let ty = ty_app ts_ref [a] in
  let result = v_result ty in
  let q = f_equ (t_app (find_ls uc ["prefix !"]) [t_var result] a) (t_var x) in
  let c = { c_result_type = Tpure ty;
	    c_effect      = Pgm_effect.empty;
	    c_pre         = f_true;
	    c_post        = (result, q), []; } in
  let v = Tarrow ([x, Tpure a], c) in
  Mstr.add "ref" (ls_ref uc, v) m

let add_type_v_assign uc m =
  let ts_ref = find_ts uc ["ref"] in
  let a = ty_var (create_tvsymbol (id_fresh "a")) in
  let a_ref = ty_app ts_ref [a] in
  let x = create_vsymbol (id_fresh "x") a_ref in
  let y = create_vsymbol (id_fresh "y") a in
  let ty = ty_app (find_ts uc ["unit"]) [] in
  let result = v_result ty in
  let q = f_equ (t_app (find_ls uc ["prefix !"]) [t_var x] a) (t_var y) in
  let c = { c_result_type = Tpure ty;
	    c_effect      = E.add_write (E.Rlocal x) E.empty;
	    c_pre         = f_true;
	    c_post        = (result, q), []; } in
  let v = Tarrow ([x, Tpure a_ref; y, Tpure a], c) in
  Mstr.add "infix :=" (ls_assign uc, v) m

let empty_env uc = { 
  uc = uc; 
  globals = add_type_v_ref uc (add_type_v_assign uc Mstr.empty);
  exceptions = Mstr.add "%Exit" (ls_Exit uc) Mstr.empty;
  (* types *)
  ts_arrow = find_ts uc ["arrow"];
  ts_bool  = find_ts uc ["bool"];
  ts_label = find_ts uc ["label"];
  ts_ref   = find_ts uc ["ref"];
  ts_exn   = find_ts uc ["exn"];
  ts_unit  = find_ts uc ["tuple0"];
  (* functions *)
  ls_at    = find_ls uc ["at"];
  ls_bang  = find_ls uc ["prefix !"];
  ls_old   = find_ls uc ["old"];
  ls_True  = find_ls uc ["True"];
  ls_False = find_ls uc ["False"];
  ls_andb  = find_ls uc ["andb"];
  ls_orb   = find_ls uc ["orb"];
  ls_notb  = find_ls uc ["notb"];
  ls_unit  = find_ls uc ["Tuple0"];
}    

let make_arrow_type env tyl ty =
  let arrow ty1 ty2 = Ty.ty_app env.ts_arrow [ty1; ty2] in
  List.fold_right arrow tyl ty

let rec uncurry_type = function
  | Tpure ty -> 
      [], ty
  | Tarrow (bl, c) -> 
      let tyl1 = List.map (fun (v,_) -> v.vs_ty) bl in
      let tyl2, ty = uncurry_type c.c_result_type in
      tyl1 @ tyl2, ty (* TODO: improve? *)

let purify env v =
  let tyl, ty = uncurry_type v in 
  make_arrow_type env tyl ty

(* parsing LOGIC strings using functions from src/parser/
   requires proper relocation *)

let reloc loc lb =
  lb.Lexing.lex_curr_p <- loc;
  lb.Lexing.lex_abs_pos <- loc.Lexing.pos_cnum

let parse_string f loc s =
  let lb = Lexing.from_string s in
  reloc loc lb;
  f lb

let logic_lexpr ((pos, _), s) =
  parse_string Lexer.parse_lexpr pos s

let logic_decls ((loc, _), s) e env =
  let parse = Lexer.parse_list0_decl e Mnm.empty env.uc in
  { env with uc = parse_string parse loc s }

(* addition *)

let add_global id tyv env = 
  let tyl, ty = uncurry_type tyv in
  let s = create_lsymbol id tyl (Some ty) in
  s, { env with globals = Mstr.add s.ls_name.id_string (s, tyv) env.globals }

let add_decl d env = 
  { env with uc = Typing.with_tuples add_decl env.uc d }

let add_exception id ty env =
  let tyl = match ty with None -> [] | Some ty -> [ty] in
  let s = create_lsymbol id tyl (Some (ty_app env.ts_exn [])) in
  s, { env with exceptions = Mstr.add s.ls_name.id_string s env.exceptions }

(* misc. functions *)

let post_map f ((v, q), ql) = 
  (v, f q), List.map (fun (e,(v,q)) -> e, (v, f q)) ql

let type_c_of_type_v env = function
  | Tarrow ([], c) ->
      c
  | v ->
      let ty = purify env v in
      { c_result_type = v;
	c_effect      = Pgm_effect.empty;
	c_pre         = f_true;
	c_post        = (v_result ty, f_true), []; }

let rec subst_var ts s vs =
  let ty' = ty_inst ts vs.vs_ty in
  if ty_equal ty' vs.vs_ty then
    s, vs
  else
    let vs' = create_vsymbol (id_clone vs.vs_name) ty' in
    Mvs.add vs (t_var vs') s, vs'

and subst_post ts s ((v, q), ql) =
  let vq = let s, v = subst_var ts s v in v, f_ty_subst ts s q in
  let handler (e, (v, q)) = match v with
    | None -> e, (v, f_ty_subst ts s q)
    | Some v -> let s, v = subst_var ts s v in e, (Some v, f_ty_subst ts s q)
  in
  vq, List.map handler ql
  
let rec subst_type_c ef ts s c = 
  { c_result_type = subst_type_v ef ts s c.c_result_type;
    c_effect      = E.subst ef c.c_effect;
    c_pre         = f_ty_subst ts s c.c_pre;
    c_post        = subst_post ts s c.c_post; }

and subst_type_v ef ts s = function
  | Tpure ty -> 
      Tpure (ty_inst ts ty)
  | Tarrow (bl, c) -> 
      let s, bl = Util.map_fold_left (binder ef ts) s bl in
      Tarrow (bl, subst_type_c ef ts s c)

and binder ef ts s (vs, v) =
  let v = subst_type_v ef ts s v in
  let s, vs = subst_var ts s vs in
  s, (vs, v)

let tpure ty = Tpure ty

let tarrow bl c = match bl with
  | [] -> 
      invalid_arg "tarrow"
  | _ -> 
      let rename (e, s) (vs, v) = 
	let vs' = create_vsymbol (id_clone vs.vs_name) vs.vs_ty in
	let v' = subst_type_v e Mtv.empty s v in
	let e' = Mvs.add vs (E.Rlocal vs') e in
	let s' = Mvs.add vs (t_var vs') s in
	(e', s'), (vs', v')
      in
      let (e, s), bl' = Util.map_fold_left rename (Mvs.empty, Mvs.empty) bl in
      Tarrow (bl', subst_type_c e Mtv.empty s c)


let subst1 vs1 t2 = Mvs.add vs1 t2 Mvs.empty

let apply_type_v env v vs = match v with
  | Tarrow ((x, tyx) :: bl, c) ->
      let ts = ty_match Mtv.empty (purify env tyx) vs.vs_ty in
      let c = type_c_of_type_v env (Tarrow (bl, c)) in
      subst_type_c Mvs.empty ts (subst1 x (t_var vs)) c
  | Tarrow ([], _) | Tpure _ -> 
      assert false

let apply_type_v_ref env v r = match r, v with
  | E.Rlocal vs as r, Tarrow ((x, tyx) :: bl, c) ->
      let ts = ty_match Mtv.empty (purify env tyx) vs.vs_ty in
      let c = type_c_of_type_v env (Tarrow (bl, c)) in
      let ef = Mvs.add x r Mvs.empty in
      subst_type_c ef ts (subst1 x (t_var vs)) c
  | E.Rglobal ls as r, Tarrow ((x, tyx) :: bl, c) -> 
      let ty = match ls.ls_value with None -> assert false | Some ty -> ty in
      let ts = ty_match Mtv.empty (purify env tyx) ty in
      let c = type_c_of_type_v env (Tarrow (bl, c)) in
      let ef = Mvs.add x r Mvs.empty in
      subst_type_c ef ts (subst1 x (t_app ls [] ty)) c
  | _ ->
      assert false

let occur_formula r f = match r with
  | E.Rlocal vs  -> f_occurs_single vs f
  | E.Rglobal ls -> f_s_any (fun _ -> false) (ls_equal ls) f

let rec occur_type_v r = function
  | Tpure _ ->
      false
  | Tarrow (bl, c) ->
      occur_arrow r bl c

and occur_arrow r bl c = match bl with
  | [] -> 
      occur_type_c r c
  | (vs, v) :: bl -> 
      occur_type_v r v || 
      not (E.ref_equal r (E.Rlocal vs)) && occur_arrow r bl c

and occur_type_c r c = 
  occur_type_v r c.c_result_type ||
  occur_formula r c.c_pre ||
  E.occur r c.c_effect ||
  occur_post r c.c_post

and occur_post r ((_, q), ql) =
  occur_formula r q ||
  List.exists (fun (_, (_, qe)) -> occur_formula r qe) ql

let rec eq_type_v v1 v2 = match v1, v2 with
  | Tpure ty1, Tpure ty2 ->
      ty_equal ty1 ty2
  | Tarrow _, Tarrow _ ->
      false (* TODO? *)
  | _ ->
      assert false

let t_True env =
  t_app env.ls_True [] (ty_app env.ts_bool [])

let type_v_unit env =
  Tpure (ty_app env.ts_unit [])

(* pretty-printers *)

open Pp
open Format
open Pretty 

let print_post fmt ((_,q), el) =
  let print_exn_post fmt (l,(_,q)) = 
    fprintf fmt "| %a -> {%a}" print_ls l print_fmla q 
  in
  fprintf fmt "{%a} %a" print_fmla q (print_list space print_exn_post) el

let rec print_type_v fmt = function
  | Tpure ty -> 
      print_ty fmt ty
  | Tarrow (bl, c) ->
      fprintf fmt "@[<hov 2>%a ->@ %a@]" 
	(print_list arrow print_binder) bl print_type_c c

and print_type_c fmt c =
  fprintf fmt "@[{%a}@ %a%a@ %a@]" print_fmla c.c_pre
    print_type_v c.c_result_type Pgm_effect.print c.c_effect
    print_post c.c_post

and print_binder fmt (x, v) =
  fprintf fmt "(%a:%a)" print_vs x print_type_v v

(* let apply_type_v env v vs = *)
(*   eprintf "apply_type_v: v=%a vs=%a@." print_type_v v print_vs vs; *)
(*   apply_type_v env v vs *)


(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
