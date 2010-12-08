
open Why
open Util
open Ident
open Theory
open Term
open Ty
module E = Pgm_effect

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
  ls_lt   : lsymbol;
  ls_gt   : lsymbol;
  ls_le   : lsymbol;
  ls_ge   : lsymbol;
  ls_add  : lsymbol;
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
  ls_lt    = find_ls uc ["infix <"];
  ls_gt    = find_ls uc ["infix >"];
  ls_le    = find_ls uc ["infix <="];
  ls_ge    = find_ls uc ["infix >="];
  ls_add   = find_ls uc ["infix +"];
}

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

let t_True env =
  t_app env.ls_True [] (ty_app env.ts_bool [])

let type_v_unit env =
  Tpure (ty_app env.ts_unit [])

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
