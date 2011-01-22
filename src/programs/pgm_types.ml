
open Why
open Util
open Ident
open Ty
open Theory
open Term
open Decl

(* mutable types *)

type mtsymbol = {
  mt_name  : ident;
  mt_args  : tvsymbol list;
  mt_model : ty option;
  mt_abstr : tysymbol;
}

let mt_equal : mtsymbol -> mtsymbol -> bool = (==)

let mutable_types = Hts.create 17

let create_mtsymbol name args model = 
  let id = id_register name in
  let ts = create_tysymbol name args None in
  let mt = 
    { mt_name  = id;
      mt_args  = args;
      mt_model = model; 
      mt_abstr = ts; }
  in
  Hts.add mutable_types ts mt;
  mt

let is_mutable_ts = Hts.mem mutable_types

let is_mutable_ty ty = match ty.ty_node with
  | Ty.Tyapp (ts, _) -> is_mutable_ts ts
  | Ty.Tyvar _ -> false

exception NotMutable

let get_mtsymbol ts = 
  try Hts.find mutable_types ts with Not_found -> raise NotMutable

let model_type ty = match ty.ty_node with
  | Tyapp (ts, tyl) when Hts.mem mutable_types ts ->
      let mt = Hts.find mutable_types ts in
      begin match mt.mt_model with
	| None -> 
	    ty
	| Some ty ->
	    let add mtv tv ty = Mtv.add tv ty mtv in
	    let mtv = List.fold_left2 add Mtv.empty mt.mt_args tyl in
	    ty_inst mtv ty
      end
  | Tyvar _ | Tyapp _ -> 
      raise NotMutable

(* types *)

let ts_exn = Ty.create_tysymbol (id_fresh "exn") [] None
let ty_exn = Ty.ty_app ts_exn []

(* let ts_label = Ty.create_tysymbol (id_fresh "label") [] None *)

let ts_arrow = 
  let v = List.map (fun s -> create_tvsymbol (Ident.id_fresh s)) ["a"; "b"] in
  Ty.create_tysymbol (Ident.id_fresh "arrow") v None

let make_arrow_type tyl ty =
  let arrow ty1 ty2 = Ty.ty_app ts_arrow [ty1; ty2] in
  List.fold_right arrow tyl ty
      
module Sexn = Term.Sls

module rec T : sig

  type pre = Term.fmla

  type post_fmla = Term.vsymbol (* result *) * Term.fmla
  type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla
      
  type esymbol = lsymbol

  type post = post_fmla * (esymbol * exn_post_fmla) list

  type type_v = private
  | Tpure    of ty
  | Tarrow   of pvsymbol list * type_c

  and type_c = { 
    c_result_type : type_v;
    c_effect      : E.t;
    c_pre         : pre;
    c_post        : post; 
  }
      
  and pvsymbol = private {
    pv_name : ident;
    pv_tv   : type_v;
    pv_ty   : ty;      (* as a logic type, for typing purposes only *)
    pv_vs   : vsymbol; (* for use in the logic *)
  }

  val tpure  : ty -> type_v
  val tarrow : pvsymbol list -> type_c -> type_v

  val create_pvsymbol : preid -> ?vs:vsymbol -> type_v -> pvsymbol

  val compare_pvsymbol : pvsymbol -> pvsymbol -> int

  (* program symbols *)

  type psymbol = private {
    p_name : ident;
    p_tv   : type_v;
    p_ty   : ty;      (* as a logic type, for typing purposes only *)
    p_ls   : lsymbol; (* for use in the logic *) 
  }
      
  val create_psymbol : preid -> type_v -> psymbol

  val p_equal : psymbol -> psymbol -> bool

  (* program types -> logic types *)

  val purify : ty -> ty

  val purify_type_v : ?logic:bool -> type_v -> ty
    (** when [logic] is [true], mutable types are turned into their models *)
    
  (* operations on program types *)
    
  val apply_type_v_var : type_v -> pvsymbol -> type_c
  val apply_type_v_sym : type_v -> psymbol  -> type_c
  val apply_type_v_ref : type_v -> R.t      -> type_c
    
  val occur_type_v : R.t -> type_v -> bool
    
  val v_result : ty -> vsymbol
  val exn_v_result : Why.Term.lsymbol -> Why.Term.vsymbol option
    
  val post_map : (fmla -> fmla) -> post -> post
    
  val subst1 : vsymbol -> term -> term Mvs.t
    
  val eq_type_v : type_v -> type_v -> bool

  (* pretty-printers *)

  val print_type_v : Format.formatter -> type_v -> unit
  val print_type_c : Format.formatter -> type_c -> unit
  val print_pre    : Format.formatter -> pre    -> unit
  val print_post   : Format.formatter -> post   -> unit

end = struct

  type pre = Term.fmla

  type post_fmla = Term.vsymbol (* result *) * Term.fmla
  type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla

  type esymbol = lsymbol

  type post = post_fmla * (esymbol * exn_post_fmla) list
      
  type type_v =
    | Tpure    of Ty.ty
    | Tarrow   of pvsymbol list * type_c

  and type_c = { 
    c_result_type : type_v;
    c_effect      : E.t;
    c_pre         : pre;
    c_post        : post; 
  }

  and pvsymbol = {
    pv_name : ident;
    pv_tv   : type_v;
    pv_ty   : ty;      (* as a logic type, for typing purposes only *)
    pv_vs   : vsymbol; (* for use in the logic *)
  }

  (* purify: turns program types into logic types *)

  let purify ty = try model_type ty with NotMutable -> ty

  let rec uncurry_type ?(logic=false) = function
    | Tpure ty when not logic ->
	[], ty
    | Tpure ty ->
	(* TODO: recursive descent? *)
	[], purify ty
    | Tarrow (bl, c) ->
	let tyl1 = 
	  List.map (fun v -> if logic then v.pv_vs.vs_ty else v.pv_ty) bl 
	in
	let tyl2, ty = uncurry_type ~logic c.c_result_type in
	tyl1 @ tyl2, ty (* TODO: improve efficiency? *)
	  
  let purify_type_v ?(logic=false) v =
    let tyl, ty = uncurry_type ~logic v in
    make_arrow_type tyl ty
      
  (* symbols *)

  type psymbol = {
    p_name : ident;
    p_tv   : type_v;
    p_ty   : ty;      (* program type, as a logic type *)
    p_ls   : lsymbol; (* for use in the logic *) 
  }

  let create_psymbol name v = 
    { p_name  = id_register name; 
      p_tv    = v;
      p_ty    = purify_type_v v;
      p_ls     = 
	let tyl, ty = uncurry_type ~logic:true v in
	create_lsymbol name tyl (Some ty); }
      
  let p_equal : psymbol -> psymbol -> bool = (==)

  let create_pvsymbol name ?vs v = 
    { pv_name = id_register name;
      pv_tv   = v;
      pv_ty   = purify_type_v v;
      pv_vs   = match vs with 
	| None -> create_vsymbol name (purify_type_v ~logic:true v)
	| Some vs -> vs; }

  let compare_pvsymbol v1 v2 =
    compare (id_hash v1.pv_name) (id_hash v2.pv_name)
      
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
	let (ef, s), bl = Util.map_fold_left (subst_binder ts) (ef, s) bl in
	Tarrow (bl, subst_type_c ef ts s c)
	  
  and subst_binder ts (ef, s) pv =
    let v' = subst_type_v ef ts s pv.pv_tv in
    let s, vs' = subst_var ts s pv.pv_vs in
    let pv' = create_pvsymbol (id_clone pv.pv_name) ~vs:vs' v' in
    let ef' = Mpv.add pv (R.Rlocal pv') ef in
    (ef', s), pv'

  let tpure ty = Tpure ty
    
  let tarrow bl c = match bl with
    | [] ->
	invalid_arg "tarrow"
    | _ ->
	let rename (e, s) v =
	  let tv' = subst_type_v e Mtv.empty s v.pv_tv in
	  let vs' = create_vsymbol (id_clone v.pv_vs.vs_name) v.pv_vs.vs_ty in
	  let v' = create_pvsymbol (id_clone v.pv_name) ~vs:vs' tv' in
	  let e' = Mpv.add v (R.Rlocal v') e in
	  let s' = Mvs.add v.pv_vs (t_var vs') s in
	  (e', s'), v'
	in
	let (e, s), bl' = Util.map_fold_left rename (Mpv.empty, Mvs.empty) bl in
	Tarrow (bl', subst_type_c e Mtv.empty s c)

  let v_result ty = create_vsymbol (id_fresh "result") ty

  let exn_v_result ls = match ls.ls_args with
    | [] -> None
    | [ty] -> Some (v_result ty)
    | _ -> assert false
	
  let post_map f ((v, q), ql) =
    (v, f q), List.map (fun (e,(v,q)) -> e, (v, f q)) ql
      
  let type_c_of_type_v = function
    | Tarrow ([], c) ->
	c
    | v ->
	let ty = purify_type_v v in
	{ c_result_type = v;
	  c_effect      = E.empty;
	  c_pre         = f_true;
	  c_post        = (v_result ty, f_true), []; }
	  
  let subst1 vs1 t2 = Mvs.add vs1 t2 Mvs.empty
    
  let apply_type_v_var v pv = match v with
    | Tarrow (x :: bl, c) ->
	let ts = ty_match Mtv.empty x.pv_ty pv.pv_ty in
	let c = type_c_of_type_v (Tarrow (bl, c)) in
	let ef = Mpv.add x (R.Rlocal pv) Mpv.empty in
	subst_type_c ef ts (subst1 x.pv_vs (t_var pv.pv_vs)) c
    | Tarrow ([], _) | Tpure _ ->
	assert false
	  
  let apply_type_v_sym v s = match v with
    | Tarrow (x :: bl, c) ->
	let ts = ty_match Mtv.empty x.pv_ty s.p_ty in
	let c = type_c_of_type_v (Tarrow (bl, c)) in
	let ef = Mpv.add x (R.Rglobal s) Mpv.empty in
	let t = t_app s.p_ls [] (ty_inst ts x.pv_vs.vs_ty) in
	subst_type_c ef ts (subst1 x.pv_vs t) c
    | _ ->
	assert false

  let apply_type_v_ref v = function
    | R.Rlocal pv -> apply_type_v_var v pv
    | R.Rglobal s -> apply_type_v_sym v s
	  
  let occur_formula r f = match r with
    | R.Rlocal  v -> f_occurs_single v.pv_vs f
    | R.Rglobal s -> f_s_any (fun _ -> false) (ls_equal s.p_ls) f
	
  let rec occur_type_v r = function
    | Tpure _ ->
	false
    | Tarrow (bl, c) ->
	occur_arrow r bl c
	  
  and occur_arrow r bl c = match bl with
    | [] ->
	occur_type_c r c
    | v :: bl ->
	occur_type_v r v.pv_tv ||
	  not (R.equal r (R.Rlocal v)) && occur_arrow r bl c
	  
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
    | Tarrow (bl1, c1), Tarrow (bl2, c2) ->
	assert (List.length bl1 = List.length bl2); (* FIXME? *)
	let s = 
	  List.fold_left2 (fun s v1 v2 -> Mpv.add v1 (R.Rlocal v2) s) 
	    Mpv.empty bl1 bl2
	in
	eq_type_c (subst_type_c s Mtv.empty Mvs.empty c1) c2
    | _ ->
	false

  and eq_type_c c1 c2 =
    eq_type_v c1.c_result_type c2.c_result_type &&
    E.equal   c1.c_effect      c2.c_effect

  (* pretty-printers *)

  open Pp
  open Format
  open Pretty
	  
  let print_pre fmt f =
    fprintf fmt "@[{ %a }@]" Pretty.print_fmla f

  and print_post fmt ((v,q), _) =
  fprintf fmt "@[{%a | %a}@]" Pretty.print_vs v Pretty.print_fmla q

  let print_post fmt ((v, q), el) =
    let print_exn_post fmt (l, (v, q)) =
      fprintf fmt "@[<hov 2>| %a %a->@ {%a}@]" 
	print_ls l (print_option print_vs) v print_fmla q
    in
    fprintf fmt "@[{%a | %a}@ %a@]" print_vs v print_fmla q 
      (print_list space print_exn_post) el
      
  let rec print_type_v fmt = function
    | Tpure ty ->
	print_ty fmt ty
    | Tarrow (bl, c) ->
	fprintf fmt "@[<hov 2>%a ->@ %a@]"
	  (print_list arrow print_binder) bl print_type_c c
	  
  and print_type_c fmt c =
    fprintf fmt "@[{%a}@ %a%a@ %a@]" print_fmla c.c_pre
      print_type_v c.c_result_type E.print c.c_effect
      print_post c.c_post
      
  and print_binder fmt x =
    fprintf fmt "(%a:%a)" print_vs x.pv_vs print_type_v x.pv_tv

end

and R : sig

  type t = 
    | Rlocal  of T.pvsymbol
    | Rglobal of T.psymbol

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val type_of : t -> ty

  val name_of : t -> ident

  val print : Format.formatter -> t -> unit

end = struct

  type t = 
    | Rlocal  of T.pvsymbol
    | Rglobal of T.psymbol

  let compare r1 r2 = match r1, r2 with
    | Rlocal v1,  Rlocal v2  -> 
	compare (id_hash v1.T.pv_name) (id_hash v2.T.pv_name)
    | Rglobal l1, Rglobal l2 -> 
	compare (id_hash l1.T.p_name) (id_hash l2.T.p_name)
    | Rlocal _,   Rglobal _  -> -1
    | Rglobal _,  Rlocal _   -> 1

  let equal r1 r2 = compare r1 r2 = 0

  let type_of = function
    | Rlocal v -> v.T.pv_vs.vs_ty
    | Rglobal { T.p_ls = { ls_value = Some ty } } -> ty
    | Rglobal { T.p_ls = { ls_value = None } }    -> assert false
	
  let name_of = function
    | Rlocal vs -> vs.T.pv_name
    | Rglobal ls -> ls.T.p_name
	
  (* let reference_of_term t = match t.t_node with *)
  (*   | Term.Tvar vs -> Rlocal vs *)
  (*   | Term.Tapp (ls, []) -> Rglobal ls *)
  (*   | _ -> assert false *)
	
  open Format

  let print fmt = function
    | Rlocal  v -> fprintf fmt "%a(l)" Pretty.print_vs v.T.pv_vs
    | Rglobal s -> fprintf fmt "%a(g)" Pretty.print_ls s.T.p_ls

end

and E : sig 

  type t = private {
    reads  : Sref.t;
    writes : Sref.t;
    raises : Sexn.t;
  }

  val empty : t

  val add_read  : R.t -> t -> t
  val add_write : R.t -> t -> t
  val add_raise : T.esymbol -> t -> t
    
  val remove_reference : R.t -> t -> t    
  val filter : (R.t -> bool) -> t -> t

  val remove_raise : T.esymbol -> t -> t

  val union : t -> t -> t

  val equal : t -> t -> bool
    
  val no_side_effect : t -> bool
    
  val subst : R.t Mpv.t -> t -> t

  val occur : R.t -> t -> bool

  val print : Format.formatter -> t -> unit

end = struct

  open T
  open R

  type t = {
    reads  : Sref.t;
    writes : Sref.t;
    raises : Sexn.t;
  }

  let empty = { reads = Sref.empty; writes = Sref.empty; raises = Sexn.empty }

  let add_read  r t = { t with reads  = Sref.add r t.reads  }
  let add_write r t = { t with writes = Sref.add r t.writes }
  let add_raise e t = { t with raises = Sexn.add e t.raises }
    
  let remove_reference r t =
    { t with reads = Sref.remove r t.reads; writes = Sref.remove r t.writes }

  let filter p t =
    { t with reads = Sref.filter p t.reads; writes = Sref.filter p t.writes }
      
  let remove_raise e t = { t with raises = Sexn.remove e t.raises }
    
  let union t1 t2 =
    { reads  = Sref.union t1.reads  t2.reads;
      writes = Sref.union t1.writes t2.writes;
      raises = Sexn.union t1.raises t2.raises; }
      
  let equal t1 t2 =
    Sref.equal t1.reads  t2.reads  &&
    Sref.equal t1.writes t2.writes &&
    Sexn.equal t1.raises t2.raises
      
  let no_side_effect t =
    Sref.is_empty t.writes && Sls.is_empty t.raises
      
  let subst m t =
    let add1 r' s = match r' with
      | Rlocal vs' -> Sref.add (try Mpv.find vs' m with Not_found -> r') s
      | _ -> Sref.add r' s
    in
    let apply s = Sref.fold add1 s Sref.empty in
    { reads = apply t.reads; writes = apply t.writes; raises = t.raises }
      
  let occur r t =
    Sref.mem r t.reads || Sref.mem r t.writes
      
  open Format
  open Pp
  open Pretty
      
  let print_rset fmt s = print_list comma R.print  fmt (Sref.elements s)
  let print_eset fmt s = print_list comma print_ls fmt (Sexn.elements s)

  let print fmt e =
    if not (Sref.is_empty e.reads) then
      fprintf fmt "@ reads %a" print_rset e.reads;
    if not (Sref.is_empty e.writes) then
      fprintf fmt "@ writes %a" print_rset e.writes;
    if not (Sexn.is_empty e.raises) then
      fprintf fmt "@ raises %a" print_eset e.raises

end 

and Spv : sig include Set.S with type elt = T.pvsymbol end = 
  Set.Make(struct type t = T.pvsymbol let compare = T.compare_pvsymbol end)

and Mpv : sig include Map.S with type key = T.pvsymbol end = 
  Map.Make(struct type t = T.pvsymbol let compare = T.compare_pvsymbol end)

and Sref : sig include Set.S with type elt = R.t end = Set.Make(R)

and Mref : sig include Map.S with type key = R.t end = Map.Make(R)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
