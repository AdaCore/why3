open Apron
open Term
open Decl

module type INFERWHY3 = sig

  val env       : Env.env
  val th_known  : known_map
  val mod_known : Pdecl.known_map

  val le_int : lsymbol
  val ge_int : lsymbol
  val lt_int : lsymbol
  val gt_int : lsymbol

  val ad_int      : lsymbol
  val min_int     : lsymbol
  val min_u_int   : lsymbol
  val mult_int    : lsymbol
  val zero_int    : term
  val one_int     : term
  val int_add     : term list -> term
  val int_minus_u : term list -> term
  val int_minus   : term list -> term
  val int_mult    : term list -> term

  val varlist_to_term :
    ('a -> term) -> (Coeff.union_5 * 'a) list * Coeff.union_5 -> term

  val t_push_negation : term -> term

  val t_inline_all : term -> term
end

module Make(S: sig
    val       env : Env.env
    val  th_known : Decl.known_map
    val mod_known : Pdecl.known_map
  end) = struct

  open Term
  open Theory

  let env       = S.env
  let th_known  = S.th_known
  let mod_known = S.mod_known

  let th_int = Env.read_theory env ["int"] "Int"
  let le_int = ns_find_ls th_int.th_export ["infix <="]
  let ge_int = ns_find_ls th_int.th_export ["infix >="]
  let lt_int = ns_find_ls th_int.th_export ["infix <"]
  let gt_int = ns_find_ls th_int.th_export ["infix >"]
  let ad_int = ns_find_ls th_int.th_export ["infix +"]
  let min_int = ns_find_ls th_int.th_export ["infix -"]
  let min_u_int = ns_find_ls th_int.th_export ["prefix -"]
  let mult_int = ns_find_ls th_int.th_export ["infix *"]
  let zero_int = t_nat_const 0
  let one_int = t_nat_const 1
  let int_add = function
    | [t1; t2] when t_equal t1 zero_int -> t2
    | [t1; t2] when t_equal t2 zero_int -> t1
    | [t1; t2] ->
       fs_app (ns_find_ls th_int.th_export ["infix +"]) [t1; t2] Ty.ty_int
    | _ -> assert false
  let int_minus_u a = fs_app (ns_find_ls th_int.th_export ["prefix -"]) a Ty.ty_int
  let int_minus = function
    | [t1; t2] when t_equal t1 zero_int -> int_minus_u [t2]
    | [t1; t2] when t_equal t2 zero_int -> t1
    | [t1; t2] ->
       fs_app (ns_find_ls th_int.th_export ["infix -"]) [t1; t2] Ty.ty_int
    | _ -> assert false
  let int_mult a = fs_app (ns_find_ls th_int.th_export ["infix *"]) a Ty.ty_int

  exception Cannot_be_expressed

  type coeff =
    | CNone
    | CPos of term
    | CMinus of term
    | CMinusOne
    | COne

  (* Apron.Coeff.t -> coeff *)
  let acoeff2coeff = function
    | Coeff.Scalar s ->
       let i = int_of_string (Scalar.to_string s) in
       let n = Constant.int_const_of_int (abs i) in
       if i = 1 then COne
       else if i = -1 then CMinusOne
       else if i > 0 then CPos (t_const n Ty.ty_int)
       else if i < 0 then CMinus (t_const n Ty.ty_int)
       else CNone
    | Coeff.Interval _ -> raise Cannot_be_expressed

  let varlist_to_term var2term (acoeff_varl, acoeff) =
    let term = List.fold_left (fun t (coeff, var) ->
        match acoeff2coeff coeff with
        | COne -> int_add [t; var2term var];
        | CMinusOne -> int_minus [t; var2term var];
        | CPos c -> int_add [t; int_mult [c; var2term var]];
        | CMinus c -> int_minus [t; int_mult [c; var2term var]];
        | CNone -> t
      ) zero_int acoeff_varl in
    match acoeff2coeff acoeff with
      | CNone     -> term
      | CPos c    -> int_add [c; term]
      | CMinus c  -> int_minus [term;c]
      | COne      -> int_add [one_int; term]
      | CMinusOne -> int_minus [term; one_int]

  (** push negations deeper in the term tree *)
  (* if way is true, then we must return the negation of t *)
  let rec t_push_negation ?way:(way=false) t =
    let is_int t = Ty.ty_equal (t_type t) Ty.ty_int in
    match t.t_node with
    | Tbinop (Tand, t1, t2) ->
      if way then
        t_or_simp (t_push_negation ~way t1) (t_push_negation ~way t2)
      else
        t_and_simp (t_push_negation ~way t1) (t_push_negation ~way t2)
    | Tbinop (Tor, t1, t2) ->
      if way then
        t_and_simp (t_push_negation ~way t1) (t_push_negation ~way t2)
      else
        t_or_simp (t_push_negation ~way t1) (t_push_negation ~way t2)
    | Tbinop (Timplies, t1, t2) ->
      t_push_negation ~way (t_or (t_not t1) t2)
    | Tbinop (Tiff, t1, t2) ->
      t_push_negation ~way (t_and (t_implies t1 t2) (t_implies t2 t1))
    | Tnot t -> t_push_negation ~way:(not way) t
    | Tapp (l, args) when ls_equal l lt_int && way ->
       t_app ge_int args None
    | Tapp (l, args) when ls_equal l gt_int && way ->
       t_app le_int args None
    | Tapp (l, args) when ls_equal l le_int && way ->
       t_app gt_int args None
    | Tapp (l, args) when ls_equal l ge_int && way ->
       t_app lt_int args None
    | Tapp (l, args) when ls_equal l ps_equ && way && is_int (List.hd args) ->
      t_or (t_app lt_int args None) (t_app gt_int args None)
    | Tapp (l, [a;b]) when ls_equal l ps_equ && way && t_equal t_bool_true a ->
      t_app ps_equ [b;t_bool_false] None
    | Tapp (l, [b;a]) when ls_equal l ps_equ && way && t_equal t_bool_true a ->
      t_app ps_equ [b;t_bool_false] None
    | Tapp (l, [a;b]) when ls_equal l ps_equ && way && t_equal t_bool_false a ->
      t_app ps_equ [b;t_bool_true] None
    | Tapp (l, [b;a]) when ls_equal l ps_equ && way && t_equal t_bool_false a ->
      t_app ps_equ [b;t_bool_true] None
    | _ -> if way then t_not t else t

  let t_push_negation = t_push_negation ~way:false

  (** Find definitions *)

  open Decl

  type env = {
    known  : known_map;
    funenv : logic_decl Mls.t;
  }

  exception Recursive_logical_definition

  let find_global_definition kn ls =
    match (Ident.Mid.find ls.ls_name kn).d_node with
    | Dlogic [d] -> Some d
    | Dlogic _   -> raise Recursive_logical_definition
    | Dparam _   -> None
    | _          -> None

  let find_definition env ls =
    try Some (Mls.find ls env.funenv) with Not_found ->
      try find_global_definition env.known ls with | Not_found ->
        Format.eprintf "Couldn't find definition of: %a@."
          Pretty.print_ls ls;
        raise Not_found

  (** Inline every symbol *)
  let t_unfold _ fs tl ty =
    let open Ty in
    if ls_equal fs ps_equ then t_app fs tl ty else
      match find_definition { known = th_known; funenv = Mls.empty; } fs with
      | None ->
        t_app fs tl ty
      | Some (vl,e) ->
        assert (ls_equal vl fs);
        try
          let vsym, new_term = open_ls_defn e in
          let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
          let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vsym tl in
          let mt = oty_match mt (Some (t_type new_term)) ty in
          t_ty_subst mt mv new_term
        with
        | TermExpected _ -> t_app fs tl ty

  let rec t_inline_all t =
    let t = t_map t_inline_all t in
    match t.t_node with
    | Tapp (fs,tl) ->
      t_attr_copy t (t_unfold t.t_loc fs tl t.t_ty)
    | _ -> t
end
