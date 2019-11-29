(** Several useful utilities to preprocess logic terms before analysing them
 * for AI *)

open Term
open Apron

module Make(S: sig
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct

  let env = S.env

  let known_logical_ident = Pmodule.(Theory.(S.pmod.mod_theory.th_known))
  let known_pdecl = Pmodule.(Theory.(S.pmod.mod_known))

  let th_int = Env.read_theory env ["int"] "Int"
  let le_int = Theory.(ns_find_ls th_int.th_export ["infix <="])
  let ge_int = Theory.(ns_find_ls th_int.th_export ["infix >="])
  let lt_int = Theory.(ns_find_ls th_int.th_export ["infix <"])
  let gt_int = Theory.(ns_find_ls th_int.th_export ["infix >"])
  let ad_int = Theory.(ns_find_ls th_int.th_export ["infix +"])
  let min_int = Theory.(ns_find_ls th_int.th_export ["infix -"])
  let min_u_int = Theory.(ns_find_ls th_int.th_export ["prefix -"])
  let mult_int = Theory.(ns_find_ls th_int.th_export ["infix *"])
  let zero_int = Term.t_nat_const 0
  let one_int = Term.t_nat_const 1
  let int_add =  begin fun a ->
    match a with
    | [a; b] ->
      if t_equal a zero_int then b
      else if t_equal b zero_int then a
      else fs_app Theory.(ns_find_ls th_int.th_export ["infix +"]) [a; b] Ty.ty_int
    | _ -> assert false
  end
  let int_minus_u = fun a -> fs_app Theory.(ns_find_ls th_int.th_export ["prefix -"]) a Ty.ty_int
  let int_minus = begin fun a ->
    match a with
    | [a; b] ->
      if t_equal a zero_int then int_minus_u [b]
      else if t_equal b zero_int then a
      else fs_app Theory.(ns_find_ls th_int.th_export ["infix -"]) [a; b] Ty.ty_int
    | _ -> assert false
  end
  let int_mult = fun a -> fs_app Theory.(ns_find_ls th_int.th_export ["infix *"]) a Ty.ty_int


  exception Cannot_be_expressed

  type coeff =
    | CNone
    | CPos of Term.term
    | CMinus of Term.term
    | CMinusOne
    | COne

  let coeff_to_term = function
    | Coeff.Scalar(s) ->
      let i = int_of_string (Scalar.to_string s) in
      let n = Constant.int_const_of_int (abs i) in

      if i = 1 then
        COne
      else if i = -1 then
        CMinusOne
      else if i > 0 then
        CPos (t_const n Ty.ty_int)
      else if i < 0 then
        CMinus (t_const n Ty.ty_int)
      else
        CNone
    | Coeff.Interval(_) -> raise Cannot_be_expressed

  let varlist_to_term variable_mapping (l, cst) =
    let open Ty in
    let term = ref zero_int in
    List.iter (fun (c, v) ->
        match coeff_to_term c with
        | CPos c ->
          let v = variable_mapping v in
          term := int_add [!term; int_mult [c; v]];
        | COne ->
          let v = variable_mapping v in
          term := int_add [!term; v];
        | CMinusOne ->
          let v = variable_mapping v in
          term := int_minus [!term; v];
        | CMinus c ->
          let v = variable_mapping v in
          term := int_minus [!term; int_mult [c; v]];
        | CNone -> ()
      ) l;
    let c = coeff_to_term cst in
    let term = match c with
      | CNone -> !term
      | CPos c ->
        int_add [c; !term]
      | CMinus c ->
        int_minus [!term;c]
      | COne ->
        int_add [one_int; !term]
      | CMinusOne ->
        int_minus [!term; one_int]
    in
    term

  (** Descend nots in the tree *)
  (* if way is true, then we must return the negation of t *)
  let rec t_descend_nots ?way:(way=false) t =
    match t.t_node with
    | Tbinop(Tand, t1, t2) ->
      if way then
        t_or_simp (t_descend_nots ~way t1) (t_descend_nots ~way t2)
      else
        t_and_simp (t_descend_nots ~way t1) (t_descend_nots ~way t2)
    | Tbinop(Tor, t1, t2) ->
      if way then
        t_and_simp (t_descend_nots ~way t1) (t_descend_nots ~way t2)
      else
        t_or_simp (t_descend_nots ~way t1) (t_descend_nots ~way t2)
    | Tbinop(Timplies, t1, t2) ->
      t_descend_nots ~way (t_or (t_not t1) t2)
    | Tnot(t) ->
      t_descend_nots ~way:(not way) t
    | Tapp(l, args) when ls_equal l lt_int && way ->
      t_app ge_int args None
    | Tapp(l, args) when ls_equal l gt_int && way ->
      t_app le_int args None
    | Tapp(l, args) when ls_equal l le_int && way ->
      t_app gt_int args None
    | Tapp(l, args) when ls_equal l ge_int && way ->
      t_app lt_int args None
    | Tapp(l, args) when ls_equal l ps_equ && way && Ty.ty_equal (t_type (List.hd args)) Ty.ty_int ->
      t_or (t_app lt_int args None) (t_app gt_int args None)
    | Tapp(l, [a;b]) when ls_equal l ps_equ && way && t_equal t_bool_true a ->
      t_app ps_equ [b;t_bool_false] None
    | Tapp(l, [b;a]) when ls_equal l ps_equ && way && t_equal t_bool_true a ->
      t_app ps_equ [b;t_bool_false] None
    | Tapp(l, [a;b]) when ls_equal l ps_equ && way && t_equal t_bool_false a ->
      t_app ps_equ [b;t_bool_true] None
    | Tapp(l, [b;a]) when ls_equal l ps_equ && way && t_equal t_bool_false a ->
      t_app ps_equ [b;t_bool_true] None
    | _ ->
      if way then
        t_not t
      else t


  (** Find definitions *)

  type env = {
    known : Decl.known_map;
    funenv : Decl.logic_decl Term.Mls.t;
  }

  exception Recursive_logical_definition

  let find_global_definition kn rs =
    let open Term in
    match (Ident.Mid.find rs.ls_name kn).Decl.d_node with
    | Decl.Dlogic(decls) ->
      if List.length decls <> 1 then
        raise Recursive_logical_definition;
      Some (List.hd decls)
    | Decl.Dparam(_) -> None
    | _ -> None

  let find_definition env rs =
    let open Term in
    try
      (* then try if it is a local function *)
      let f = Mls.find rs env.funenv in
      Some f
    with Not_found ->
    (* else look for a global function *)
    try
      find_global_definition env.known rs
    with
    | Not_found ->
      Format.eprintf "Couldn't find definition of: ";
      Pretty.print_ls Format.err_formatter rs;
      Format.eprintf "@.";
      raise Not_found

  (** Inline every symbol *)

  let t_unfold loc fs tl ty =
    let open Ty in
    if Term.ls_equal fs Term.ps_equ then
      t_app fs tl ty
    else
      match find_definition { known = known_logical_ident; funenv = Mls.empty; } fs with
      | None ->
        t_app fs tl ty
      | Some (vl,e) ->
        assert (Term.ls_equal vl fs);
        try
          let vsym, new_term = Decl.open_ls_defn e in
          let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
          let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vsym tl in
          let mt = oty_match mt (Some (t_type new_term)) ty in
          t_ty_subst mt mv new_term
        with
        | Term.TermExpected(_) -> t_app fs tl ty

  let rec t_replace_all t =
    let t = t_map t_replace_all t in
    match t.t_node with
    | Tapp (fs,tl) ->
      t_attr_copy t (t_unfold t.t_loc fs tl t.t_ty)
    | _ -> t
end

let rec extract_atom_from_conjuction l t =
  match t.t_node with
  | Tbinop(Tand, a, b) ->
    extract_atom_from_conjuction
      (extract_atom_from_conjuction l a) b
  | _ -> t::l

let is_in t myt =
  let found = ref false in
  let rec is_in myt =
    if t_equal t myt then
      found := true;
    t_map is_in myt
  in
  is_in myt |> ignore;
  !found

let rec descend_quantifier q t =
  match t.t_node with
  | Tbinop(Tand, a, b) ->
    let ia = is_in q a
    and ib = is_in q b in
    if ia && ib then
      let var = match q.t_node with
        | Tvar(v) -> v
        | _ -> assert false
      in
      t_quant Tforall (t_close_quant [var] [] t)
    else if ia && not ib then
      t_and_simp (descend_quantifier q a) b
    else if not ia && ib then
      t_and_simp a (descend_quantifier q b)
    else
      t_and_simp a b
  | _ ->
      let var = match q.t_node with
        | Tvar(v) -> v
        | _ -> assert false
      in
      t_quant Tforall (t_close_quant [var] [] t)
