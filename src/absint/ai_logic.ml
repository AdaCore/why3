(** Several useful utilities to preprocess logic terms before analysing them
 * for AI *)

open Term

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
      t_label_copy t (t_unfold t.t_loc fs tl t.t_ty)
    | _ -> t
end
