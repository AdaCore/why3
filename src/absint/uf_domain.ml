open Domain
open Apron
open Term

module Make(S:sig
    module A:DOMAIN
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct
  module A = S.A
  module D = A
  
  module Ai_logic = Ai_logic.Make(struct
      let env = S.env
      let pmod = S.pmod
    end)
  open Ai_logic

  type domain = A.t

  exception Not_handled of Term.term

  (* utility function that make equivalent classes and sum the last component *)
  let sum_list a =
    let a = List.sort (fun (i, _) (j, _) ->
        compare i j) a in
    let rec merge = function
      | [] -> []
      | [b] -> [b]
      | (a, b)::(c, d)::q ->
        if a = c then
          merge ((a, b + d)::q)
        else
          (a, b) :: (merge ((c, d)::q))
    in
    merge a


  type uf_man = {
    variable_mapping: (Apron.Var.t, Term.term) Hashtbl.t;
    mutable apron_mapping: Var.t Term.Mterm.t;
    mutable region_mapping: (Ity.pvsymbol * Term.term) list Ity.Mreg.t;
    mutable env: Environment.t;

    (* UF_QF *)
    mutable defined_terms: unit Term.Mterm.t; 
    mutable term_mapping: Union_find.t Term.Mterm.t;
    class_mapping: (Union_find.t, Term.term) Hashtbl.t;
    mutable term_depend: unit Term.Mterm.t Term.Mterm.t;
    mutable every_term: Union_find.set;
    classes_var_mapping: (Union_find.t, Apron.Var.t option) Hashtbl.t;
  }

  type uf_t = { classes: Union_find.set;
                known_terms: unit Term.Mterm.t; 
              }


  type man = A.man * uf_man
  type env = unit
  type t = A.t * uf_t

  let create_manager () =
    A.create_manager (), { variable_mapping = Hashtbl.create 512;
                           apron_mapping = Term.Mterm.empty;
                           region_mapping = Ity.Mreg.empty;
                           env = Environment.make [||] [||];
                           term_mapping = Term.Mterm.empty;
                           class_mapping = Hashtbl.create 512;
                           term_depend = Term.Mterm.empty;
                           defined_terms = Term.Mterm.empty;
                           classes_var_mapping = Hashtbl.create 512;
                           every_term = Union_find.empty;
                         }

  let empty_uf_domain = { classes = Union_find.empty; known_terms = Term.Mterm.empty; }

  let bottom (man, uf_man) env =
    A.bottom man uf_man.env, empty_uf_domain

  let top (man, uf_man) env =
    A.top man uf_man.env, empty_uf_domain

  let canonicalize (man, _) (a, b) =
    A.canonicalize man a

  let is_bottom (man, _) (a, b) =
    A.is_bottom man a

  let is_leq (man, _) (a, b) (c, d) =
    A.is_leq man a c && Union_find.is_leq b.classes d.classes

  let join_uf uf_man a b =
    { classes = Union_find.join a.classes b.classes; known_terms = Term.Mterm.union (fun _ _ _ -> Some ()) a.known_terms b.known_terms }


  let join (man, uf_man) (a, b) (c, d) =
    A.join man a c, join_uf uf_man b d

  let join_list man l = match l with
    | [] -> assert false
    | t::q -> List.fold_left (join man) t q

  let widening (man, uf_man) (a, b) (c, d) =
    A.widening man a c, join_uf uf_man b d

  let print fmt (a, b) = A.print fmt a

  let to_term env pmod (man, _) (a, b) v =
    A.to_term env pmod man a v

  let push_label (man, uf_man) env i (a, b) =
    A.push_label man uf_man.env i a, b
  
  let warning_t s t =
    Format.eprintf "-- warning: %s -- triggered by " s;
    Pretty.print_term Format.err_formatter t;
    Format.eprintf " of type ";
    Pretty.print_ty Format.err_formatter (Term.t_type t);
    Format.eprintf "@."

  let ident_ret = Ident.{pre_name = "$pat"; pre_label = Ident.Slab.empty; pre_loc = None; }
  let access_field constr constr_args a i (proj, t) =
      match a.t_node with
      | Tapp(func, args) when func.ls_constr = 1 ->
        List.nth args i
      | Tvar(_) | _ ->
        match proj with
        | None ->
          let return = create_vsymbol ident_ret t in
          let pat = List.mapi (fun k t ->
              if k = i then
                pat_var return
              else
                pat_wild t
            ) constr_args in
          t_case a [t_close_branch (pat_app constr pat (t_type a)) (t_var return)]
        | Some s ->
          t_app s [a] (Some t)

  
  let get_subvalues a ity =
    let open Ty in
    let myty = t_type a in
    let rec aux ity =
      match myty.ty_node with
      | _ when ty_equal myty ty_bool ->
        []
      | _ when ty_equal myty ty_int ->
        [a, None]
      | Tyapp(tys, vars) -> 
        begin
          let vars = Ty.ts_match_args tys vars in
          match (Ident.Mid.find tys.ts_name known_logical_ident).Decl.d_node with
          | Decl.Ddata([_, [ls, ls_projs]]) ->
            let l =
              let my_ls_args = List.map (fun i -> Ty.ty_inst vars i) ls.ls_args in
              List.combine my_ls_args ls_projs
              |> List.map (fun (arg_type, proj) ->
                  match proj with
                  | Some s ->  Some s,
                               (match s.ls_value with
                                | Some t ->
                                  let l = Ty.ty_inst vars t in
                                  assert (Ty.ty_equal l arg_type);
                                  l
                                | None -> assert false)
                  | None -> None, arg_type)
              |> List.mapi (access_field ls my_ls_args a)
            in
            begin
              match ity with
              | None -> List.map (fun a -> a, None) l
              | Some its ->
                let pdecl = Pdecl.((find_its_defn known_pdecl its).itd_fields) in
                List.map (fun a -> Some a) pdecl
                |> List.combine l
            end
          | Decl.Dtype({ts_def = Some _; ts_args = _; _ }) ->
            (* untested code*)
            let () = assert false in
            aux ity
          | Decl.Ddata([_; _]) ->
            warning_t "Multiple constructors is not supported in abstract interpretation." a; []
          | Decl.Ddata(_) ->
            warning_t "Recursive types is not supported in abstract interpretation." a; []
          | Decl.Dtype(_) -> (* This happens when a type is private or has an invariant: it can't be accesed
                              * by the logic, so we give up and only look for projections by looking
                              * at program projections. *)
            begin
              try
                let its = Ity.restore_its tys in
                (match ity with
                 | None -> ()
                 | Some s -> assert (Ity.its_equal its s));
                let pdecl = Pdecl.((find_its_defn known_pdecl its).itd_fields) in
                List.map (fun b ->
                    let l = match Expr.(b.rs_logic) with | Expr.RLls(l) -> l | _ -> assert false in
                    let this_ty = Expr.(Ity.(ty_of_ity b.rs_cty.cty_result)) in
                    let ty = Ty.ty_inst vars this_ty in
                    t_app l [a] (Some ty), if ity = None then None else Some b) pdecl
              with
              | Not_found -> failwith "could not restore its"
            end
          | Decl.Dind(_) ->
            warning_t "Could not find type declaration (got inductive predicate)."
              a;
            []
          | Decl.Dlogic(_) ->
            warning_t "Could not find type declaration (got logic declaration)."
              a;
            []
          | Decl.Dprop(_) ->
            warning_t "Could not find type declaration (got propsition) for: "
              a;
            []
          | Decl.Dparam(_) ->
            warning_t "Could not find type declaration (got param)."
              a;
            []
        end
      | Tyvar(_) ->
        warning_t "Comparison of values with an abstract type, the interpretation will not be precise" a;
        []
    in
    aux ity

  let get_td uf_man a =
    try
      let c = Mterm.find a uf_man.term_depend in
      Format.eprintf "depend found@.";
      c
    with
    | Not_found ->
      Format.eprintf "depend for term not found:";
      Pretty.print_term Format.err_formatter a;
      Format.eprintf "@.";
      Mterm.empty

  let rec get_depend s t =
    match t.t_node with
    | Tvar(_) ->
      if t_equal s t then
        Mterm.empty
      else Mterm.add t () Mterm.empty
    | Tapp(_, args) ->
      List.map (get_depend s) args
      |> List.fold_left (Mterm.union (fun _ _ _ -> Some ())) Mterm.empty
    | _ -> Mterm.empty

  let create_class_var =
    let uf_var = ref 0 in
    fun uf_man t ->
    uf_man.defined_terms <- Mterm.add t () uf_man.defined_terms;
    let c = Union_find.new_class () in
    uf_man.term_mapping <- Mterm.add t c uf_man.term_mapping;
    Hashtbl.add uf_man.class_mapping c t;
    let deps = get_depend t t in
    uf_man.term_depend <- Mterm.fold_left (fun td k () ->
        let a =
          try
            Mterm.find k td
          with
          | Not_found -> Mterm.empty
        in
        let a = Mterm.add t () a in
        Mterm.add k a td) uf_man.term_depend deps;
    let myvar = try
        if Ty.ty_equal (t_type t) Ty.ty_int then
        Some (Mterm.find t uf_man.apron_mapping)
        else None
      with 
      | Not_found ->
        incr uf_var;
        let v = Var.of_string (Format.sprintf "$uf%d" !uf_var) in
        uf_man.env <- Environment.add uf_man.env [|v|] [||];
        uf_man.apron_mapping <- Mterm.add t v uf_man.apron_mapping;
        Hashtbl.add uf_man.variable_mapping v t;
        Some v
    in
    Hashtbl.add uf_man.classes_var_mapping c myvar;
    c, myvar

  let get_class_for_term uf_man t =
    try
      Mterm.find t uf_man.term_mapping
    with
    | Not_found ->
      let c, _ = create_class_var uf_man t in
      c
  
  let get_class_for_term_ro uf_man t =
    try
      Mterm.find t uf_man.term_mapping
    with
    | Not_found ->
      assert false


  (** Get a set of (apron) linear expressions from a constraint stated in why3 logic.
   *
   * The resulting list of linear expressions is weaker than the original why3
   * formula.
   * In the most imprecise case, it returns an empty list.
   **)
  let meet_term: man -> Term.term -> (t -> t) = fun (man, uf_man) t ->
    let open Term in

    (* First inline everything, for instance needed for references
     * where !i is (!) i and must be replaced by (contents i) *)
    let t = t_replace_all t in

    (* Let's try to remove the nots that we can *)
    let t = t_descend_nots t in

    let var_of_term t =
      try
        Some (Term.Mterm.find t uf_man.apron_mapping)
      with
      | Not_found -> None
    in

    (* Assuming that t is an arithmetic term, this computes the number of ocurrence of variables
     * ando the constant of the arithmetic expression.
     * It returns (variables, constant)
     *
     * For instance, 4 + x + y set cst to 4, and constr to [(x, 1), (y, 1)]
     * *)
    let rec term_to_var_list f coeff t =
      let re = term_to_var_list f in
      match t.t_node with
      | Tvar(_) ->
        begin
        match var_of_term t with
        | Some var -> ([(var, coeff)], 0)
        | None -> Format.eprintf "Variable undefined: "; Pretty.print_term Format.err_formatter t; Format.eprintf "@."; failwith "undefined var"
        end
      | Tconst(Number.ConstInt(n)) ->
        let n = Number.compute_int n in
        ([], coeff * (BigInt.to_int n))
      | Tapp(func, args) when Term.ls_equal func ad_int ->
        List.fold_left (fun (a, b) c ->
            let c, d = re coeff c in
            (a @ c, b + d)) ([], 0)args
      | Tapp(func, [a;b]) when Term.ls_equal func min_int ->
        let c, d = re coeff a in
        let e, f = re (-coeff) b in
        (c @ e, d + f)
      | Tapp(func, [a]) when Term.ls_equal func min_u_int ->
        re (-coeff)  a;
      | Tapp(func, [{t_node = Tconst(Number.ConstInt(n)); _}; a])
      | Tapp(func, [a; {t_node = Tconst(Number.ConstInt(n)); _};]) when Term.ls_equal func mult_int ->
        let n = Number.compute_int n in
        re ((BigInt.to_int n) * coeff) a
      (* FIXME: need a nice domain for algebraic types *)
      | _ -> (* maybe a record access *)
        begin
          match var_of_term t with
          | None ->
            Format.eprintf "Could not find term";
            Pretty.print_term Format.err_formatter t;
            Format.eprintf ", switch it to uninterpreted function.@.";
            let _, Some myvar = create_class_var uf_man t in
            ([myvar, coeff], 0)
          | Some s ->
            ([s, coeff], 0)
        end
    in
    
    (* This takes an epsilon-free formula and returns a list of linear expressions weaker than
     * the original formula. *)
    let rec aux t =
      Pretty.print_term Format.err_formatter t;
      try
        match t.t_node with
        | Tbinop(Tand, a, b) ->
          let fa = aux a in
          let fb = aux b in
          (fun d ->
             fb (fa d))
        | Tbinop(Tor, a, b) ->
          let fa = aux a in
          let fb = aux b in
          (fun (d, a) ->
             let (d1, a1) = fa (d, a) in
             let (d2, a2) = fb (d, a) in
             D.join man d1 d2, join_uf man a1 a2)

        | Tapp(func, [a; b]) when (Ty.ty_equal (t_type a) Ty.ty_int (* || Ty.ty_equal (t_type a) Ty.ty_bool*))
          && 
          (ls_equal ps_equ func ||
           ls_equal lt_int func ||
           ls_equal gt_int func ||
           ls_equal le_int func ||
           ls_equal ge_int func)

          ->

          (* FIXME: >, <=, >=, booleans *)
            let base_coeff, eq_type =
              if ls_equal ps_equ func then
                1, Lincons1.EQ
              else if ls_equal lt_int func then
                1, Lincons1.SUP
              else if ls_equal gt_int func then
                -1, Lincons1.SUP
              else if ls_equal le_int func then
                1, Lincons1.SUPEQ
              else if ls_equal ge_int func then
                -1, Lincons1.SUPEQ
              else
                assert false
            in
            let f = ref (fun d -> d) in
            let va, ca = term_to_var_list f (-base_coeff) a in
            let vb, cb = term_to_var_list f base_coeff b in
            let c = ca + cb in
            let v = sum_list (va @ vb) in
            let expr = Linexpr1.make uf_man.env in
            let constr = List.map (fun (var, coeff) ->
                Coeff.Scalar (Scalar.of_int coeff), var) v in
            Linexpr1.set_list expr constr None;
            let cons = Lincons1.make expr eq_type in
            Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int c));
            let arr = Lincons1.array_make uf_man.env 1 in
            Lincons1.array_set arr 0 cons;
            let f = !f in
            let f = 
              if ls_equal ps_equ func then
                let ca = get_class_for_term uf_man a in
                let cb = get_class_for_term uf_man b in
                uf_man.every_term <- Union_find.union ca cb uf_man.every_term;
                (fun uf_d ->
                   let tda = Mterm.find a uf_man.term_depend in
                   let tdb = Mterm.find b uf_man.term_depend in
                   assert (Mterm.cardinal tda = Mterm.cardinal tdb);
                   let replaceby a b t =
                     t_map (fun t ->
                         if t_equal t a then b else t) t
                   in
                   let l = Mterm.fold_left (fun l k _ ->
                       ((replaceby a b) k, k) :: l) [] tda in
                   let l = List.map (fun (a, b) ->
                       get_class_for_term_ro uf_man a, get_class_for_term_ro uf_man b) l in
                   let l = (ca, cb) :: l in
                   f uf_d |>
                   fun c -> { c with classes = List.fold_left (fun c (ca, cb) ->
                       Union_find.union ca cb c) c.classes l } )
              else
                f
            in
            let f =
              if Ty.ty_equal (t_type a) Ty.ty_int then f
              else fun x -> x
            in

            (fun (d, a) ->
               D.meet_lincons_array man d arr, f a)
        | Tapp(func, [a;b]) when ls_equal ps_equ func ->
          let subv_a = get_subvalues a None in
          let subv_b = get_subvalues b None in
          List.combine subv_a subv_b 
          |> List.fold_left (fun f ((a, _), (b, _)) ->
              let g = aux (t_app ps_equ [a; b] None) in
              (fun abs ->
                 g abs |> f)) (fun x -> x)
        | Tif(a, b, c) ->
          let fa = aux a in
          let fa_not = aux (t_descend_nots a) in
          let fb = aux b in
          let fc = aux c in
          (fun d ->
             let (d1, a1) = fb (fa d) in
             let (d2, a2) = fc (fa_not d) in
             D.join man d1 d2, join_uf man a1 a2)
        | Ttrue -> (fun d -> d)
        | _ when t_equal t t_bool_true || t_equal t t_true -> (fun d -> d)
        | Tfalse -> (fun _ -> D.bottom man uf_man.env, empty_uf_domain)
        | _ when t_equal t t_bool_false || t_equal t t_false -> (fun _ -> D.bottom man uf_man.env, empty_uf_domain)
        | _ ->
          raise (Not_handled t)
      with
      | Not_handled(t) ->
        Format.eprintf "Couldn't understand entirely the post condition: ";
        Pretty.print_term Format.err_formatter t;
        Format.eprintf "@.";
        (fun d -> d)
    in
    try
      aux t
    with
    | e ->
      Format.eprintf "error while computing domain for post conditions: ";
      Pretty.print_term Format.err_formatter t;
      Format.eprintf "@.";
      raise e

  let var_id = ref 0

  let ensure_variable uf_man v t =
    if not (Environment.mem_var uf_man.env v) then
      begin
        Hashtbl.add uf_man.variable_mapping v t;
        uf_man.env <- Environment.add uf_man.env [|v|] [||]
      end
  
  let add_lvariable_to_env (man, uf_man) vsym =
    incr var_id;
    let open Expr in
    let open Ity in
    let open Ty in
    let logical_term = t_var vsym in
    try
      let _ = Mterm.find logical_term uf_man.defined_terms in
      ()
    with
    | Not_found ->
      uf_man.defined_terms <- Mterm.add logical_term () uf_man.defined_terms;
      ignore (Format.flush_str_formatter ());
      if Ty.ty_equal (t_type logical_term) ty_int then
        begin
          Format.eprintf " added@.";
          let reg_name = Pretty.print_term Format.str_formatter logical_term
                         |> Format.flush_str_formatter
                         |> Format.sprintf "%d%s" !var_id in
          let v =
            Var.of_string reg_name in
          assert (not (Environment.mem_var uf_man.env v));
          ensure_variable uf_man v logical_term;
          uf_man.apron_mapping <- Term.Mterm.add logical_term v uf_man.apron_mapping
        end
      else if Ty.ty_equal (t_type logical_term) ty_bool then
        begin
          let reg_name = Pretty.print_term Format.str_formatter logical_term
                         |> Format.flush_str_formatter
                         |> Format.sprintf "%d%s" !var_id in
          let v =
            Var.of_string reg_name in
          assert (not (Environment.mem_var uf_man.env v));
          ensure_variable uf_man v logical_term;
          uf_man.apron_mapping <- Term.Mterm.add logical_term v uf_man.apron_mapping;
        end
      else
        begin
          let reg_name = Pretty.print_term Format.str_formatter logical_term
                         |> Format.flush_str_formatter in
          let subv = get_subvalues logical_term None in
          List.iter (fun (t, _) ->
              ignore (Format.flush_str_formatter ());
              let v = Pretty.print_term Format.str_formatter t
                      |> Format.flush_str_formatter
                      |> Format.sprintf "%d%s.%s" !var_id reg_name
                      |> Var.of_string
              in
              ensure_variable uf_man v t;
              uf_man.apron_mapping <- Term.Mterm.add t v uf_man.apron_mapping) subv
        end

  
  let cached_vreturn = ref (Ty.Mty.empty)
  let ident_ret = Ident.{pre_name = "$reg"; pre_label = Ident.Slab.empty; pre_loc = None; }
  let create_vreturn man ty =
    try
      Ty.Mty.find ty !cached_vreturn
    with
    | Not_found ->
      let v  = Term.create_vsymbol ident_ret ty in
      add_lvariable_to_env man v;
      cached_vreturn := Ty.Mty.add ty v !cached_vreturn;
      v

  let add_variable_to_env (man, uf_man) psym =
    incr var_id;
    let open Expr in
    let open Ity in
    let open Ty in
    let variable_type = Ity.(psym.pv_ity) in
    let logical_term =
      match Expr.term_of_expr ~prop:false (Expr.e_var psym) with
      | Some s -> s
      | None -> assert false
    in
    ignore (Format.flush_str_formatter ());
    match Ity.(variable_type.ity_node), (Term.t_type logical_term).ty_node with
    | _ when Ty.ty_equal (t_type logical_term) ty_int ->
      let reg_name = Pretty.print_term Format.str_formatter logical_term
                     |> Format.flush_str_formatter
                     |> Format.sprintf "%d%s" !var_id in
      let v =
        Var.of_string reg_name in
      assert (not (Environment.mem_var uf_man.env v));
      ensure_variable uf_man v logical_term;
      uf_man.apron_mapping <- Term.Mterm.add logical_term v uf_man.apron_mapping
    | _ when Ty.ty_equal (t_type logical_term) ty_bool ->
      let reg_name = Pretty.print_term Format.str_formatter logical_term
                     |> Format.flush_str_formatter
                     |> Format.sprintf "%d%s" !var_id in
      let v =
        Var.of_string reg_name in
      assert (not (Environment.mem_var uf_man.env v));
      ensure_variable uf_man v logical_term;
      uf_man.apron_mapping <- Term.Mterm.add logical_term v uf_man.apron_mapping;
    | _ when Ity.ity_equal variable_type Ity.ity_unit
      -> ()
    | Ity.Ityreg(reg), Tyapp(_, _) -> 
      begin
        let reg_name = 
          Ity.print_reg_name Format.str_formatter reg
          |> Format.flush_str_formatter
        in
        let vret = create_vreturn (man, uf_man) (t_type logical_term) in
        let vret = t_var vret in
        let subv = get_subvalues vret (Some reg.reg_its) in
        let subv_r = get_subvalues logical_term (Some reg.reg_its) in
        let subv = List.combine subv subv_r in
        let proj_list =
          List.fold_left (fun acc ((generic_region_term, pfield), (real_term, _)) ->
              let pfield = match pfield with
                | Some s -> s
                | None -> assert false
              in

              ignore (Format.flush_str_formatter ());
              let v = Pretty.print_term Format.str_formatter generic_region_term
                      |> Format.flush_str_formatter
                      |> Format.sprintf "r$%s.%s" reg_name
                      |> Var.of_string
              in
              ensure_variable uf_man v real_term;
              let accessor = match pfield.rs_field with
                | Some s -> s
                | None -> assert false
              in
              uf_man.apron_mapping <- Term.Mterm.add real_term v uf_man.apron_mapping;
              (accessor, real_term) :: acc
            ) [] subv
        in
        uf_man.region_mapping <- Ity.Mreg.add reg proj_list uf_man.region_mapping
      end
    | Ity.Ityapp(_), _ ->
      Format.eprintf "Let's check that ";
      Ity.print_ity Format.err_formatter variable_type;
      Format.eprintf " has only non mutable fields.";
      let reg_name = Ity.print_pv Format.str_formatter psym
                     |> Format.flush_str_formatter in
      let subv = get_subvalues logical_term None in
      List.iter (fun (t, _) ->
          ignore (Format.flush_str_formatter ());
          let v = Pretty.print_term Format.str_formatter t
                  |> Format.flush_str_formatter
                  |> Format.sprintf "%d%s.%s" !var_id reg_name
                  |> Var.of_string
          in
          ensure_variable uf_man v t;
          uf_man.apron_mapping <- Term.Mterm.add t v uf_man.apron_mapping) subv;
    | _ ->
      (* We can safely give up on a, as no integer variable can descend from it (because it is well typed) *)
      Format.eprintf "Variable could not be added properly: ";
      Pretty.print_term Format.err_formatter logical_term;
      Format.eprintf " of type ";
      Ity.print_ity Format.err_formatter variable_type;
      Format.eprintf "@.";
      ()

  let rec forget_term (man, uf_man) t =
    let deps =
      try
        Mterm.find t uf_man.term_depend
      with 
      | Not_found -> Mterm.empty
    in
    let c = get_class_for_term uf_man t in
    let vars_to_forget =
      get_subvalues t None
      |> List.fold_left (fun f (a, _) ->
          let v = Term.Mterm.find a uf_man.apron_mapping in
          fun (a, b) ->
            let mt, (c, d) = f (a, b) in
            let c = 
              match mt with
              | None -> c
              | Some cl ->
                let linexpr = Linexpr1.make uf_man.env in
                Linexpr1.set_array linexpr [|Coeff.s_of_int 1, v|] None;
                let Some a = Hashtbl.find uf_man.classes_var_mapping cl in
                D.assign_linexpr man c a linexpr None
            in
            mt, (D.forget_array man c [|v|] false, d) )
        (fun (a, b) ->
          let mt, bs = Union_find.forget c b.classes in
           if mt <> None then begin
           Format.eprintf "forgetting@.";
           Union_find.print b.classes;
           end;
          mt, (a, { b with classes = bs }))
    in
    Mterm.fold_left (fun f t _ ->
        let g = forget_term (man, uf_man) t in
        (fun d -> g d |> f))
      (fun a -> snd (vars_to_forget a))
    deps

  let forget_var m v = forget_term m (t_var v)

  let forget_region (man, uf_man) v b =
    let terms = Ity.Mreg.find v uf_man.region_mapping in
    let members =
      Ity.Mpv.fold_left (fun acc c () ->
          let _, t =
            try
              List.find (fun (p, _) ->
                  Ity.pv_equal p c) terms
            with
            | Not_found ->
              Format.eprintf "Couldn't find projection for field ";
              Ity.print_pv Format.err_formatter c;
              Format.eprintf "@.";
              Format.eprintf "(known fields: ";
              List.iter (fun (p, _) ->
                  Ity.print_pv Format.err_formatter p;
                  Format.eprintf " @.";
                ) terms;
              Format.eprintf ")@.";
              assert false
          in
          t::acc
        ) [] b in
    List.fold_left (fun f t ->
        let a = forget_term (man, uf_man) t in
        fun x -> f x |> a) (fun x -> x) members

  let to_term (man, uf_man) (a, b) =
    D.to_term S.env S.pmod man a (fun a ->
        try
          Hashtbl.find uf_man.variable_mapping a
        with 
        | Not_found ->
          Format.eprintf "Couldn't find variable %s@." (Var.to_string a);
          raise Not_found
      )

  let update_possible_substitutions (man, uf_man) =
    Union_find.print uf_man.every_term;
    let k = ref 0 in
    Union_find.fold_equal (fun () a b ->
        incr k;
        Format.eprintf "%d@." !k;
        let a = Hashtbl.find uf_man.class_mapping a in
        let b = Hashtbl.find uf_man.class_mapping b in
        let tda = get_td uf_man a in
        let tdb = get_td uf_man b in
        let replaceby a b t =
          t_map (fun t ->
              if t_equal t a then b else t) t
        in
        let l = Mterm.fold_left (fun l k _ ->
            ((replaceby a b) k, k) :: l) [] tda in
        let l = Mterm.fold_left (fun l k _ ->
            (k, (replaceby b a) k) :: l) l tdb in
        let tda, tdb = List.fold_left (fun (ma, mb) (for_b, for_a) ->
            Mterm.add for_a () ma, Mterm.add for_b () mb) (Mterm.empty, Mterm.empty) l in
        List.iter (fun (a, b) ->
            ignore (get_class_for_term uf_man a, get_class_for_term uf_man b)) l;
        uf_man.term_depend <- Mterm.add a tda (Mterm.add b tdb uf_man.term_depend);
      ) () uf_man.every_term;
    Format.eprintf "done%d@." (Environment.size uf_man.env);
    Hashtbl.iter (fun _ t ->
        Pretty.print_term Format.err_formatter t;
        Format.eprintf "@.";
      ) uf_man.class_mapping
end
