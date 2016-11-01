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

  module TermToVar = O2oterm.Make(struct type t = Var.t end)
  module TermToClass = O2oterm.Make(struct type t = Union_find.t end)


  type uf_man = {
    variable_mapping: (Apron.Var.t, Term.term) Hashtbl.t;
    mutable apron_mapping: Var.t Term.Mterm.t;
    mutable region_mapping: (Ity.pvsymbol * Term.term) list Ity.Mreg.t;
    mutable env: Environment.t;

    mutable defined_terms: unit Mterm.t;

    (* UF_QF *)
    mutable class_to_term: TermToClass.t;
    mutable var_to_term: TermToVar.t;
  }

  type uf_t = { classes: Union_find.set;
                uf_to_var: TermToVar.t;
                }


  type man = A.man * uf_man
  type env = unit
  type t = A.t * uf_t

  let create_manager () =
    A.create_manager (), { variable_mapping = Hashtbl.create 512;
                           apron_mapping = Term.Mterm.empty;
                           region_mapping = Ity.Mreg.empty;
                           env = Environment.make [||] [||];
                           defined_terms = Mterm.empty;

                           class_to_term = TermToClass.empty;
                           var_to_term = TermToVar.empty;
                         }

  let empty_uf_domain = { classes = Union_find.empty; uf_to_var = TermToVar.empty; }

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

  (* probably not clever enough, will not work with a complex CFG with exceptions etc *)
  let join_uf uf_man a b =
    Union_find.print a.classes;
    Union_find.print b.classes;
    Union_find.print (Union_find.join a.classes b.classes);
    Format.eprintf "joining@.";
    let uf_to_var = TermToVar.union a.uf_to_var b.uf_to_var in
    { classes = Union_find.join a.classes b.classes; uf_to_var; }


  let join (man, uf_man) (a, b) (c, d) =
    A.join man a c, join_uf uf_man b d

  let join_list man l = match l with
    | [] -> assert false
    | t::q -> List.fold_left (join man) t q

  let widening (man, uf_man) (a, b) (c, d) =
    A.widening man a c, join_uf uf_man b d

  let print fmt (a, b) = A.print fmt a

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

  let get_class_for_term uf_man t =
    try
      TermToClass.to_t uf_man.class_to_term t
    with
    | Not_found ->
      let c = Union_find.new_class () in
      uf_man.class_to_term <- TermToClass.add uf_man.class_to_term t c;
      c

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

  let get_equivs uf_man uf t =
    let tcl = TermToClass.to_t uf_man.class_to_term t in
    match t.t_node with
    | Tvar(_) | Tconst(_) -> List.map (TermToClass.to_term uf_man.class_to_term) (Union_find.get_class tcl uf)
    | Tapp(lsym, args) ->
      let l = List.fold_left (fun args argi ->
          let tclarg = get_class_for_term uf_man argi in
          let argsi =
            List.map (TermToClass.to_term uf_man.class_to_term) (Union_find.get_class tclarg uf) in
          List.map (fun ai ->
              List.map (fun l -> ai::l) args) argsi |> List.concat) [[]] args
      in
      l
      |> List.map List.rev
      |> List.map (fun a -> t_app lsym a (Some (t_type t)))
    | _ -> [t]



  let get_var_for_term id uf_man t =
    try
      TermToVar.to_t uf_man.var_to_term t
    with
    | Not_found ->
      let v = 
        ignore (Format.flush_str_formatter ());
        Pretty.print_term Format.str_formatter t
        |> Format.flush_str_formatter
        |> Format.sprintf "uf%d%s" id
        |> Var.of_string
      in
      uf_man.env <- Environment.add uf_man.env [|v|] [||];
      uf_man.var_to_term <- TermToVar.add uf_man.var_to_term t v;
      v
  
  let to_term (man, uf_man) (a, b) =
    let t = 
      D.to_term S.env S.pmod man a (fun a ->
          try
            Hashtbl.find uf_man.variable_mapping a
          with 
          | Not_found ->
            try
              Format.eprintf "Couldn't find variable %s, trying uf@." (Var.to_string a);
              let t = TermToVar.to_term b.uf_to_var a in
              let tcl = get_class_for_term uf_man t in
                let repr = Union_find.repr tcl b.classes in
              assert (t_equal t (TermToClass.to_term uf_man.class_to_term repr));
              t

            with
            | Not_found ->
              Format.eprintf "Couldn't find variable %s@." (Var.to_string a);
              raise Not_found
        )
    in
    Union_find.fold_class (fun t a b ->
        let a = TermToClass.to_term uf_man.class_to_term a in
        let b = TermToClass.to_term uf_man.class_to_term b in
        t_and_simp t (t_equ a b)) t b.classes


  
  let get_class_for_term_ro uf_man t =
    TermToClass.to_t uf_man.class_to_term t

  let do_eq (man, uf_man) a b =
    fun (d, ud) ->
      Format.eprintf "!!! equality";
      Pretty.print_term Format.err_formatter a;
      Format.eprintf " = ";
      Pretty.print_term Format.err_formatter b;
      let all_values = Union_find.flat ud.classes in
      Format.eprintf " -> %d@." (List.length all_values);
      let all_values = List.map (TermToClass.to_term uf_man.class_to_term) all_values in
      let d, ud = List.fold_left (fun (d, ud) v ->
          let rec replaceby t =
            if t_equal t a then
              b
            else
              t_map replaceby t
          in
          let v' = replaceby v in
          if t_equal v v' then
            d, ud
          else
            let _ =
              Format.eprintf "--  adding class for ";
              Pretty.print_term Format.err_formatter v;
              Format.eprintf " i.e. ";
              Pretty.print_term Format.err_formatter v';
              Format.eprintf "@.";
            in
            let cl = (get_class_for_term uf_man v |> Union_find.repr) ud.classes in
            let cl' = (get_class_for_term uf_man v' |> Union_find.repr) ud.classes in
            if cl = cl' then
              d, ud
            else
              begin
      let t = to_term (man, uf_man) (d, ud) in
      Pretty.print_term Format.err_formatter t;
                let ud = { ud with classes = Union_find.union cl cl' ud.classes } in
                let var = try
                    Some (TermToVar.to_t ud.uf_to_var (TermToClass.to_term uf_man.class_to_term cl))
                  with
                  | Not_found -> None
                in
                let var' = try
                    Some (TermToVar.to_t ud.uf_to_var (TermToClass.to_term uf_man.class_to_term cl'))
                  with
                  | Not_found -> None
                in
                match var, var' with
                | Some var, Some var' ->
                  let final_repr = Union_find.repr cl ud.classes in
                  let t = TermToClass.to_term uf_man.class_to_term final_repr in
                  assert (Union_find.repr cl' ud.classes = final_repr);
                  let uf_to_var = TermToVar.remove_t ud.uf_to_var var in
                  let uf_to_var = TermToVar.remove_t uf_to_var var' in
                  let uf_to_var = TermToVar.add uf_to_var t var in
                  let ud = { ud with uf_to_var } in
                  let linexpr = Linexpr1.make uf_man.env in
                  Linexpr1.set_coeff linexpr var (Coeff.s_of_int 1);
                  let d = D.assign_linexpr man d var' linexpr None in
                  D.forget_array man d [|var'|] false, ud
                | Some var, None  | None, Some var->
                  let final_repr = Union_find.repr cl ud.classes in
                  let t = TermToClass.to_term uf_man.class_to_term final_repr in
                  assert (Union_find.repr cl' ud.classes = final_repr);
                  let uf_to_var = TermToVar.remove_t ud.uf_to_var var in
                  let uf_to_var = TermToVar.add uf_to_var t var in
                  let ud = { ud with uf_to_var } in
                  d, ud
                | None, None -> d, ud
              end

        ) (d, ud) all_values in
      let ud = { ud with classes = Union_find.union (get_class_for_term uf_man a) (get_class_for_term uf_man b) ud.classes } in
      Format.eprintf "equality done attempt@.@.@.@.@.";
      let t = to_term (man, uf_man) (d, ud) in
      Pretty.print_term Format.err_formatter t;
      Format.eprintf "equality done@.@.@.@.@.";
      d, ud



  (** Get a set of (apron) linear expressions from a constraint stated in why3 logic.
   *
   * The resulting list of linear expressions is weaker than the original why3
   * formula.
   * In the most imprecise case, it returns an empty list.
   **)
  let meet_term: man -> Term.term -> (t -> t) =
    let meetid = ref 0 in
    fun (man, uf_man) t ->
      incr meetid;
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
              let myvar = get_var_for_term !meetid uf_man t in
              let g = !f in
              let tcl = get_class_for_term uf_man t in
              f := (fun u ->
                  let u = g u in
                  let equivs = get_equivs uf_man u.classes t in
                  let classes = List.fold_left (fun classes u ->
                      Union_find.union tcl (get_class_for_term uf_man u) classes) u.classes equivs in
                  let repr = Union_find.repr tcl u.classes in
                  let u = { u with classes } in
                  let t = TermToClass.to_term uf_man.class_to_term repr in
                  { u with uf_to_var = TermToVar.add u.uf_to_var t myvar });
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
                let g = do_eq (man, uf_man) a b in
                (fun (d, ud) ->
                   let d, ud = g (d, ud) in
                   let a, b = d, f ud in
      let t = to_term (man, uf_man) (a, b) in
      Pretty.print_term Format.err_formatter t;
                   a, b
                )
              else
                (fun (a, b) -> a, f b)
            in
            let f =
              if Ty.ty_equal (t_type a) Ty.ty_int then f
              else fun x -> x
            in

            (fun (d, a) ->
               let d, a = f (d, a) in
               D.meet_lincons_array man d arr, a)
          | Tapp(func, [a;b]) when ls_equal ps_equ func ->
            let f_uf = do_eq (man, uf_man) a b in
            let subv_a = get_subvalues a None in
            let subv_b = get_subvalues b None in
            List.combine subv_a subv_b 
            |> List.fold_left (fun f ((a, _), (b, _)) ->
                let g = aux (t_app ps_equ [a; b] None) in
                (fun abs ->
                   g abs |> f)) f_uf
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
        let f = aux t in
        (fun d ->
           Format.eprintf "\027[32mMeeting\027[0m.";
           Format.eprintf " with "; Pretty.print_term Format.err_formatter t;
           Format.eprintf "@.before %d -> " (Union_find.flat (snd d).classes |> List.length);
           let t = to_term (man, uf_man) d in
           Pretty.print_term Format.err_formatter t;
           let d = f d in
           Format.eprintf "@.after %d -> " (Union_find.flat (snd d).classes |> List.length);
           let t = to_term (man, uf_man) d in
           Pretty.print_term Format.err_formatter t;
           Format.eprintf "@.";
           d)
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
    let f = fun (a, b) ->
      Format.eprintf "forgetting… ";
      Pretty.print_term Format.err_formatter t;
      Format.eprintf " |  ";
      Pretty.print_term Format.err_formatter (to_term (man, uf_man) (a, b));
      Format.eprintf "@.";

      let all_values = Union_find.flat b.classes in
      let all_values = List.map (TermToClass.to_term uf_man.class_to_term) all_values in
      List.fold_left (fun (a, b) v ->
              Format.eprintf "examining 1… ";
              Pretty.print_term Format.err_formatter v;
              Format.eprintf "@.";
          let found = ref false in
          let rec is_in myt =
            if t_equal t myt then
              found := true;
            t_map is_in myt
          in
          is_in v |> ignore;
          if !found && not (t_equal t v) then
            begin
              let cl = get_class_for_term uf_man v in
              Format.eprintf "examining (%d)… " (List.length (Union_find.get_class cl b.classes));
              Pretty.print_term Format.err_formatter v;
              Format.eprintf "@.";
              let was_repr = cl = Union_find.repr cl b.classes in
              let maybe_repr, s = Union_find.forget cl b.classes in
              let b = { b with classes = s } in
                    Format.eprintf "notrepr!!@.";
              if was_repr then
                try
                    Format.eprintf "repr!!@.";
                  let myv = TermToVar.to_t b.uf_to_var v in
                  match maybe_repr with
                  | None -> 
                    Format.eprintf "none!!@.";
                    let uf_to_var = TermToVar.remove_term b.uf_to_var v in
                    D.forget_array man a [|myv|] false, { b with uf_to_var }
                  | Some s ->
                    let t = TermToClass.to_term uf_man.class_to_term s in
                    let cl = Union_find.get_class s b.classes in
              Format.eprintf "found term… ";
              List.map (TermToClass.to_term uf_man.class_to_term) cl |>
              List.iter (Pretty.print_term Format.err_formatter);
              Format.eprintf "@.";
                    let uf_to_var = TermToVar.remove_term b.uf_to_var v in
                    let uf_to_var = TermToVar.add uf_to_var t myv in
                    a, { b with uf_to_var }
                with
                | Not_found ->
                    Format.eprintf "notfound!!@.";
                  a, b
              else
                a, b
            end
          else
            a, b
        ) (a, b) all_values
    in



    get_subvalues t None
    |> List.fold_left (fun f (a, _) ->
        let v = Term.Mterm.find a uf_man.apron_mapping in
        fun (a, b) ->
          let a ,b = f (a,b) in
          D.forget_array man a [|v|] false, b )
      (fun x ->
         let a, b = f x in
         let cl = get_class_for_term uf_man t in
         let _, classes = Union_find.forget cl b.classes in
         let b = { b with classes } in
      Format.eprintf "after… ";
      Pretty.print_term Format.err_formatter t;
      Format.eprintf " |  ";
      Pretty.print_term Format.err_formatter (to_term (man, uf_man) (a, b));
      Format.eprintf "@.";
      a, b)

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

  let update_possible_substitutions (man, uf_man) =
    ()
end
