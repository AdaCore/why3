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

  module TermToVar = O2mterm.Make(struct type t = Var.t end)
  module TermToVaro = O2oterm.Make(struct type t = Var.t end)
  module TermToClass = O2oterm.Make(struct type t = Union_find.t end)


  type uf_man = {
    variable_mapping: (Apron.Var.t, Term.term) Hashtbl.t;
    mutable apron_mapping: Var.t Term.Mterm.t;
    mutable region_mapping: (Ity.pvsymbol * Term.term) list Ity.Mreg.t;
    mutable region_var: Term.vsymbol list Ity.Mreg.t;
    mutable env: Environment.t;

    mutable defined_terms: unit Mterm.t;

    (* UF_QF *)
    mutable class_to_term: TermToClass.t;
    mutable var_to_term: TermToVar.t;

    apron_var: Var.t;
    quant_var: Term.term;
  }

  type uf_t = {
    classes: Union_find.set;
    uf_to_var: TermToVar.t;
    quantified_vars: TermToVaro.t;
  }


  type man = A.man * uf_man
  type env = unit
  type t = A.t * uf_t

  let create_manager () =
    let ident_ret = Ident.{pre_name = "w"; pre_label = Ident.Slab.empty; pre_loc = None; } in
    let v  = Term.create_vsymbol ident_ret Ty.ty_int in
    let apron_var = Var.of_string "$quant" in
    let quant_var = t_var v in
    let apron_mapping = Term.Mterm.add quant_var apron_var Term.Mterm.empty in
    A.create_manager (), { variable_mapping = Hashtbl.create 512;
                           apron_mapping;
                           region_mapping = Ity.Mreg.empty;
                           region_var = Ity.Mreg.empty;
                           env = Environment.make [|apron_var|] [||];
                           defined_terms = Mterm.empty;

                           class_to_term = TermToClass.empty;
                           var_to_term = TermToVar.empty;
                           apron_var;
                           quant_var; 
                         }

  let empty_uf_domain = {
    classes = Union_find.empty;
    uf_to_var = TermToVar.empty;
    quantified_vars = TermToVaro.empty; }

  let bottom (man, uf_man) env =
    A.bottom man uf_man.env, empty_uf_domain

  let top (man, uf_man) env =
    A.top man uf_man.env, empty_uf_domain

  let canonicalize (man, _) (a, b) =
    A.canonicalize man a

  let is_bottom (man, _) (a, b) =
    A.is_bottom man a

  let p = Pretty.print_term Format.err_formatter
  
  let get_class_for_term uf_man t =
    try
      TermToClass.to_t uf_man.class_to_term t
    with
    | Not_found ->
      let c = Union_find.new_class () in
      uf_man.class_to_term <- TermToClass.add uf_man.class_to_term t c;
      c
  
  
  let get_equivs uf_man uf t =
    let tcl = TermToClass.to_t uf_man.class_to_term t in
    match t.t_node with
    | Tvar(_) | Tconst(_) when not( Ty.ty_equal (t_type t) Ty.ty_int) ->
      List.map (TermToClass.to_term uf_man.class_to_term) (Union_find.get_class tcl uf)
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

  let do_eq_ns (man, uf_man) a b =
    if not (Ty.ty_equal (t_type a) Ity.ty_unit) then
    fun (d, ud) ->
      let all_values = Union_find.flat ud.classes in
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
            let cl = (get_class_for_term uf_man v |> Union_find.repr) ud.classes in
            let cl' = (get_class_for_term uf_man v' |> Union_find.repr) ud.classes in
            if cl = cl' then
              d, ud
            else
              begin
                let ud =
                  if not (Ty.ty_equal (t_type v) Ty.ty_int) then
                    { ud with classes = Union_find.union cl cl' ud.classes }
                  else
                    { ud with classes = Union_find.union cl' cl' ud.classes }
                in
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
                | Some var, Some var' when var <> var' ->
                  let expr = Linexpr1.make uf_man.env in
                  Linexpr1.set_coeff expr var' (Coeff.s_of_int 1);
                  Linexpr1.set_coeff expr var (Coeff.s_of_int (-1));
                  let lincons = Lincons1.make expr Lincons1.EQ in
                  let lincons_array = Lincons1.array_make uf_man.env 1 in
                  Lincons1.array_set lincons_array 0 lincons;
                  Pretty.print_term Format.err_formatter v;
                  Pretty.print_term Format.err_formatter v';
                  Format.eprintf "blip@.";
                  let d = D.meet_lincons_array man d lincons_array in
                  d, ud
                | _ ->
                  d, ud
              end

        ) (d, ud) all_values in
      let ud =
        if not (Ty.ty_equal (t_type a) (Ty.ty_int)) then
          { ud with classes = Union_find.union (get_class_for_term uf_man a) (get_class_for_term uf_man b) ud.classes }
        else ud
      in
      d, ud
    else
      fun x -> x

  let do_eq (man, uf_man) a b =
    let f = do_eq_ns (man, uf_man) a b in
    let g = do_eq_ns (man, uf_man) b a in
    (fun x ->
       f x |> g )



  (* probably not clever enough, will not work with a complex CFG with exceptions etc *)
  let join_uf (man, uf_man) d a b =
    let d = ref d in
    let eqs = ref [] in
    let classes =  Union_find.join a.classes b.classes in
    let uf_to_var = TermToVar.union (fun v1 v2 ->
        let expr = Linexpr1.make uf_man.env in
        Linexpr1.set_coeff expr v2 (Coeff.s_of_int 1);
        Linexpr1.set_coeff expr v1 (Coeff.s_of_int (-1));
        let lincons = Lincons1.make expr Lincons1.EQ in
        let lincons_array = Lincons1.array_make uf_man.env 1 in
        Lincons1.array_set lincons_array 0 lincons;
        d := D.meet_lincons_array man !d lincons_array; 
        d := D.forget_array man !d [|v2|] false;
      ) (fun te ->
        (*let eqs' =
          try
            get_equivs uf_man classes te |> List.map (fun t -> t, te)
          with
          | Not_found -> []
        in
        eqs := !eqs @ eqs';*) ()
      )
      a.uf_to_var b.uf_to_var in
    let d = !d in
    let e = { classes; uf_to_var; quantified_vars = a.quantified_vars; } in
    List.fold_left (fun (d, e) (a, b) ->
        D.print Format.std_formatter d;
        let d, e = do_eq (man, uf_man) a b (d, e) in
        Format.printf "@.";
        D.print Format.std_formatter d;
        assert false |> ignore;
      d, e) (d, e) !eqs

  let print fmt (a, b) = A.print fmt a

  let join (man, uf_man) (a, b) (c, d) =
    (* Why3 terms and APRON variables must be kept consistent. So. First there is
     * the case where two different terms are linked to the same APRON variable.
     * One on them must be erased. *)
    let terms = TermToVar.get_inconsistent b.uf_to_var d.uf_to_var in
    let c, d = List.fold_left (fun (c, d) t ->
        let v = TermToVar.to_t d.uf_to_var t in
        let d = { d with uf_to_var = TermToVar.remove_term d.uf_to_var t } in
        let c = try
            TermToVar.to_term d.uf_to_var v |> ignore;
            c
          with
          | Not_found ->
            D.forget_array man c [|v|] false
        in
        c, d) (c, d) terms
    in

    let a = A.join man a c in
    (* And then join_uf takes care of one term linked to 2 variables. (They are made equal,
     * and then forgotten.) *)
    let a, e = join_uf (man, uf_man) a b d in
    a, e

  let join_list man l = match l with
    | [] -> assert false
    | t::q -> List.fold_left (join man) t q

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

  let class_exists uf_man u t =
    let cl = get_class_for_term uf_man t in
    Union_find.get_class cl u.classes |> List.length > 1


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
  
  exception Bad_domain of D.t

  let rec extract_term (man, uf_man) is_in (dom, b) v =
    let find_var = fun a ->
      if a = uf_man.apron_var then
        uf_man.quant_var
      else
        try
          let candidate = Hashtbl.find uf_man.variable_mapping a in
          if is_in candidate then
            raise Not_found
          else
            candidate
        with 
        | Not_found ->
          try
            let t = TermToVar.to_terms b.uf_to_var a in
            assert (Mterm.cardinal t >= 1);
            Mterm.filter (fun i _ -> not (is_in i)) t |> Mterm.choose |> fst

          with
          | Not_found ->
            raise (Bad_domain (D.forget_array man dom [|a|] false))
    in
    match D.get_linexpr man dom v with
    | Some l ->
      begin
        try
          let t = Ai_logic.varlist_to_term find_var l in
          assert (Ty.ty_equal (t_type t) Ty.ty_int);
          Some t
        with
        | Bad_domain(a) -> extract_term (man, uf_man) is_in (a, b) v
      end
    | None -> None

  
  let to_term (man, uf_man) (a, b) =
    let find_var = fun a ->
      if a = uf_man.apron_var then
        uf_man.quant_var
      else
        try
          Hashtbl.find uf_man.variable_mapping a
        with 
        | Not_found ->
          try
            let t = TermToVar.to_term b.uf_to_var a in
            t

          with
          | Not_found ->
            Format.eprintf "Couldn't find variable %s@." (Var.to_string a);
            raise Not_found
    in
    let t = 
      D.to_term S.env S.pmod man a find_var    in
    let t = Union_find.fold_class (fun t a b ->
        let a = TermToClass.to_term uf_man.class_to_term a in
        let b = TermToClass.to_term uf_man.class_to_term b in
        t_and t (t_equ a b)) t b.classes
    in
    let var = match uf_man.quant_var.t_node with
      | Tvar(v) -> v
      | _ -> assert false
    in
    t_quant Tforall (t_close_quant [var] [] t)

  
  let get_class_for_term_ro uf_man t =
    TermToClass.to_t uf_man.class_to_term t

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
              let myvar = get_var_for_term !meetid uf_man t in
              let g = !f in
              let tcl = get_class_for_term uf_man t in
              f := (fun (d, u) ->
                  let d, u = g (d, u) in
                  let d, u =
                    try
                      if not (t_equal (TermToVar.to_term u.uf_to_var myvar) t) then
                        D.forget_array man d [|myvar|] false, { u with uf_to_var = TermToVar.remove_t u.uf_to_var myvar }
                      else
                        d, u
                    with
                    | Not_found -> d, u
                  in
                  (*let d = D.forget_array man d [|myvar|] false in*)
                  let d, u =
                    try
                      let v' = TermToVar.to_t u.uf_to_var t in
                      if v' = myvar then
                        d, u
                      else
                        begin
                          let u = { u with uf_to_var = TermToVar.remove_term u.uf_to_var t } in
                          let expr = Linexpr1.make uf_man.env in
                          Linexpr1.set_coeff expr v' (Coeff.s_of_int 1);
                          Linexpr1.set_coeff expr myvar (Coeff.s_of_int (-1));
                          let lincons = Lincons1.make expr Lincons1.EQ in
                          let lincons_array = Lincons1.array_make uf_man.env 1 in
                          Lincons1.array_set lincons_array 0 lincons;
                          let d = D.meet_lincons_array man d lincons_array in
                          D.forget_array man d [|v'|] false, u
                        end
                    with
                    | Not_found ->
                      let u = { u with uf_to_var = TermToVar.remove_t u.uf_to_var myvar } in
                      D.forget_array man d [|myvar|] false, u
                  in
                  let equivs = get_equivs uf_man u.classes t in
                  let classes, uf_to_var, d = List.fold_left (fun (classes, uf_to_var, d) u ->
                      let uf_to_var, d = 
                        try
                          let v = (TermToVar.to_t uf_to_var u) in
                          let expr = Linexpr1.make uf_man.env in
                          Linexpr1.set_coeff expr v (Coeff.s_of_int 1);
                          Linexpr1.set_coeff expr myvar (Coeff.s_of_int (-1));
                          let lincons = Lincons1.make expr Lincons1.EQ in
                          let lincons_array = Lincons1.array_make uf_man.env 1 in
                          Lincons1.array_set lincons_array 0 lincons;
                          let d = if v <> myvar then D.meet_lincons_array man d lincons_array else d in
                          uf_to_var, d
                        with
                        | Not_found -> TermToVar.add uf_to_var u myvar, d
                      in
                     classes, uf_to_var,d ) (u.classes, u.uf_to_var, d) equivs in
                  let classes = Union_find.union tcl tcl classes in
                  let u = { u with classes; } in
                  let u = { u with uf_to_var } in
                  d, u
                );
              ([myvar, coeff], 0)
            | Some s ->
              ([s, coeff], 0)
          end
      in

      (* This takes an epsilon-free formula and returns a list of linear expressions weaker than
       * the original formula. *)
      let rec aux t =
        try
          match t.t_node with
          | Tbinop(Tand, a, b) ->
            let fa = aux a in
            let fb = aux b in
            (fun (d, a) ->
               fb (fa (d, a)))
          | Tbinop(Tor, a, b) ->
            let fa = aux a in
            let fb = aux b in
            (fun (d, a) ->
               let a1 = fa (d, a) in
               let a2 = fb (d, a) in
               join (man, uf_man) a1 a2
            )

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
                   let a, b = f (d, ud) in
                   a, b
                )
              else
                f
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
                   g abs |> f
                   )) f_uf
          | Tif(a, b, c) ->
            let fa = aux a in
            let fa_not = aux (t_descend_nots a) in
            let fb = aux b in
            let fc = aux c in
            (fun d ->
               let a1 = fb (fa d) in
               let a2 = fc (fa_not d) in
               join (man, uf_man) a1 a2)
          | Ttrue -> (fun d -> d)
          | _ when t_equal t t_bool_true || t_equal t t_true -> (fun d -> d)
          | Tfalse -> (fun _ -> D.bottom man uf_man.env, empty_uf_domain)
          | _ when t_equal t t_bool_false || t_equal t t_false -> (fun _ -> D.bottom man uf_man.env, empty_uf_domain)
          | Tquant(Tforall, tq) ->
            begin
              match t_open_quant tq with
              | [a], _, t when (Ty.ty_equal a.vs_ty Ty.ty_int) ->
                let quant_var, apron_var = uf_man.quant_var, uf_man.apron_var in (*TermToVaro.choose ud.quantified_vars in*)
                let t = t_descend_nots t in
                let t = t_subst_single a quant_var t in
                aux t
              | _ -> raise (Not_handled t)
            end
          | _ ->
            raise (Not_handled t)
        with
        | Not_handled(t) ->
          Format.eprintf "Couldn't understand entirely the post condition: ";
          Pretty.print_term Format.err_formatter t;
          Format.eprintf "@.";
          (fun d -> d)
      in
      let f = aux t in
      (fun d ->
         let d = f d in
         d)

  let is_leq (man, uf_man) (a, b) (c, d) =
    let a', _ = join_uf (man, uf_man) a b d in
    let c', _ = join_uf (man, uf_man) c b d in
    let b_dom = A.is_leq man a' c' in
    let b_uf = Union_find.is_leq b.classes d.classes in
    b_dom && b_uf

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
    assert (not (Ty.ty_equal ty Ity.ty_unit));
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
        let old_projs, old_vars = try
            Ity.Mreg.find reg uf_man.region_mapping, Ity.Mreg.find reg uf_man.region_var
          with
          | Not_found -> [], []
        in
        uf_man.region_mapping <- Ity.Mreg.add reg (proj_list @ old_projs) uf_man.region_mapping;
        uf_man.region_var <- Ity.Mreg.add reg (Ity.(psym.pv_vs) :: old_vars) uf_man.region_var
      end
    | Ity.Ityapp(_), _ ->
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
            
  let is_in t myt =
    let found = ref false in
    let rec is_in myt =
      if t_equal t myt then
        found := true;
      t_map is_in myt
    in
    is_in myt |> ignore;
    !found

  let rec tdepth t =
    1 + t_fold (fun k' t ->
        max (tdepth t) k') 0 t


  let rec forget_term (man, uf_man) t =
    let f = fun (a, b) ->
      let last_n = ref (-1) in
      let d = ref (a, b) in
      let all_values = ref [] in
      while (
        let all_values' = Union_find.flat (snd !d).classes in
        let all_values' = List.map (TermToClass.to_term uf_man.class_to_term) all_values' in
        all_values := all_values';
        let c = List.length !all_values <> !last_n in
        last_n := List.length !all_values;
      c) do
        let all_values = !all_values in
        let all_values =
          List.filter (fun a -> not (t_equal t a) && is_in t a) all_values |> fun l -> List.append l [t] in
        let int_values, other_values = List.partition (fun t -> Ty.ty_equal (t_type t) Ty.ty_int) all_values in

        let tcl = get_class_for_term uf_man t in
        let alternatives =
          Union_find.get_class tcl b.classes
          |> List.map (TermToClass.to_term uf_man.class_to_term)
          |> List.filter (fun k -> not (is_in t k))
          |> List.sort (fun i j -> compare (tdepth i) (tdepth j))
          |> function
          | [] -> None
          | t::_ -> Some t
        in
        d := List.fold_left (fun (a, b) v ->
                let cl = get_class_for_term uf_man v in
                let b =
                  match alternatives with
                  | None -> b
                  | Some alt ->
                    let rec replaceby myt =
                      if t_equal myt t then
                        alt
                      else
                        t_map replaceby myt
                    in
                    let alt = replaceby v in
                    let altcl = get_class_for_term uf_man alt in
                    let b = { b with classes = Union_find.union altcl altcl b.classes } in
                    let b =
                      { b with classes = Union_find.union altcl cl b.classes }
                    in
                    b
                in
                let _, s = Union_find.forget cl b.classes in
                let b = { b with classes = s } in
                a, b
          ) !d other_values;
        if match int_values with
          | [] -> false
          | t'::[] when t_equal t t' -> false
          | _ -> true
        then
          begin
            let alternatives =
              if not (Ty.ty_equal (t_type t) Ty.ty_int) then
                alternatives
              else
                let myv =
                  try
                    TermToVar.to_t b.uf_to_var t
                  with
                  | Not_found -> Mterm.find t uf_man.apron_mapping
                in
                extract_term (man, uf_man) (is_in t) (a, b) myv
            in
            d :=
              List.fold_left (fun (a, b) v ->
                let cl = get_class_for_term uf_man v in
                let b =
                  match alternatives with
                  | None -> b
                  | Some alt ->
                    let rec replaceby myt =
                      if t_equal myt t then
                        alt
                      else
                        t_map replaceby myt
                    in
                    let alt = replaceby v in
                    let altcl = get_class_for_term uf_man alt in
                    let b = { b with classes = Union_find.union altcl altcl b.classes } in
                    let uf_to_var = 
                      try
                        let myv = TermToVar.to_t b.uf_to_var v in
                        try
                          ignore (TermToVar.to_t b.uf_to_var alt); b.uf_to_var
                        with
                        | Not_found -> TermToVar.add b.uf_to_var alt myv
                      with
                      | Not_found -> b.uf_to_var
                    in
                    let b = { b with uf_to_var } in
                    b
                in
                let _, s = Union_find.forget cl b.classes in
                let b = { b with classes = s } in
                let old_b = b in
                try
                  let myv = TermToVar.to_t old_b.uf_to_var v in
                  try
                    let _t = TermToVar.to_term b.uf_to_var myv in
                    a, b
                  with
                  | Not_found ->
                    D.forget_array man a [|myv|] false, b
                with
                | Not_found ->
                  a, b
              ) !d int_values
          end;
        d :=
        let a, b = !d in
              let uf_to_var, orphan_vars = TermToVar.filter_term b.uf_to_var (fun t' ->
                  not (is_in t t')) in
              D.forget_array man a (Array.of_list orphan_vars) false, { b with uf_to_var }
              ;
      done;
      !d
    in
    get_subvalues t None
    |> List.fold_left (fun f (a, _) ->
        if t_equal a t then
          f
        else
          let g = forget_term (man, uf_man) a in
          fun d  ->
            g d |> f)
      (fun x ->
         let d, b = f x in
         let cl = get_class_for_term uf_man t in
         let _, classes = Union_find.forget cl b.classes in
         let b = { b with classes } in
         if Ty.ty_equal Ty.ty_int (t_type t) then
           let v = Term.Mterm.find t uf_man.apron_mapping in
           D.forget_array man d [|v|] false, b
         else
           d, b)

  let forget_var m v = forget_term m (t_var v)

  let forget_region (man, uf_man) v b =
    let members = Ity.Mreg.find v uf_man.region_mapping |> List.map snd in
    let vars = Ity.Mreg.find v uf_man.region_var in
    let f = List.fold_left (fun f t ->
        let a = forget_term (man, uf_man) t in
        fun x -> f x |> a) (fun x -> x) members in
    List.fold_left (fun f v ->
        fun (d, ud) ->
          let acl = get_class_for_term uf_man (t_var v) in
          let ud = { ud with classes = Union_find.forget acl ud.classes |> snd } in
          let d = f (d, ud) in
          d) f vars

  let update_possible_substitutions (man, uf_man) =
    ()
  
  let widening (man, uf_man) (a, b) (c, d) =
    let a = A.widening man a c in
    let a, e = join_uf (man, uf_man) a b d in
    a, e

end
