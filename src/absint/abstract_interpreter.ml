
open Format
open Apron

(* Copied from inlining, it looks like it is difficult to use the code from there
 * without messing up the interface. *)

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

module Abstract_interpreter(E: sig
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct
  
  open Term

  let known_logical_ident = Pmodule.(Theory.(E.pmod.mod_theory.th_known))
  let known_pdecl = Pmodule.(Theory.(E.pmod.mod_known))
  
  let th_int = Env.read_theory E.env ["int"] "Int"
  let le_int = Theory.(ns_find_ls th_int.th_export ["infix <="])
  let ge_int = Theory.(ns_find_ls th_int.th_export ["infix >="])
  let lt_int = Theory.(ns_find_ls th_int.th_export ["infix <"])
  let gt_int = Theory.(ns_find_ls th_int.th_export ["infix >"])
  let ad_int = Theory.(ns_find_ls th_int.th_export ["infix +"])
  let min_int = Theory.(ns_find_ls th_int.th_export ["infix -"])
  let min_u_int = Theory.(ns_find_ls th_int.th_export ["prefix -"])
  let mult_int = Theory.(ns_find_ls th_int.th_export ["infix *"])


  (* General purpose inlining stuff *)

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

  (* inline every symbol *)

  let rec t_replace_all t =
    let t = t_map t_replace_all t in
    match t.t_node with
    | Tapp (fs,tl) ->
      t_label_copy t (t_unfold t.t_loc fs tl t.t_ty)
    | _ -> t

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


 


  (* Apron manager *)
  let manpk = Polka.manager_alloc_strict()
  type apron_domain = Polka.strict Polka.t

  type control_point = int

  type domain = apron_domain Abstract1.t

  (* control flow graph *)
  type cfg = {
    (* not one to one *)
    expr_to_control_point: (Expr.expr, control_point) Hashtbl.t;
    g:(int,int,unit,unit,unit) PSHGraph.t;
    mutable control_point_count: int;
    mutable hedge_count: int;
    mutable env: Environment.t;
    mutable apply: apron_domain Apron.Manager.t -> int -> apron_domain Apron.Abstract1.t array -> unit * apron_domain Apron.Abstract1.t;
    mutable loop_invariants: (Expr.expr * control_point) list;
    variable_mapping: (Apron.Var.t, Term.term) Hashtbl.t;
  
  }

  type local_ty = {
      ident_ty: Ity.ity Ident.Mid.t;
      region_ident: (Ity.pvsymbol * Term.term) list Ity.Mreg.t;
      local_vars: Var.t Term.Mterm.t
  }

  let empty_local_ty = { ident_ty = Ident.Mid.empty; region_ident = Ity.Mreg.empty; local_vars = Term.Mterm.empty; }

  exception Unknown_hedge

  (* Some useful constants to express return values and linear expressions *)
  let zero = Coeff.Scalar (Scalar.of_int 0) 
  let one = Coeff.Scalar (Scalar.of_int 1)
  let neg_one = Coeff.Scalar (Scalar.of_int (-1))

  (* Initialize an hedge *)

  let ensure_variable cfg v t =
    if not (Environment.mem_var cfg.env v) then
      begin
        Hashtbl.add cfg.variable_mapping v t;
        cfg.env <- Environment.add cfg.env [|v|] [||]
      end
  
  let ident_ret = Ident.{pre_name = "return"; pre_label = Ident.Slab.empty; pre_loc = None; }
  let cached_vreturn = ref (Ty.Mty.empty)
  let create_vreturn ty =
    try
      Ty.Mty.find ty !cached_vreturn
    with
    | Not_found ->
      let v  = Term.create_vsymbol ident_ret ty in
      cached_vreturn := Ty.Mty.add ty v !cached_vreturn;
      v

  let start_cfg rs =
    let cfg = { expr_to_control_point = Hashtbl.create 100;
      variable_mapping = Hashtbl.create 100;
      control_point_count = 0;
      hedge_count = 0;
      g = PSHGraph.create PSHGraph.stdcompare 3 ();
      apply = (fun _ _ a -> raise Unknown_hedge);
      env = Environment.make [||] [||];
      loop_invariants = []; }
    in
    let open Ident in
    cfg

  (* Adds a new node to the cfg, associated to expr (which is only useful for
   * debugging purpose ATM) *)
  let new_node_cfg cfg expr =
    let i = cfg.control_point_count in
    Hashtbl.add cfg.expr_to_control_point expr i;
    cfg.control_point_count <- i + 1;
    (* save in the cfg *)
    PSHGraph.add_vertex cfg.g i ();
    i

  (* Adds a new hyperedge between a and b, whose effect is described in f *)
  let new_hedge_cfg cfg (a, b) f =
    let hedge = cfg.hedge_count in
    cfg.hedge_count <- cfg.hedge_count + 1;
    PSHGraph.add_hedge cfg.g hedge () ~pred:[|a|] ~succ:[|b|];
    let old_apply = cfg.apply in
    cfg.apply <- begin fun man h tabs ->
      if h = hedge then
        let abs = tabs.(0) in
        (), f man abs
      else old_apply man h tabs
    end

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

  let warning_t s t =
    Format.eprintf "-- warning: %s -- triggered by " s;
    Pretty.print_term Format.err_formatter t;
    Format.eprintf " of type ";
    Pretty.print_ty Format.err_formatter (Term.t_type t);
    Format.eprintf "@."
            
          
  let get_subvalues a ity =
    let open Ty in
    let myty = t_type a in
    let rec aux ty ity =
      match myty.ty_node with
      | _ when ty_equal myty ty_int || ty_equal myty ty_bool ->
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
          | Decl.Dtype({ts_def = Some ty; ts_args = args; _ } as tys) ->
            (* untested code, probably works *)
            let () = assert false in
            let vars = Ty.ts_match_args tys (List.map Ty.ty_var args) in
            aux (Ty.ty_inst vars ty) ity
          | Decl.Ddata([c, b]) ->
            warning_t "Multiple constructors is not supported in abstract interpretation." a; []
          | Decl.Ddata(_) ->
            warning_t "Recursive types is not supported in abstract interpretation." a; []
          | Decl.Dtype({ ts_def = ty; _}) -> (* This happens when a type is private or has an invariant: it can't be accesed
                                              * by the logic, so we give up and only look for projections by looking
                                              * at program projections. *)
            (* warning_t "Could not find type declaration (got type alias)." a; *)
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
    aux myty ity

  (* Get a set of (apron) linear expressions from a constraint stated in why3 logic.
   * ATM it only works for conjunction, and if there is not that much uninterpreted function.
   * In the worst case, it returns an empty list.
   *
   * The resulting list of linear expressions is weaker than the original why3
   * formula. *)
  let linear_expressions_from_term: cfg -> local_ty -> Term.term -> ((domain -> domain) * Var.t list)  = fun cfg local_ty t ->
    let open Term in

    (* First inline everything, for instance needed for references
     * where !i is (!) i and must be replaced by (contents i) *)
    let t = t_replace_all t in

    (* Let's try to remove the nots that we can *)
    let t = t_descend_nots t in

    let local_ty = ref local_ty in

    let var_of_term t =
      try
        Some (Term.Mterm.find t (!local_ty).local_vars)
      with
      | Not_found -> None
    in

    (* Assuming that t is an arithmetic term, this computes the number of ocurrence of variables
     * ando the constant of the arithmetic expression.
     * It returns (variables, constant)
     *
     * For instance, 4 + x + y set cst to 4, and constr to [(x, 1), (y, 1)]
     * *)
    let rec term_to_var_list coeff t =
      match t.t_node with
      | Tvar(a) ->
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
            let c, d = term_to_var_list coeff c in
            (a @ c, b + d)) ([], 0)args
      | Tapp(func, [a;b]) when Term.ls_equal func min_int ->
        let c, d = term_to_var_list coeff a in
        let e, f = term_to_var_list (-coeff) b in
        (c @ e, d + f)
      | Tapp(func, [a]) when Term.ls_equal func min_u_int ->
        term_to_var_list (-coeff)  a;
      | Tapp(func, [{t_node = Tconst(Number.ConstInt(n)); _}; a])
      | Tapp(func, [a; {t_node = Tconst(Number.ConstInt(n)); _};]) when Term.ls_equal func mult_int ->
        let n = Number.compute_int n in
        term_to_var_list ((BigInt.to_int n) * coeff) a
      (* FIXME: need a nice domain for algebraic types *)
      | _ -> (* maybe a record access *)
        begin
          match var_of_term t with
          | None -> Format.eprintf "Could not find term@."; raise (Not_handled t)
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
          (fun d ->
            fb (fa d))
        | Tbinop(Tor, a, b) ->
          let fa = aux a in
          let fb = aux b in
          (fun d ->
             let d1 = fa d in
             let d2 = fb d in
             Abstract1.join manpk d1 d2)
        | Tapp(func, [a; b]) when (Ty.ty_equal (t_type a) Ty.ty_int || Ty.ty_equal (t_type a) Ty.ty_bool)
          && 
          (ls_equal ps_equ func ||
           ls_equal lt_int func ||
           ls_equal gt_int func ||
           ls_equal le_int func ||
           ls_equal ge_int func)

          -> (* ATM, this is handled only for equality and integer comparison *)
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
            let va, ca = term_to_var_list (-base_coeff) a in
            let vb, cb = term_to_var_list base_coeff b in
            let c = ca + cb in
            let v = sum_list (va @ vb) in
            let expr = Linexpr1.make cfg.env in
            let constr = List.map (fun (var, coeff) ->
                Coeff.Scalar (Scalar.of_int coeff), var) v in
            Linexpr1.set_list expr constr None;
            let cons = Lincons1.make expr eq_type in
            Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int c));
            let arr = Lincons1.array_make cfg.env 1 in
            Lincons1.array_set arr 0 cons;
              (fun d ->
                 Abstract1.meet_lincons_array manpk d arr)
        | Tapp(func, [a;b]) when ls_equal ps_equ func ->
          begin
            let open Ty in
            let subv_a = get_subvalues a None in
            let subv_b = get_subvalues b None in
            List.combine subv_a subv_b 
            |> List.fold_left (fun f ((a, _), (b, _)) ->
                let g = aux (t_app ps_equ [a; b] None) in
                (fun abs ->
                   f (g (abs)))) (fun abs -> abs)
          end
        | Tif(a, b, c) ->
          let fa = aux a in
          let fa_not = aux (t_descend_nots a) in
          let fb = aux b in
          let fc = aux c in
          (fun d ->
             let d1 = fb (fa d) in
             let d2 = fc (fa_not d) in
             Abstract1.join manpk d1 d2)
        | Ttrue  | _ when t_equal t t_bool_true -> (fun d -> d)
        | Tfalse | _ when t_equal t t_bool_false -> (fun d -> Abstract1.bottom manpk cfg.env)
        | _ ->
          raise (Not_handled t)
      with
      | Not_handled(t) ->
        Format.eprintf "Couldn't understand entirely the post condition: ";
        Pretty.print_term Format.err_formatter t;
        Format.eprintf "@.";
        (fun d -> d)
    in

    let to_forget = ref [] in
    try
      let open Ty in
      match t.t_node with
      | Teps(tb) ->
        let return, t = Term.t_open_bound tb in
        (* Always use the same variable when returning a value, 
         * otherwise variables keep being created and the previous ones (with the
         * good constraints) can not be accessed *)
        let return_var = create_vreturn (return.vs_ty) in
        let return_term = t_var return_var in
        let subvalues = get_subvalues return_term None in
        let l =
          List.fold_left (fun local_ty (a, _) ->

              ignore (Format.flush_str_formatter ());
              let v = Pretty.print_term Format.str_formatter a
                      |> Format.flush_str_formatter
                      |> Var.of_string
              in
              to_forget := v :: !to_forget;
              ensure_variable cfg v a;
              { local_ty with local_vars = Term.Mterm.add a v local_ty.local_vars }
            ) !local_ty subvalues
        in
        local_ty := l;
        aux (t_subst_single return return_term t), !to_forget
      | _ ->
        aux t, !to_forget
    with
    | e ->
      Format.eprintf "error while computing domain for post conditions: ";
      Pretty.print_term Format.err_formatter t;
      Format.eprintf "@.";
      raise e

  let add_typed_variable cfg local_ty psym variable_type =
    let open Expr in
    let open Ity in
    let open Ty in
    let variable_ident = (Ity.(Term.(psym.pv_vs.vs_name))) in
    let logical_term =
      match Expr.term_of_expr ~prop:false (Expr.e_var psym) with
      | Some s -> s
      | None -> assert false
    in
    let local_ty = { local_ty with
                     ident_ty = Ident.Mid.add variable_ident variable_type local_ty.ident_ty } in
    ignore (Format.flush_str_formatter ());
    let local_ty = 
      match Ity.(variable_type.ity_node), (Term.t_type logical_term).ty_node with
      | _ when Ty.ty_equal (t_type logical_term) ty_int ->
        let reg_name = Ity.print_pv Format.str_formatter psym
        |> Format.flush_str_formatter in
        let v =
          Var.of_string reg_name in
        ensure_variable cfg v logical_term;
        { local_ty with local_vars = Term.Mterm.add logical_term v local_ty.local_vars }
      | _ when Ty.ty_equal (t_type logical_term) ty_bool ->
        let reg_name = Ity.print_pv Format.str_formatter psym
        |> Format.flush_str_formatter in
        let v =
          Var.of_string reg_name in
        ensure_variable cfg v logical_term;
        { local_ty with local_vars = Term.Mterm.add logical_term v local_ty.local_vars }
      | _ when Ity.ity_equal variable_type Ity.ity_unit
        -> local_ty
      | Ity.Ityreg(reg), Tyapp(tys, vars) -> 
        begin
          let reg_name = 
            Ity.print_reg_name Format.str_formatter reg
            |> Format.flush_str_formatter
          in
          let vret = create_vreturn (t_type logical_term) in
          let vret = t_var vret in
          let subv = get_subvalues vret (Some reg.reg_its) in
          let subv_r = get_subvalues logical_term (Some reg.reg_its) in
          let subv = List.combine subv subv_r in
          let local_ty, proj_list =
            List.fold_left (fun (local_ty, acc) ((generic_region_term, pfield), (real_term, _)) ->
                let pfield = match pfield with
                  | Some s -> s
                  | None -> assert false
                in

                ignore (Format.flush_str_formatter ());
                let v = Pretty.print_term Format.str_formatter generic_region_term
                        |> Format.flush_str_formatter
                        |> Format.sprintf "%s.%s" reg_name
                        |> Var.of_string
                in
                ensure_variable cfg v real_term;
                let accessor = match pfield.rs_field with
                  | Some s -> s
                  | None -> assert false
                in
                { local_ty with local_vars = Term.Mterm.add real_term v local_ty.local_vars }, (accessor, real_term) :: acc
              ) (local_ty, []) subv
          in
          { local_ty with region_ident = Ity.Mreg.add reg proj_list local_ty.region_ident }
        end
      | Ity.Ityapp(_), _ ->
        Format.eprintf "Let's check that ";
        Ity.print_ity Format.err_formatter variable_type;
        Format.eprintf " has only non mutable fields.";
        let subv = get_subvalues logical_term None in
        let local_ty = List.fold_left (fun local_ty (t, _) ->
            ignore (Format.flush_str_formatter ());
            let v = Pretty.print_term Format.str_formatter t
                    |> Format.flush_str_formatter
                    |> Var.of_string
            in
            ensure_variable cfg v t;
            { local_ty with local_vars = Term.Mterm.add t v local_ty.local_vars }) local_ty subv
        in
        local_ty
      | _ ->
        (* We can safely give up on a, as no integer variable can descend from it (because it is well typed) *)
        Format.eprintf "Variable could not be added properly: ";
        Pretty.print_term Format.err_formatter logical_term;
        Format.eprintf " of type ";
        Ity.print_ity Format.err_formatter variable_type;
        Format.eprintf "@.";
        local_ty
    in local_ty

  let add_variable cfg local_ty pv =
    add_typed_variable cfg local_ty pv Ity.(pv.pv_ity)

  let create_postcondition cfg local_ty psym =
    if not Ity.(ity_equal  psym.pv_ity ity_unit) then
      begin
        let ty = Term.(Ity.(psym.pv_vs.vs_ty) ) in

        let vreturn = create_vreturn ty in
        let postcondition = Term.( t_eps_close vreturn (
            t_app ps_equ [t_var Ity.(psym.pv_vs);(t_var vreturn)] None)) in

        Format.eprintf "--> Postcondition for let: ";
        Pretty.print_term Format.err_formatter postcondition;
        Format.eprintf "@.";
        (linear_expressions_from_term cfg local_ty) postcondition
      end
    else
      let () = Format.eprintf "no Postocndition:@." in
      (fun abs -> abs), []



  (* Adds expr to the cfg. local_ty is the types of the locally defined variable
   * (useful for references, when we need to get the type of a term in a logical formula).
   *
   * Adds multiple node and edges if expr requires so.
   *
   * returns a tuple, whose first element is the entry point of expr in the cfg, and the second
   * one is the ending point. The result of expr is stored is the variable "result"
   * (see var_return) *)
  let rec put_expr_in_cfg cfg local_ty expr =
    let open Expr in
    match expr.e_node with
    | Epure (t) ->
      let i, j = new_node_cfg cfg expr, new_node_cfg cfg expr in
      let vreturn = create_vreturn (t_type t) in
      let postcondition = t_eps_close vreturn (t_app ps_equ [t_var vreturn; t] None) in
      let constraints, _ = linear_expressions_from_term cfg local_ty postcondition in
      new_hedge_cfg cfg (i, j) (fun man abs ->
          constraints abs);
      i, j, []

    | Elet(LDvar(psym, let_expr), b) ->
      (* As it may not be an int, the type could be useful, so we can save it *)
      let variable_type = Expr.(let_expr.e_ity) in

          (*
           * let a = b in c
           *
           *  . let_begin_cp
           *  | result = b
           *  . let_end_cp
           *  | a = result
           *  . b_begin_cp
           *  | …
           *  | result = c
           *  . b_begin_cp
           *  | erase every temporary variable
           *  . end_cp
           **)
      let let_begin_cp, let_end_cp, let_exn = put_expr_in_cfg cfg local_ty let_expr in

      let local_ty = add_typed_variable cfg local_ty psym variable_type in

      let constraints, to_forget =
        create_postcondition cfg local_ty psym
      in

      (* compute the child and add an hyperedge, to set the value of psym
       * to the value returned by let_expr *)
      let b_begin_cp, b_end_cp, b_exn = put_expr_in_cfg cfg local_ty b in


      (* Save the effect of the let *)
      new_hedge_cfg cfg (let_end_cp, b_begin_cp) (fun man abs ->
          let to_forget = Array.of_list to_forget in
          Abstract1.forget_array man (constraints abs) to_forget false
        );
      let end_cp = new_node_cfg cfg expr in
      (* erase a *)
      let var_term = match Expr.term_of_expr ~prop:false (Expr.e_var psym) with
        | Some s -> s
        | None -> assert false
      in
      let vars_to_forget =
        get_subvalues var_term None
        |> List.map (fun (a, _) -> Term.Mterm.find a local_ty.local_vars)
        |> Array.of_list
      in
      new_hedge_cfg cfg (b_end_cp, end_cp) (fun man abs ->
          Abstract1.forget_array man abs vars_to_forget false
        );


      let_begin_cp, end_cp, let_exn @ b_exn
    | Evar(psym) ->
      let constraints, _ =
        if not Ity.(ity_equal  psym.pv_ity ity_unit) then
          begin
          let ty = Term.(Ity.(psym.pv_vs.vs_ty) ) in

          let vreturn = create_vreturn ty in
          let postcondition = Term.( t_eps_close vreturn (
              t_app ps_equ [t_var Ity.(psym.pv_vs);(t_var vreturn)] None)) in

          Format.eprintf "--> Postcondition for let: ";
          Pretty.print_term Format.err_formatter postcondition;
          Format.eprintf "@.";
          (linear_expressions_from_term cfg local_ty) postcondition
          end
        else
          let () = Format.eprintf "no Postocndition:@." in
          (fun abs -> abs), []
      in

      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
          constraints abs
        );
      begin_cp, end_cp, []
    | Econst(n) ->
      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in

      let vreturn = create_vreturn Ty.ty_int in
      let postcondition = t_eps_close vreturn (t_app ps_equ [t_const n; t_var vreturn] None) in
      let constraints, _ = linear_expressions_from_term cfg local_ty postcondition in

      new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
          constraints abs
        );
      begin_cp, end_cp, []
    | Eexec({c_node = Capp(rsym, args); _}, { Ity.cty_post = post; Ity.cty_result = ity; Ity.cty_effect = effect;  _ }) ->
      let eff_write = Ity.(effect.eff_writes) in

      (* Computing domain from postcondition *)
      Format.eprintf "Computing domain from postconditions for function: ";
      Expr.print_rs Format.err_formatter rsym;
      List.iter (fun a ->
          Format.eprintf "    ###>  ";
          Pretty.print_term Format.err_formatter a;
          Format.eprintf "@.";
        ) post;

      Format.eprintf "@.";
      let constraints =
        List.map (linear_expressions_from_term cfg local_ty) post
        |> List.fold_left (fun f (a, _) ->
            (fun d -> f (a d))) (fun x -> x)
      in
      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in

      new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
          (* effects *)
          let abs = ref abs in
          (* FIXME: bad, does not work with sub records *)
          ignore @@ Ity.Mreg.mapi (fun a b ->
              Ity.Mpv.mapi (fun c () ->
                  let open Ity in
                  let var = Ity.Mreg.find a local_ty.region_ident in
                  let _, t =
                    try List.find (fun (p, _) ->
                      Ity.pv_equal p c) var
                    with
                    | Not_found ->
                      Format.eprintf "Couldn't find projection for field ";
                      Ity.print_pv Format.err_formatter c;
                      Format.eprintf "@.";
                      Format.eprintf "(known fields: ";
                      List.iter (fun (p, _) ->
                          Ity.print_pv Format.err_formatter p;
                          Format.eprintf " @.";
                        ) var;
                      Format.eprintf ")@.";
                      assert false
                  in
                  Pretty.print_term Format.err_formatter t;
                  let v = Term.Mterm.find t local_ty.local_vars in
                  Format.eprintf "%s@." (Var.to_string v);
                  abs :=  Abstract1.forget_array man !abs [|v|] false;
                ) b;
            ) eff_write;

          constraints !abs
        );
      (* FIXME: handle exceptions *)
      begin_cp, end_cp, []
    | Ewhile(cond, inv, var, content) ->
      let open Expr in
      (* Condition expression *)
      let cond_term = 
        match Expr.term_of_expr ~prop:false cond with
        | Some s ->
          s
        | None ->
          Format.eprintf "warning, condition in while could not be translated to term, an imprecise invariant will be generated";
          Term.t_true
      in
      let constraints, _ = linear_expressions_from_term cfg local_ty cond_term in

      let before_loop_cp = new_node_cfg cfg cond in
      let start_loop_cp, end_loop_cp, loop_exn = put_expr_in_cfg cfg local_ty content in
      cfg.loop_invariants <- (expr, before_loop_cp) :: cfg.loop_invariants;
      let after_loop_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (before_loop_cp, start_loop_cp) (fun man abs ->
          constraints abs
        );
      new_hedge_cfg cfg (before_loop_cp, after_loop_cp) (fun man abs ->
          (* todo *)
          abs
        );
      new_hedge_cfg cfg (end_loop_cp, before_loop_cp) (fun man abs ->
          abs
        );
      (* FIXME: exceptions while inside the condition *)
      before_loop_cp, after_loop_cp, loop_exn
    | Etry(e, exc) ->
      let additional_exn = ref [] in
      let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg local_ty e in
      let i = new_node_cfg cfg expr in
      let exc = Ity.Mexn.map (fun (l, e) ->

          let local_ty = List.fold_left (fun local_ty p ->
              add_typed_variable cfg local_ty p Ity.(p.pv_ity)) local_ty l in

          let before_assign_cp = new_node_cfg cfg e in

          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg local_ty e in

          additional_exn := e_exn @ !additional_exn;

          begin
            match l with
            | [p] ->
              let constraints, to_forget = create_postcondition cfg local_ty p in
              new_hedge_cfg cfg (before_assign_cp, e_begin_cp) (fun man abs -> constraints abs);
              new_hedge_cfg cfg (e_end_cp, i) (fun man abs -> Abstract1.forget_array manpk abs (Array.of_list to_forget) false);
            | _ -> Format.eprintf "Multiple constructors exception, not handled by AI.";
              new_hedge_cfg cfg (before_assign_cp, e_begin_cp) (fun man abs -> abs);
              new_hedge_cfg cfg (e_end_cp, i) (fun man abs -> abs);
          end;
          l, before_assign_cp, e_end_cp
          ) exc in
      
      let e_exn = Ity.Mexn.fold (fun exc_sym (l, cp_begin, _) e_exn ->
          List.filter (fun (cp, exc_sym_) ->
              if Ity.xs_equal exc_sym exc_sym_ then
                begin
                  new_hedge_cfg cfg (cp, cp_begin) (fun man abs ->
                       abs
                    );
                  false
                end
              else
                true
            ) e_exn) exc e_exn in
      new_hedge_cfg cfg (e_end_cp, i) (fun man abs ->
          abs
        );
      e_begin_cp, i, !additional_exn @ e_exn
    | Eraise(s, e) ->
      let arg_begin, arg_end_cp, arg_exn = put_expr_in_cfg cfg local_ty e in
      let j = new_node_cfg cfg expr in
      let k = new_node_cfg cfg expr in
      new_hedge_cfg cfg (j, k) (fun man abs ->
          Abstract1.bottom man cfg.env);
      arg_begin, k, [(arg_end_cp, s)]

    | Eif(cond, b, c) ->
      let open Expr in
      (* Condition expression *)
      let cond_term = 
        match Expr.term_of_expr ~prop:true cond with
        | Some s ->
          s
        | None ->
          Format.eprintf "warning, condition in if could not be translated to term (not pure), an imprecise invariant will be generated (migth even be wrong if there are exceptions)";
          Term.t_true
      in
      let constraints, _ = linear_expressions_from_term cfg local_ty cond_term in
      let constraints_not, _ = linear_expressions_from_term cfg local_ty (t_not cond_term) in
      let b_begin_cp, b_end_cp, b_exn = put_expr_in_cfg cfg local_ty b in
      let c_begin_cp, c_end_cp, c_exn = put_expr_in_cfg cfg local_ty c in
      let start_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (start_cp, b_begin_cp) (fun man abs ->
          constraints abs);
      new_hedge_cfg cfg (start_cp, c_begin_cp) (fun man abs ->
          constraints_not abs);
      new_hedge_cfg cfg (c_end_cp, end_cp) (fun man abs ->
          abs);
      new_hedge_cfg cfg (b_end_cp, end_cp) (fun man abs ->
          abs);
      start_cp, end_cp, b_exn @ c_exn
    | Ecase(case_e, l) ->
      let case_e_begin_cp, case_e_end_cp, case_e_exn = put_expr_in_cfg cfg local_ty case_e in
      let e_exns = ref [case_e_exn] in
      let case_end_cp = new_node_cfg cfg expr in
      List.iter (fun (p, e) ->
          let open Term in
          let open Expr in
          let local_ty = ref local_ty in
          let constraints, to_forget = match p.pp_pat.pat_node with
            | Pwild -> (fun abs -> abs), []
            | Pvar(vsym) -> failwith "pattern"
            | Papp(l, p) ->
              let args = List.map (fun p -> match p.pat_node with
                  | Pvar(vsym) ->
                    let pv = Ity.restore_pv vsym in
                    local_ty := add_typed_variable cfg !local_ty pv Ity.(pv.pv_ity);
                    t_var vsym
                  | _ -> failwith "nested pattern or worse"
                ) p in
              let matched_term = t_app l args (Some (Ity.ty_of_ity (case_e.e_ity))) in
              let vreturn = create_vreturn (t_type matched_term) in
              let postcondition =
                t_eps_close vreturn (
                  t_app ps_equ [matched_term; t_var vreturn] None) in
              linear_expressions_from_term cfg !local_ty postcondition

            | Por(a, b) -> failwith "pattern or"
            | Pas(a, b) -> failwith "pattern as"
          in
          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg !local_ty e in
          new_hedge_cfg cfg (case_e_end_cp, e_begin_cp) (fun man abs ->
              Abstract1.forget_array man (constraints abs) (Array.of_list to_forget) false
            );
          new_hedge_cfg cfg (e_end_cp, case_end_cp) (fun man abs -> abs);
          e_exns := e_exn :: !e_exns;
        ) l;
      case_e_begin_cp, case_end_cp, (List.concat !e_exns)
    | Eassert(_) | Eabsurd -> (* FIXME: maybe they could be taken into account *)
      let i = new_node_cfg cfg expr in

      i, i, []

    | Eghost(e) -> put_expr_in_cfg cfg local_ty e

    | Efor(k, (lo, dir, up), _, e) ->
      (* . before_loop
       * | k = 0      k = n -> forget_k
       * . start_loop ------------------> end_loop
       * | 0 <= k <= n 
       * . e_begin
       * :
       * :       k = k + 1
       * . e_end --------> start_loop
       *)
      let k_term, lo, up =
        match Expr.term_of_expr ~prop:false (Expr.e_var k),
              Expr.term_of_expr ~prop:false (Expr.e_var lo),
              Expr.term_of_expr ~prop:false (Expr.e_var up) with
        | Some s, Some u, Some v -> s, u, v
        | _ -> assert false
      in
      let local_ty = add_variable cfg local_ty k in
      let k_var = Mterm.find k_term local_ty.local_vars in

      let before_loop_cp = new_node_cfg cfg expr in
      let start_loop_cp = new_node_cfg cfg expr in
      let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg local_ty e in
      let end_loop_cp = new_node_cfg cfg expr in

      let postcondition_before = t_app ps_equ [k_term; lo] None in
      let constraints_start, _ = linear_expressions_from_term cfg local_ty postcondition_before in

      let precondition_e =
        if dir = Expr.To then
          t_and (t_app le_int [lo; k_term] None) (t_app le_int [k_term; up] None)
        else
          t_and (t_app le_int [up; k_term] None) (t_app le_int [k_term; lo] None)
      in
      let constraints_e, _ = linear_expressions_from_term cfg local_ty precondition_e in

      let postcondition =
          t_app ps_equ [k_term; up] None
      in
      let constraints_post, _ = linear_expressions_from_term cfg local_ty postcondition in

      new_hedge_cfg cfg (before_loop_cp, start_loop_cp) (fun man -> constraints_start);
      new_hedge_cfg cfg (start_loop_cp, e_begin_cp) (fun man -> constraints_e);
      new_hedge_cfg cfg (e_end_cp, start_loop_cp) (fun man abs ->
          (* k = k + 1 *)
          let expr = Linexpr1.make cfg.env in
          Linexpr1.set_array expr [|Coeff.s_of_int 1,  k_var|] (Some (Coeff.s_of_int 1));
          Abstract1.assign_linexpr man abs k_var expr None
        );
      new_hedge_cfg cfg (start_loop_cp, end_loop_cp) (fun man abs ->
          let abs = constraints_post abs in
          Abstract1.forget_array man abs [|k_var|] false);
      cfg.loop_invariants <- (expr, start_loop_cp) :: cfg.loop_invariants;
      before_loop_cp, end_loop_cp, e_exn

    | _ ->
      Format.eprintf "expression not handled";
      Expr.print_expr Format.err_formatter expr;
      begin
      match expr.e_loc with
      | None -> ()
      | Some l -> Loc.report_position Format.err_formatter l;
      end;
      let i = new_node_cfg cfg expr in
      i, i, []

  let put_expr_with_pre cfg local_ty e pre =
    let i = new_node_cfg cfg e in
    let e_start_cp, e_end_cp, e_exn = put_expr_in_cfg cfg local_ty e in
    let constraints, _ = linear_expressions_from_term cfg local_ty (t_and_l pre) in
    new_hedge_cfg cfg (i, e_start_cp) (fun man -> constraints);
    i, e_end_cp, e_exn

  module Apron_to_term = Apron_to_term.Apron_to_term (E)
  let domain_to_term cfg domain =
    Apron_to_term.domain_to_term manpk domain (fun a ->
        try
          Hashtbl.find cfg.variable_mapping a
        with 
        | Not_found ->
          Format.eprintf "Couldn't find variable %s@." (Var.to_string a);
          raise Not_found
      )


  let vertex_dummy = -1
  (** dummy value *)
  let hedge_dummy= -1
  (** dummy value *)


  (** {2 The fixpoint manager } *)

  let dot_file = open_out "t.dot";;
  let dot_fmt = Format.formatter_of_out_channel dot_file;;

  let get_fixpoint_man cfg man =
    let (manager:(int,int,'a Abstract1.t,unit) Fixpoint.manager) = {
      Fixpoint.bottom = begin fun vertex -> Abstract1.bottom man cfg.env end;
      Fixpoint.canonical = begin fun vertex abs -> Abstract1.canonicalize man abs end;
      Fixpoint.is_bottom = begin fun vertex abs -> Abstract1.is_bottom man abs end;
      Fixpoint.is_leq = begin fun vertex abs1 abs2 -> Abstract1.is_leq man abs1 abs2 end;
      Fixpoint.join = begin fun vertex abs1 abs2 -> Abstract1.join man abs1 abs2 end;
      Fixpoint.join_list = begin fun vertex labs -> Abstract1.join_array man (Array.of_list labs) end;
      Fixpoint.widening = begin fun vertex abs1 abs2 -> Abstract1.widening man abs1 abs2 end;
      Fixpoint.odiff = None;
      Fixpoint.apply = cfg.apply man;
      Fixpoint.arc_init = begin fun hedge -> () end;
      Fixpoint.abstract_init=
        begin fun vertex ->
          if vertex=0 then Abstract1.top man cfg.env else Abstract1.bottom man cfg.env
        end;

      Fixpoint.print_abstract = Abstract1.print;
      Fixpoint.print_arc = (fun fmt () -> pp_print_string fmt "()");
      Fixpoint.print_vertex = pp_print_int;
      Fixpoint.print_hedge = pp_print_int;

      Fixpoint.accumulate = false;
      Fixpoint.print_fmt = Format.std_formatter;
      Fixpoint.print_analysis = false;
      Fixpoint.print_component = false;
      Fixpoint.print_step = false;
      Fixpoint.print_state = false;
      Fixpoint.print_postpre = false;
      Fixpoint.print_workingsets = false;

      Fixpoint.dot_fmt = Some dot_fmt;
      Fixpoint.dot_vertex = (fun fmt v -> Format.fprintf fmt "v%i" v);
      Fixpoint.dot_hedge = (fun fmt h -> Format.fprintf fmt "h%i" h);
      Fixpoint.dot_attrvertex = (fun _ -> Format.printf "%d");
      Fixpoint.dot_attrhedge = (fun _ -> Format.printf "%d");
    }
    in manager
  
  
  let eval_fixpoints cfg =
    try
      begin
        let manager = get_fixpoint_man cfg manpk in
        let compare_no_closured = PSHGraph.stdcompare.PSHGraph.comparev in
        let sinit = PSette.singleton compare_no_closured 0 in
        let make_strategy =
          fun is_active ->
            Fixpoint.make_strategy_default
              ~widening_start:30 ~widening_descend:1
              ~priority:(PSHGraph.Filter is_active)
              ~vertex_dummy ~hedge_dummy
              cfg.g sinit
        in
        let output = Fixpoint.analysis_guided
            manager cfg.g sinit make_strategy
        in
        (*printf "output=%a@." (Fixpoint.print_output manager) output;*)
        let l = ref [] in
        PSHGraph.iter_vertex output
          (fun vtx abs ~pred ~succ ->
             l := (vtx, abs) :: !l);

        let l = List.sort (fun (i, _) (j, _) -> compare i j) !l in
        List.iter (fun (vtx, abs) ->
            printf "acc(%i) = %a@."
              vtx (Abstract1.print) abs;
            let gen = Abstract1.to_generator_array manpk abs in
            Generator1.array_print Format.std_formatter gen;
            let n = Generator1.array_length gen in
            for i = 0 to n - 1 do
              let linexpr = Generator1.array_get  gen i |> Generator1.get_linexpr1 in
              Linexpr1.print Format.std_formatter linexpr;
              Format.printf " = ";
              Coeff.print Format.std_formatter (Linexpr1.get_cst linexpr);
              Format.printf "@.";
            done;
            Format.printf "@.";
          ) l;

        let l = ref [] in
        Hashtbl.iter (fun a b ->
            l := (a, b) :: !l;
          )cfg.expr_to_control_point;
        let l = List.sort (fun (_, i) (_, j) -> compare i j) !l in
        List.iter (fun (a, b) ->

            Format.eprintf "%d -> " b;
            Expr.print_expr Format.err_formatter a;
            Format.eprintf "@."
          ) l;

        (* Print loop invariants *)

        Format.printf "Loop invariants:\n@.";

        List.iter (fun (expr, cp) ->
            Format.printf "For:@.";
            Expr.print_expr Format.std_formatter expr;
            Format.printf "@.";
            let abs = PSHGraph.attrvertex output cp in
            Format.printf "%a@." Abstract1.print abs;
            Pretty.forget_all ();
            Pretty.print_term Format.std_formatter (domain_to_term cfg abs);
            printf "@."
          ) cfg.loop_invariants;

        List.map (fun (expr, cp) ->
            let abs = PSHGraph.attrvertex output cp in
            expr, abs
          ) cfg.loop_invariants
      end
    with Manager.Error(exc) ->
      Manager.print_exclog Format.err_formatter exc;
      raise (Manager.Error (exc))

end
