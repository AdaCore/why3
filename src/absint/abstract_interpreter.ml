
open Format
open Apron

(* Copied from inlining, it looks like it is difficult to use the code from there
 * without messing up the interface. *)

type env = {
  known : Decl.known_map;
  funenv : Decl.logic_decl Term.Mls.t;
}

exception Recursive_logical_definition

let hc = Hashtbl.create 100

let get_proj = Hashtbl.find hc

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

let extract_fields known_map variable_type = 
  let open Ity in
  match Ity.(variable_type.ity_node) with
  | Ity.Ityvar(_) -> []
  | Ity.Ityreg({reg_args = a; reg_regs = b; reg_name = n; reg_its = its }) ->
    begin
      match its with
      | { its_mfields = fldl; _ } ->
        let open Term in
        let open Ident in
        let open Expr in
        let open Ity in
        let my_fields = Pdecl.((find_its_defn known_map its).itd_fields) in
        let fields = List.combine fldl my_fields in
        List.map (fun (p, r) ->
            try
              Hashtbl.find hc p
            with
            | Not_found ->
                Expr.print_rs Format.err_formatter r;
                let res = p, r, r.rs_cty.cty_result in
                Hashtbl.add hc p res;
                res) fields
    end
  | Ity.Ityapp(its, a, b) -> []

module Abstract_interpreter(E: sig
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct

  let known_logical_ident = Pmodule.(Theory.(E.pmod.mod_theory.th_known))
  let known_pdecl = Pmodule.(Theory.(E.pmod.mod_known))

  (* General purpose inlining stuff *)

  let t_unfold loc fs tl ty =
    let open Term in
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
    let open Term in
    let t = t_map t_replace_all t in
    match t.t_node with
    | Tapp (fs,tl) ->
      t_label_copy t (t_unfold t.t_loc fs tl t.t_ty)
    | _ -> t


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
  let var_return = Var.of_string "$$result"

  (* Initialize an hedge *)

  let vs_to_var vs =
    ignore (Format.flush_str_formatter ());
    Pretty.print_vs Format.str_formatter vs;
    Var.of_string (Format.flush_str_formatter ())

  let pv_to_var psym =
    vs_to_var Ity.(psym.pv_vs)

  let ensure_variable cfg v t =
    if not (Environment.mem_var cfg.env v) then
      begin
        Hashtbl.add cfg.variable_mapping v t;
        cfg.env <- Environment.add cfg.env [|v|] [||]
      end
  
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
    ensure_variable cfg var_return (Term.t_var (Term.create_vsymbol {pre_name = "result"; pre_label = Expr.(Ident.(rs.rs_name.id_label)); pre_loc = None } Ty.ty_int));
    cfg

  let add_variable cfg psym =
    if Ity.(ity_equal ity_int psym.pv_ity) then
      begin
        let var = pv_to_var psym in
        ensure_variable cfg var (Term.t_var Ity.(psym.pv_vs));
      end

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

  let th_int = Env.read_theory E.env ["int"] "Int"
  let le_int = Theory.(ns_find_ls th_int.th_export ["infix <="])
  let ge_int = Theory.(ns_find_ls th_int.th_export ["infix >="])
  let lt_int = Theory.(ns_find_ls th_int.th_export ["infix <"])
  let gt_int = Theory.(ns_find_ls th_int.th_export ["infix >"])
  let ad_int = Theory.(ns_find_ls th_int.th_export ["infix +"])
  let min_int = Theory.(ns_find_ls th_int.th_export ["infix -"])
  let min_u_int = Theory.(ns_find_ls th_int.th_export ["prefix -"])
  let mult_int = Theory.(ns_find_ls th_int.th_export ["infix *"])

  type logic_path = int list
  type logic_value =
    | VTree of (logic_value list * Ty.ty)
    | VNode of int * (Var.t * int) list
    | VVar of Term.vsymbol * Ty.ty * logic_path * Term.term

  let ty_from_tree = function
    | VTree(_, t) -> t
    | VNode(_) -> Ty.ty_int
    | VVar(_, t, _, _) -> t

  let logic_path_to_var cfg vsym logic_path =
    let _ = Format.flush_str_formatter () in
    let v =
      Pretty.print_vs Format.str_formatter vsym
      |> Format.flush_str_formatter
      |> Format.sprintf "%s|%s" (List.map string_of_int logic_path |> String.concat "|")
      |> Var.of_string
    in
    ensure_variable cfg v Term.t_true;
    v

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

  open Term

  let access_field a i (proj, t) =
    match proj with
    | None -> Format.eprintf "complex field access@."; raise Not_found
    | Some s ->
      match a.t_node with
      | Tapp(func, args) when func.ls_constr = 1 ->
        List.nth args i
      | Tvar(_) | _ ->
        t_app s [a] (Some t)

  let access_fields a b i (proj, t) =
    access_field a i (proj, t), access_field b i (proj, t)

  (* Get a set of (apron) linear expressions from a constraint stated in why3 logic.
   * ATM it only works for conjunction, and if there is not that much uninterpreted function.
   * In the worst case, it returns an empty list.
   *
   * The resulting list of linear expressions is weaker than the original why3
   * formula. *)
  let linear_expressions_from_term: cfg -> local_ty -> Term.term -> ((domain -> domain) * Var.t list)  = fun cfg local_ty t ->
    let open Term in

    (* First inline everything, for instance needed for references
     * where !i is (!) i *)
    let t = t_replace_all t in
    let return_var = ref None in

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
        let var =
          match !return_var with
          | Some s when Term.vs_equal a s -> var_return
          | _ -> vs_to_var a
        in
        ([(var, coeff)], 0)
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
      | Tapp(func, [{t_node = Tconst(Number.ConstInt(n)); _}; a]) when Term.ls_equal func mult_int ->
        let n = Number.compute_int n in
        term_to_var_list ((BigInt.to_int n) * coeff) a
      (* FIXME: need a nice domain for algebraic types *)
      | Tapp(func, [arg]) when Term.(func.ls_constr = 0) -> (* maybe a record access *)
        begin
          match var_of_term t with
          | None -> raise (Not_handled t)
          | Some s ->
            ([s, coeff], 0)
        end
      | _ ->
        raise (Not_handled t)
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
        | Tapp(func, [a; b]) when Ty.ty_equal (t_type a) Ty.ty_int
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
            (* FIXME: is the order of the type guaranteed ? *)
            let child_types =  
              ty_fold (fun l a ->
                  a::l
                ) [] (Term.t_type a) in
            (* the only case handled ATM is types with a single constructor *)
            match (Term.t_type a).ty_node with
            | Tyapp(tys, _) -> 
              begin
                match (Ident.Mid.find tys.ts_name known_logical_ident).Decl.d_node with
                | Decl.Ddata([_, [ls, ls_projs]]) ->
                  List.combine ls_projs child_types
                  |> List.mapi (access_fields a b)
                  |> List.fold_left (fun f (a, b) ->
                      let g = aux (t_app ps_equ [a; b] None) in
                      (fun abs ->
                         f (g (abs)))) (fun abs -> abs)
                | _->
                  Format.eprintf "type equality not fully recognized: ";
                  Pretty.print_term Format.err_formatter t;
                  Format.eprintf "@."; fun abs -> abs
              end
            | Tyvar(_) -> raise (Not_handled t)
          end
        | Tif(a, b, c) ->
          let fa = aux a in
          let fb = aux b in
          let fc = aux c in
          (fun d ->
             let d1 = fb (fa d) in
             let d2 = fc d in
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
        let myty = Term.(return.vs_ty) in
        let child_types =  
          ty_fold (fun l a ->
              a::l
            ) [] myty in
        let l =
          match myty.ty_node with
          | _ when Ty.ty_equal myty ty_int ->
            let v = var_return in
            ensure_variable cfg v Term.t_bool_true;
            to_forget := v :: !to_forget;
            { !local_ty with local_vars = Term.Mterm.add t v (!local_ty).local_vars }
          | Tyapp(tys, _) -> 
            begin
              match (Ident.Mid.find tys.ts_name known_logical_ident).Decl.d_node with
              | Decl.Ddata([_, [ls, ls_projs]]) ->
                List.combine ls_projs child_types
                |> List.mapi (access_field (Term.t_var return))
                |> List.combine ls_projs
                |> List.fold_left (fun local_ty (Some l, a) ->

                    ignore (Format.flush_str_formatter ());
                    let v = Pretty.print_ls Format.str_formatter l
                            |> Format.flush_str_formatter
                            |> Format.sprintf "%s.%s" "$$result"
                            |> Var.of_string
                    in
                    to_forget := v :: !to_forget;
                    ensure_variable cfg v a;
                    { local_ty with local_vars = Term.Mterm.add a v local_ty.local_vars }
                  ) !local_ty
              | _->
                Format.eprintf "type equality not fully recognized: ";
                Pretty.print_term Format.err_formatter t;
                Format.eprintf "@."; !local_ty
            end
          | _ -> raise (Not_handled t)
        in
        local_ty := l;
        return_var := Some return;
        aux t, !to_forget
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
    let child_types =  
      ty_fold (fun l a ->
          a::l
        ) [] (Term.t_type logical_term) in
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
      | _ when Ity.ity_equal variable_type Ity.ity_unit
        -> local_ty
      | Ity.Ityreg(reg), Tyapp(tys, _) -> 
        begin
          let reg_name = 
            Ity.print_reg_name Format.str_formatter reg
            |> Format.flush_str_formatter
          in
          let local_ty, proj_list =
            match (Ident.Mid.find tys.ts_name known_logical_ident).Decl.d_node
            with
            | Decl.Ddata([_, [ls, ls_projs]]) ->
              let pfields = 
                Pdecl.((find_its_defn known_pdecl reg.reg_its).itd_fields) in
              List.combine ls_projs child_types
              |> List.mapi (access_field logical_term)
              |> List.combine ls_projs
              |> List.combine pfields
              |> List.fold_left (fun (local_ty, acc) (pfield, (Some l, a)) ->

                  ignore (Format.flush_str_formatter ());
                  let v = Pretty.print_ls Format.str_formatter l
                          |> Format.flush_str_formatter
                          |> Format.sprintf "%s.%s" reg_name
                          |> Var.of_string
                  in
                  ensure_variable cfg v a;
                  let accessor = match pfield.rs_field with
                    | Some s -> s
                    | None -> assert false
                  in
                  { local_ty with local_vars = Term.Mterm.add a v local_ty.local_vars }, (accessor, a) :: acc
                ) (local_ty, [])
            | _->
              Format.eprintf "type equality not fully recognized: ";
              Pretty.print_term Format.err_formatter logical_term;
              Format.eprintf "@."; local_ty, []
          in
          { local_ty with region_ident = Ity.Mreg.add reg proj_list local_ty.region_ident }
        end
      | _ ->
        Format.eprintf "Variable could not be added properly: ";
        Pretty.print_term Format.err_formatter logical_term;
        Format.eprintf "@.";
        raise (Not_handled logical_term)
    in local_ty


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
        if not Ity.(ity_equal  psym.pv_ity ity_unit) then
          begin
          let ty = Term.(Ity.(psym.pv_vs.vs_ty) ) in

          let vreturn = Term.create_vsymbol Ident.{pre_name = "return"; pre_label = Ident.Slab.empty; pre_loc = None; }
              ty in
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
      new_hedge_cfg cfg (b_end_cp, end_cp) (fun man abs ->
          match Ity.(variable_type.ity_node) with
          | _ when Ity.(ity_equal variable_type ity_int) ->
            Abstract1.forget_array man abs [|pv_to_var psym|] false
          | _ -> abs
        );


      let_begin_cp, end_cp, let_exn @ b_exn
    | Evar(psym) ->
      if Ity.(ity_equal psym.pv_ity ity_int) then
        begin
          let begin_cp = new_node_cfg cfg expr in
          let end_cp = new_node_cfg cfg expr in
          new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
              let expr = Linexpr1.make cfg.env in
              let p = pv_to_var psym in
              Linexpr1.set_list expr [(one, p)] (Some(zero));
              Abstract1.assign_linexpr man abs var_return expr None
            );
          begin_cp, end_cp, []
        end
      else
        let i = new_node_cfg cfg expr in
        i, i, []
    | Econst(Number.ConstInt(n)) ->
      let coeff =
        Number.compute_int n
        |> BigInt.to_int
        |> Coeff.s_of_int
      in
      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
          let expr = Linexpr1.make cfg.env in
          Linexpr1.set_list expr [] (Some(coeff));
          Abstract1.assign_linexpr man abs var_return expr None
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
          let abs = ref (Abstract1.forget_array man abs [|var_return|] false) in
          (* FIXME: bad, does not work with sub records *)
          ignore @@ Ity.Mreg.mapi (fun a b ->
              Ity.Mpv.mapi (fun c () ->
                  let open Ity in
                  let var = Ity.Mreg.find a local_ty.region_ident in
                  let _, t = List.find (fun (p, _) ->
                      Ity.pv_equal p c) var in
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
          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg local_ty e in
          additional_exn := e_exn @ !additional_exn;
          new_hedge_cfg cfg (e_end_cp, i) (fun man abs -> abs);
          l, e_begin_cp, e_end_cp) exc in
      
      let e_exn = Ity.Mexn.fold (fun exc_sym (l, cp_begin, _) e_exn ->
          List.filter (fun (cp, exc_sym_) ->
              if Ity.xs_equal exc_sym exc_sym_ then
                begin
                  new_hedge_cfg cfg (cp, cp_begin) (fun man abs ->
                      match l with
                      | [t] ->
                        if Ity.(ity_equal t.pv_ity ity_int) then
                          begin
                            let old_arg = var_return in
                            let new_arg = pv_to_var t in
                            let expr = Linexpr1.make cfg.env in
                            Linexpr1.set_list expr [(one, old_arg)] (Some(zero));
                            let abs = Abstract1.assign_linexpr man abs new_arg expr None in
                            Abstract1.forget_array man abs [|old_arg|] false
                          end
                        else abs
                      | _ -> abs
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
      arg_begin, j, [(arg_end_cp, s)]

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
      let b_begin_cp, b_end_cp, b_exn = put_expr_in_cfg cfg local_ty b in
      let c_begin_cp, c_end_cp, c_exn = put_expr_in_cfg cfg local_ty c in
      let start_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (start_cp, b_begin_cp) (fun man abs ->
          constraints abs);
      new_hedge_cfg cfg (start_cp, c_begin_cp) (fun man abs ->
          (* todo *)
          abs);
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
          begin
              match p.pp_pat.pat_node with
              | Pwild -> ()
              | Pvar(vsym) -> failwith "pattern"
              | Papp(l, p) -> Pretty.print_ls Format.err_formatter l; failwith "pattern app"
              | Por(a, b) -> failwith "pattern or"
              | Pas(a, b) -> failwith "pattern as"
          end;
          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg local_ty e in
          new_hedge_cfg cfg (case_e_end_cp, e_begin_cp) (fun man abs ->
              (* we need to add the new variables declared in the case pattern *)
              match p.pp_pat.pat_node with
              | Pwild -> abs
              | Pvar(vsym) -> failwith "pattern"
              | Papp(l, p) -> failwith "pattern app"
              | Por(a, b) -> failwith "pattern or"
              | Pas(a, b) -> failwith "pattern as"
              );
          new_hedge_cfg cfg (e_end_cp, case_end_cp) (fun man abs -> abs);
          e_exns := e_exn :: !e_exns;
        ) l;
      case_e_begin_cp, case_end_cp, (List.concat !e_exns)
    | Eassert(_) | Eabsurd -> (* FIXME: maybe they could be taken into account *)
      let i = new_node_cfg cfg expr in

      i, i, []
    | _ ->
      Expr.print_expr Format.err_formatter expr;
      Format.eprintf "@.";
      Format.eprintf "unhandled expr@.";

      let i = new_node_cfg cfg expr in

      i, i, []

  let get_domain cfg control_point = ()

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
              ~widening_start:1 ~widening_descend:2
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
              vtx (Abstract1.print) abs
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
