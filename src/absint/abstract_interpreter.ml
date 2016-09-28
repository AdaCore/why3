
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
  | _ -> raise Not_found

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

  let known_logical_ident = Pmodule.(Theory.(E.pmod.mod_theory.th_known))

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
        let vsym, new_term = Decl.open_ls_defn e in
        let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
        let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vsym tl in
        let mt = oty_match mt (Some (t_type new_term)) ty in
        t_ty_subst mt mv new_term

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

  type domain = unit

  type cfg = {
    (* not one to one *)
    expr_to_control_point: (Expr.expr, control_point) Hashtbl.t;
    g:(int,int,unit,unit,unit) PSHGraph.t;
    mutable control_point_count: int;
    mutable hedge_count: int;
    mutable env: Environment.t;
    mutable apply: apron_domain Apron.Manager.t -> int -> apron_domain Apron.Abstract1.t array -> unit * apron_domain Apron.Abstract1.t
  }

  exception Unknown_hedge

  (* Some useful constants to express return values and linear expressions *)
  let zero = Coeff.Scalar (Scalar.of_int 0) 
  let one = Coeff.Scalar (Scalar.of_int 1)
  let neg_one = Coeff.Scalar (Scalar.of_int (-1))
  let var_return = Var.of_string "result"

  (* Initialize an hedge *)
  let start_cfg rs =
    { expr_to_control_point = Hashtbl.create 100;
      control_point_count = 0;
      hedge_count = 0;
      g = PSHGraph.create PSHGraph.stdcompare 3 ();
      apply = (fun _ _ a -> raise Unknown_hedge);
      env = Environment.make [|var_return|] [||]; }

  let vs_to_var vs =
    ignore (Format.flush_str_formatter ());
    Pretty.print_vs Format.str_formatter vs;
    Var.of_string (Format.flush_str_formatter ())

  let pv_to_var psym =
    vs_to_var Ity.(psym.pv_vs)

  let add_variable cfg psym =
    if Ity.(ity_equal ity_int psym.pv_ity) then
      begin
        let var = pv_to_var psym in
        cfg.env <- Environment.add cfg.env [|var|] [||]
      end

  let new_node_cfg cfg expr =
    let i = cfg.control_point_count in
    Hashtbl.add cfg.expr_to_control_point expr i;
    cfg.control_point_count <- i + 1;
    (* save in the cfg *)
    PSHGraph.add_vertex cfg.g i ();
    i

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

  let unepsilon_term var_string = 7

  exception Not_handled of Term.term

  let th_int = Env.read_theory E.env ["int"] "Int"
  let le_int = Theory.(ns_find_ls th_int.th_export ["infix <="])
  let lt_int = Theory.(ns_find_ls th_int.th_export ["infix <"])
  let ad_int = Theory.(ns_find_ls th_int.th_export ["infix +"])

  let linear_expressions_from_term cfg t =
    let open Term in

    let t = t_replace_all t in

    match t.t_node with
    | Teps(tb) ->
      let return, t = Term.t_open_bound tb in

      let rec term_to_int coeff cst constr t = match t.t_node with
        | Tvar(a) ->
          begin
            let var =
              if Term.vs_equal a return then
                var_return
              else vs_to_var a in
            try
              let c = List.assoc var !constr in
              constr := (var, c+coeff) :: (List.remove_assoc var !constr);
            with
            | Not_found ->
              constr := (var, coeff) :: !constr
          end
        | Tconst(Number.ConstInt(n)) ->
          let n = Number.compute_int n in
          cst := !cst + coeff * (BigInt.to_int n)
        | Tapp(func, args) when Term.ls_equal func ad_int ->
          List.iter (term_to_int coeff cst constr) args
        | Tapp(func, [arg]) -> (* record access *)
          let rec term_to_string t = match t.t_node with
            | Tapp(func, [arg]) ->
              begin

                (* this check might not be needed, as everyting is supposed to
                 * have been inlined *)
                match (Ident.Mid.find func.ls_name known_logical_ident).Decl.d_node with
                | Decl.Ddata(_) ->
                  ignore (Format.flush_str_formatter ());
                  Pretty.print_ls Format.str_formatter func;
                  let func_str = (Format.flush_str_formatter ()) in
                  Format.sprintf "%s(%s)@." func_str (term_to_string arg)
                | _ ->  raise (Not_handled t)
              end
            | Tvar(a) ->
              ignore (Format.flush_str_formatter ());
              Pretty.print_vs Format.str_formatter a;
              let func_str = (Format.flush_str_formatter ()) in
              func_str
            | _ -> raise (Not_handled t)
          in
          let t = term_to_string t in
          let v = Var.of_string t in
          if not (Environment.mem_var cfg.env v) then
            cfg.env <- Environment.add cfg.env [|v|] [||];
          constr := (v, coeff) :: !constr
        | _ -> raise (Not_handled t)
      in
      let rec aux t =
        try
          match t.t_node with
          | Tbinop(Tand, a, b) ->
            aux a @ aux b
          | Tapp(func, args) -> (* ATM, this is handled only for equality. *)

            let cst = ref 0 in
            let constr = ref [] in
            if ls_equal ps_equ func then
              match args with
              | [a; b] ->
                term_to_int 1 cst constr a; term_to_int (-1) cst constr b;
                let expr = Linexpr1.make cfg.env in
                let constr = List.map (fun (var, coeff) ->
                    Coeff.Scalar (Scalar.of_int coeff), var) !constr in
                Linexpr1.set_list expr constr None;
                let cons = Lincons1.make expr Lincons1.EQ in
                Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int !cst));
                [cons]
              | _ -> raise (Not_handled t)
            else
              raise (Not_handled t)

          | _ ->
            raise (Not_handled t)
        with
        | Not_handled(t) ->
          Format.eprintf "Couldn't understand entirely the post condition: ";
          Pretty.print_term Format.err_formatter t;
          Format.eprintf "@.";
          []
      in

      aux t
    | _ ->
      Format.eprintf "Couldn't understand post condition.@.";
      []



  let rec put_expr_in_cfg cfg expr =
    let open Expr in
    match expr.e_node with
    | Elet(LDvar(psym, let_expr), b) ->
      if Ity.(ity_equal psym.pv_ity ity_int) then
        begin
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

          let let_begin_cp, let_end_cp = put_expr_in_cfg cfg let_expr in
          add_variable cfg psym;

          (* compute the child and add an hyperedge, to set the value of psym
           * to the value returned by let_expr *)
          let b_begin_cp, b_end_cp = put_expr_in_cfg cfg b in

          let end_cp = new_node_cfg cfg expr in

          (* Save the effect of the let *)
          new_hedge_cfg cfg (let_end_cp, b_begin_cp) (fun man abs ->
              let expr = Linexpr1.make cfg.env in
              Linexpr1.set_list expr [(one, var_return)] (Some(zero));
              let p = pv_to_var psym in
              Abstract1.assign_linexpr man abs p expr None
            );

          (* erase a *)
          new_hedge_cfg cfg (b_end_cp, end_cp) (fun man abs ->
              Abstract1.forget_array man abs [|pv_to_var psym|] false);

          let_begin_cp, end_cp
        end
      else
        put_expr_in_cfg cfg b
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
          begin_cp, end_cp
        end
      else
        let i = new_node_cfg cfg expr in
        i, i
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
      begin_cp, end_cp
    | Eexec({c_node = Capp(rsym, args); _}, { Ity.cty_post = post; Ity.cty_result = ity; _ }) ->
      if Ity.(ity_equal ity ity_int) then
        begin
          (* Computing domain from postcondition *)
          let constraints =
            List.map (linear_expressions_from_term cfg) post
            |> List.concat
          in
          Format.eprintf "Computing domain from postconditions for function:";
          Expr.print_rs Format.err_formatter rsym;
          Format.eprintf "@.";
          List.iter (fun a ->
              Format.eprintf "  ->  ";
              Pretty.print_term Format.err_formatter a;
              Format.eprintf "@.";
            ) post;

          let cons_arr = Lincons1.array_make cfg.env (List.length constraints) in
          List.iteri (Lincons1.array_set cons_arr) constraints;
          Expr.print_rs Format.err_formatter rsym;
          let begin_cp = new_node_cfg cfg expr in
          let end_cp = new_node_cfg cfg expr in
          new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
              let abs = Abstract1.forget_array man abs [|var_return|] false in
              Abstract1.meet_lincons_array man abs cons_arr
            );
          begin_cp, end_cp
        end
      else
        let i = new_node_cfg cfg expr in
        i, i
    | _ ->
      Expr.print_expr Format.err_formatter expr;
      Format.eprintf "unhandled expr@.";

      let i = new_node_cfg cfg expr in

      i, i

  let get_domain cfg control_point = ()

  let domain_to_logic domain = ()

  let domain_to_string domain = ""

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
  printf "output=%a@." (Fixpoint.print_output manager) output;
  PSHGraph.iter_vertex output
    (begin fun vtx abs ~pred ~succ ->
      printf "acc(%i) = %a@."
	vtx (Abstract1.print) abs
    end)
  ;
  ()

end
