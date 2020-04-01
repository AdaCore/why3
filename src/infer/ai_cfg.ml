open Format
open Ident
open Domain
open Term
open Expr
open Ity

let infer_print_cfg =
  Debug.register_flag "infer-print-cfg" ~desc:"Print CFG used in abstract interpretation"

let infer_print_ai_result =
  Debug.register_flag "infer-print-ai-result" ~desc:"Print result of Abstract Interpretation"

module type AiCfg = sig
  module QDom : Domain.TERM_DOMAIN

  type control_point
  type xcontrol_point = control_point * xsymbol
  type control_points = control_point * control_point * xcontrol_point list

  type domain
  type cfg
  type context = QDom.man

  val empty_context  : unit -> context
  val start_cfg      : unit -> cfg

  val put_expr_in_cfg   : cfg -> context -> ?ret:vsymbol option -> expr ->
                         control_points
  val put_expr_with_pre : cfg -> context -> expr -> term list ->
                         control_points

  val eval_fixpoints : cfg -> context -> (expr * domain) list

  val domain_to_term : cfg -> context -> domain -> term

  val add_variable   : context -> pvsymbol -> unit
end

module Make(E: sig
    val       env : Env.env
    val  th_known : Decl.known_map
    val mod_known : Pdecl.known_map
    val  widening : int
  end) (Domain: DOMAIN) = struct

  module Ai_logic = Ai_logic.Make(struct
    let       env = E.env
    let  th_known = E.th_known
    let mod_known = E.mod_known
  end)

  module Uf_domain = Uf_domain.Make(struct
    module    Dom = Domain
    let  th_known = E.th_known
    let mod_known = E.mod_known
    let       env = E.env
  end)

  module QDom = Quant_domain.Make(struct
    module   TDom   = Disjunctive_term_domain.Make(Uf_domain)
    module Ai_logic = Ai_logic
  end)


  type control_point = int
  type xcontrol_point = control_point * xsymbol
  type control_points = control_point * control_point * xcontrol_point list

  type hedge = int (* hyper edge *)

  type domain = QDom.t
  type context = QDom.man

  (* control flow graph *)
  type cfg = {
    (* Not one to one. Only used for debugging purpose. *)
    expr_to_control_point: (Expr.expr, control_point) Hashtbl.t;

    (* The actual control flow graph *)
    psh_graph: (int,int,unit,unit,unit) PSHGraph.t;

    (* If id is the latest node added to the graph, then
       control_point_count is * equal to id+1 *)
    mutable control_point_count: int;

    (* Same but for hyperedge *)
    mutable hedge_count: int;

    (* Domain environment. Holds every variable that is defined in the
       program.
       FIXME might be out of date *)
    mutable env: QDom.env;

    (* This function apply the effect of a transition (an hyperedge)
       to an abstract domain *)
    mutable apply: QDom.man -> hedge -> QDom.t array -> QDom.t;

    (* Used to save the interesting control points, i.e. the beginning
       of while and for loops *)
    mutable loop_invariants: (Expr.expr * control_point) list;

    (* A term corresponding to an Apron variable. Because of regions,
       some terms can represent the same variable (let i = ref 0 in
       let j = i, terms 'contents j' and 'contents i' are the same
       apron variable). *)
    variable_mapping: (Apron.Var.t, term) Hashtbl.t;

  }

  let debug_fmt =
    if Debug.test_flag infer_print_cfg then
      let _ = Format.fprintf Format.std_formatter
                "CFG will be printed in inferdbg.dot" in
      let d = open_out "inferdbg.dot" in
      ref (formatter_of_out_channel d)
    else ref err_formatter

  let _ = if Debug.test_flag infer_print_cfg then
            fprintf !debug_fmt "digraph graphname {@."

  let fun_id x = x

  exception Unknown_hedge

  let start_cfg () =
    let cfg = { expr_to_control_point = Hashtbl.create 100;
      variable_mapping = Hashtbl.create 100;
      control_point_count = 0;
      hedge_count = 0;
      psh_graph = PSHGraph.create PSHGraph.stdcompare 3 ();
      apply = (fun _ _ _ -> raise Unknown_hedge);
      env = ();
      loop_invariants = []; }
    in
    cfg

  let empty_context = QDom.create_manager

  let add_variable a pvs =
    QDom.add_variable_to_env a pvs

  (* Adds a new node to the cfg, associated to expr (which is only useful for
   * debugging purpose ATM) *)
  let new_node_cfg cfg ?(lbl="") expr =
    let id = cfg.control_point_count in
    cfg.control_point_count <- id + 1;
    Hashtbl.add cfg.expr_to_control_point expr id;
    (* save in the cfg *)
    PSHGraph.add_vertex cfg.psh_graph id ();
    (* debug *)
    if Debug.test_flag infer_print_cfg then
      fprintf !debug_fmt
        "%d [label=\"%d:%a@\n%s\"];@."
        id id Expr.print_expr expr lbl;
    id

  (* Adds a new hyperedge between src and trg, whose effect is
     described in effect *)
  let new_hedge_cfg ?(lbl="") cfg src trg effect =
    let hedge = cfg.hedge_count in
    cfg.hedge_count <- cfg.hedge_count + 1;
    PSHGraph.add_hedge cfg.psh_graph hedge () ~pred:[|src|] ~succ:[|trg|];
    let old_apply = cfg.apply in
    cfg.apply <- begin fun man h tabs ->
      if h = hedge then
        let abs = QDom.push_label man () h tabs.(0) in
        effect man abs
      else old_apply man h tabs
    end;
    if Debug.test_flag infer_print_cfg then
      fprintf !debug_fmt "%d -> %d [label=\"%s\"];@." src trg lbl

  let create_postcondition_equality man pv vreturn =
    if not (ity_equal pv.pv_ity ity_unit) then begin
        let postcondition =
          t_app ps_equ [t_var (pv.pv_vs); t_var vreturn] None in
        QDom.meet_term man postcondition
      end
    else fun_id

  let create_vreturn: QDom.man -> Ty.ty -> vsymbol =
    let cached_vreturn = ref (Ty.Mty.empty) in
    fun man ty ->
    assert (not (Ty.ty_equal ty ty_unit));
    let vs =
      try Ty.Mty.find ty !cached_vreturn with Not_found ->
        let v = create_vsymbol (id_fresh "$ret") ty in
        cached_vreturn := Ty.Mty.add ty v !cached_vreturn;
        v in
    QDom.add_lvariable_to_env man vs;
    vs

  let create_postcondition man pv =
    if not (ity_equal pv.pv_ity ity_unit) then
      let vreturn = create_vreturn man pv.pv_vs.vs_ty in
      create_postcondition_equality man pv vreturn, QDom.forget_var man vreturn
    else fun_id, fun_id

  let remove_eps ?ret:(ret=None) manpk t =
    match t.t_node with
    | Teps tb ->
      let return, t = t_open_bound tb in
      (* Always use the same variable when returning a value,
         otherwise variables keep being created and the previous ones
         (with the good constraints) can not be accessed *)
      if Ty.ty_equal return.vs_ty ty_unit then t
      else begin
          match ret with
          | None ->
             let vs = create_vreturn manpk (return.vs_ty) in
             t_subst_single return (t_var vs) t
          | Some v -> t_subst_single return (t_var v) t
        end
    | _ -> t

  (* Adds expr to the cfg. manpk is the types of the locally defined
     variable (useful for references, when we need to get the type of
     a term in a logical formula). *)
  (* Adds multiple node and edges if expr requires so.  returns a
     tuple, whose first element is the entry point of expr in the cfg,
     and the second one is the ending point. *)
  (* The result of expr is stored is the variable "result" (see
     var_return) *)
  let rec put_expr_in_cfg cfg (manpk:QDom.man) ?ret:(ret=None) expr =
    match expr.e_node with
    | Epure t ->
      let node1, node2 = new_node_cfg cfg expr ~lbl:"pure bgn",
                         new_node_cfg cfg expr ~lbl:"pure end" in
      let vreturn = match ret with
        | None -> create_vreturn manpk (t_type t)
        | Some v -> v
      in
      let postcondition = t_app ps_equ [t_var vreturn; t] None in
      let constraints = QDom.meet_term manpk postcondition in
      new_hedge_cfg cfg node1 node2 (fun _ -> constraints) ~lbl:"pure";
      node1, node2, []
    | Elet (LDvar (pv, e1), e2) ->
          (*  let pv = e1 in e2
           *
           *  . begin_e1
           *  | e1[pv/return]
           *  . end_e1
           *  . begin_e2
           *  | …
           *  | ret = e2
           *  . end_e2
           *  | erase every temporary variable
           *  . end_cp
           **)

      add_variable manpk pv;

      let begin_e1, end_e1, exn_e1 =
        put_expr_in_cfg ~ret:(Some pv.pv_vs) cfg manpk e1 in

      let begin_e2, end_e2, exn_e2 = put_expr_in_cfg ~ret cfg manpk e2 in

      (* Save the effect of the let *)
      new_hedge_cfg cfg end_e1 begin_e2
        (fun _ abs -> abs) ~lbl:"let_e1_e2";

      let end_cp = new_node_cfg cfg expr ~lbl:"end let" in
      (* erase pv *)
      let forget_fun = QDom.forget_var manpk pv.pv_vs in
      new_hedge_cfg cfg end_e2 end_cp
        (fun _ abs -> forget_fun abs) ~lbl:"let_forget: ";

      begin_e1, end_cp, exn_e1 @ exn_e2
    | Evar pv ->
      let postcondition =
        if ity_equal pv.pv_ity ity_unit then fun_id else
          let vreturn = match ret with
            | None -> create_vreturn manpk pv.pv_vs.vs_ty
            | Some v -> v in
          let t = t_app ps_equ [t_var pv.pv_vs;t_var vreturn] None in
          QDom.meet_term manpk t in
      let begin_cp = new_node_cfg cfg expr ~lbl:"var bgn" in
      let end_cp   = new_node_cfg cfg expr ~lbl:"var end" in
      new_hedge_cfg cfg begin_cp end_cp (fun _ abs ->
          postcondition abs) ~lbl:"var";
      begin_cp, end_cp, []
    | Econst n ->
       let begin_cp = new_node_cfg cfg expr ~lbl:"const bgn" in
       let end_cp   = new_node_cfg cfg expr ~lbl:"const end" in
       let vreturn  = match ret with
         | None -> create_vreturn manpk Ty.ty_int
         | Some v -> v in
       let postcondition =
         t_app ps_equ [t_const n Ty.ty_int; t_var vreturn] None in
       let constraints = QDom.meet_term manpk postcondition in
       new_hedge_cfg cfg begin_cp end_cp (fun _ abs ->
           constraints abs) ~lbl:"const return";
       begin_cp, end_cp, []
    | Eexec ({ c_node = Capp (_, _) },
             { cty_post; cty_effect; cty_oldies }) ->

       let forget_and_constraints (forget, constrs) pv1 pv2 =
         add_variable manpk pv1;
         let new_constr = create_postcondition_equality manpk pv2 pv1.pv_vs in
         let new_forget = QDom.forget_var manpk pv1.pv_vs in
         (fun abs -> new_forget (forget abs)),
         (fun abs -> new_constr (constrs abs)) in
       let vars_to_forget, constraint_copy_ghost =
         Mpv.fold_left forget_and_constraints (fun_id, fun_id) cty_oldies in

       let constraints = List.map (remove_eps ~ret manpk) cty_post
                         |> List.fold_left t_and t_true
                         |> QDom.meet_term manpk in

       let begin_cp = new_node_cfg cfg expr ~lbl:"exec bgn" in
       let end_cp   = new_node_cfg cfg expr ~lbl:"exec end" in

       let forget_writes = Mreg.fold_left (fun constr reg pvm ->
         let forget = QDom.forget_region manpk reg pvm in
         (fun d -> constr d |> forget) ) fun_id cty_effect.eff_writes in

       (* let forget_writes = Sreg.fold_left (fun constr reg ->
        *                         let forget = QDom.forget_region manpk reg Mpv.empty in
        *                         (fun x -> constr x |> forget)
        *                       ) forget_writes cty_effect.eff_resets in *)

       new_hedge_cfg cfg begin_cp end_cp (fun _ abs ->
           constraint_copy_ghost abs
           |> forget_writes
           |> constraints
           |> vars_to_forget) ~lbl:"copy ghost\nforget writes\npost \
                                    constraints\nforget vars";

       (* FIXME: handle exceptions *)
       begin_cp, end_cp, []
    | Ewhile (e1,_,_,e2) ->

      let e1_term = match Expr.term_of_expr ~prop:true e1 with
        | Some s -> s
        | None ->
           Format.eprintf "warning, condition in while could not be \
             translated to term, an imprecise invariant will be \
             generated: %a@." Expr.print_expr e1;
           t_true in
      let constraints = QDom.meet_term manpk e1_term in

      let before_loop = new_node_cfg cfg e1 ~lbl:"before while" in
      cfg.loop_invariants <- (expr, before_loop) :: cfg.loop_invariants;
      let start_loop, end_loop, exn_loop = put_expr_in_cfg cfg manpk e2 in
      let after_loop = new_node_cfg cfg expr ~lbl:"after while" in

      new_hedge_cfg cfg before_loop start_loop
        (fun _ abs -> constraints abs) ~lbl:"meet";
      new_hedge_cfg cfg before_loop after_loop (fun _ abs ->
          (* TODO *)
          (* constraints negation loop condition,
             constraints invariants *)
          abs) ~lbl:"end (should negate)";
      new_hedge_cfg cfg end_loop before_loop
        (fun _ abs -> abs) ~lbl:"loop";

      (* FIXME: exceptions while inside the condition *)
      before_loop, after_loop, exn_loop
    | Eraise (xs, e) ->
       let e_begin, e_end, e_exn = put_expr_in_cfg cfg manpk e in

       (* create nodes to capture normal termination *)
       let raise_bgn = new_node_cfg cfg expr ~lbl:"raise" in
       let raise_end = new_node_cfg cfg expr ~lbl:"normal termination BOT" in
       new_hedge_cfg cfg raise_bgn raise_end
         (fun man _ -> QDom.bottom man ()) ~lbl:"raise bottom";

       e_begin, raise_end, (e_end, xs) :: e_exn
    | Eif (e1, e2, e3) ->
       let e1_true, e1_false =
         match Expr.term_of_expr ~prop:true e1 with
         | Some t -> t, t_not t
         | None ->
            Format.eprintf "warning, condition in if could not be \
              translated to term (not pure), an imprecise invariant \
              will be generated: %a@." Expr.print_expr e1;
            t_true, t_true in
       let constraints     = QDom.meet_term manpk e1_true in
       let constraints_not = QDom.meet_term manpk e1_false in
       let e2_begin, e2_end, e2_exn = put_expr_in_cfg ~ret cfg manpk e2 in
       let e3_begin, e3_end, e3_exn = put_expr_in_cfg ~ret cfg manpk e3 in
       let start_if = new_node_cfg cfg expr ~lbl:"if start" in
       let end_if   = new_node_cfg cfg expr ~lbl:"if end" in
       new_hedge_cfg cfg start_if e2_begin
         (fun _ abs -> constraints abs) ~lbl:"if true";
       new_hedge_cfg cfg start_if e3_begin
         (fun _ abs -> constraints_not abs) ~lbl:"if false";
       new_hedge_cfg cfg e2_end end_if
         (fun _ abs -> abs) ~lbl:"if true end";
       new_hedge_cfg cfg e3_end end_if
         (fun _ abs -> abs) ~lbl:"if false end";
      start_if, end_if, e2_exn @ e3_exn
    | Ematch (match_e, l, mxs) when Mxs.is_empty mxs ->
      let e_begin, e_end, e_exn = put_expr_in_cfg cfg manpk match_e in
      let e_exns = ref [e_exn] in
      let match_end = new_node_cfg cfg expr ~lbl:"match end" in
      let process_branch (p,be) =
        let constraints, forget_before, forget_end =
          match p.pp_pat.pat_node with
          | Pwild -> fun_id, fun_id, fun_id
          | Pvar _ -> failwith "pattern"
          | Papp (ls, p) ->
             let args = List.map (fun p -> match p.pat_node with
               | Pvar vs -> add_variable manpk (restore_pv vs); vs
               | Pwild   -> create_vreturn manpk p.pat_ty
               | _       -> failwith "nested pattern or worse") p in
             let matched_term =
               t_app ls (List.map t_var args) (Some (ty_of_ity match_e.e_ity)) in
             let vreturn = match ret with
               | None -> create_vreturn manpk (t_type matched_term)
               | Some v -> v in
             let postcondition =
               t_app ps_equ [matched_term; t_var vreturn] None in
             let constr = QDom.meet_term manpk postcondition in
             let forget_before = QDom.forget_var manpk vreturn in
             let forget_after = List.fold_left (fun f arg ->
                  fun x -> QDom.forget_var manpk arg (f x)) fun_id args in
             constr,forget_before,forget_after
          | Por _ -> failwith "pattern or"
          | Pas _ -> failwith "pattern as" in
        let be_begin, be_end, be_exn = put_expr_in_cfg cfg manpk be in
        new_hedge_cfg cfg e_end be_begin
          (fun _ abs -> forget_before (constraints abs)) ~lbl:"match asgns forgets before";
        new_hedge_cfg cfg be_end match_end
          (fun _ abs -> forget_end abs) ~lbl:"match forget end";
        e_exns := be_exn :: !e_exns in
      List.iter process_branch l;
      e_begin, match_end, List.concat !e_exns
    | Ematch (exc_e, [], exc) ->
       let additional_exn = ref [] in
       let e_begin, e_end, e_exn = put_expr_in_cfg ~ret cfg manpk exc_e in
       let end_match = new_node_cfg cfg expr ~lbl:"exn end" in
       let process_branch (pvl,e) =
         List.iter (fun p -> add_variable manpk p) pvl;
         let before_assign = new_node_cfg cfg e ~lbl:"exn branch bfr asgn" in
         let e_begin, e_end, e_exn = put_expr_in_cfg ~ret cfg manpk e in
         additional_exn := e_exn @ !additional_exn;
         begin match pvl with
         | [p] ->
            let constraints, forget_ret = create_postcondition manpk p in
              new_hedge_cfg cfg before_assign e_begin (fun _ abs ->
                  forget_ret (constraints abs)) ~lbl:"exn asgn forget before";
              let to_forget = QDom.forget_var manpk p.pv_vs in
              new_hedge_cfg cfg e_end end_match
                (fun _ abs -> to_forget abs) ~lbl:"exn forget end";
         | _ -> Format.eprintf
                  "Multiple constructors exception, not handled by AI.";
                new_hedge_cfg cfg before_assign e_begin
                  (fun _ abs -> abs) ~lbl:"exn TODO";
                new_hedge_cfg cfg e_end end_match
                  (fun _ abs -> abs) ~lbl:"exn TODO";
         end;
         pvl, before_assign, e_end in
       let exc = Mxs.map process_branch exc in
       let process_exception xs1 (_, cp1,_) e_exn =
         List.filter (fun (cp2, xs2) ->
             if xs_equal xs1 xs2 then begin
               new_hedge_cfg cfg cp2 cp1 (fun _ abs -> abs) ~lbl:"exn nothing";
               false end
             else true ) e_exn in
       let e_exn = Mxs.fold process_exception exc e_exn in
       new_hedge_cfg cfg e_end end_match
         (fun _ abs -> abs) ~lbl:"exn e normal termination";
       e_begin, end_match, !additional_exn @ e_exn
    | Eassert _ | Eabsurd -> (* FIXME: maybe they could be taken into account *)
       let node = new_node_cfg cfg expr in
       node, node, []
    | Eghost e -> put_expr_in_cfg ~ret cfg manpk e
    | Efor (pv, (lo, dir, up), _, _, e) ->
       (* . before_loop
        * | k = 0      k = n -> forget_k
        * . start_loop ------------------> end_loop
        * | 0 <= k <= n
        * . e_begin
        * :
        * :       k = k + 1
        * . e_end --------> start_loop
        *)
       let pv_t, lo_t, up_t = t_var pv.pv_vs, t_var lo.pv_vs, t_var up.pv_vs in
       add_variable manpk pv;

       let before_loop = new_node_cfg cfg expr ~lbl:"for before" in
       let start_loop = new_node_cfg cfg expr ~lbl:"for start" in
       cfg.loop_invariants <- (expr, start_loop) :: cfg.loop_invariants;
       let e_begin, e_end, e_exn = put_expr_in_cfg cfg manpk e in
       let end_loop_cp = new_node_cfg cfg expr ~lbl:"for end" in

       let postcondition_before = t_app ps_equ [pv_t; lo_t] None in
       let constraints_start = QDom.meet_term manpk postcondition_before in

       let bounds a b =
         t_and (t_app Ai_logic.le_int [a; pv_t] None)(t_app Ai_logic.le_int [pv_t; b] None) in
       let precondition_e =
         if dir = Expr.To then bounds lo_t up_t else bounds up_t lo_t in
       let constraints_e = QDom.meet_term manpk precondition_e in
       let postcondition = t_app ps_equ [pv_t; up_t] None in
       let constraints_post = QDom.meet_term manpk postcondition in

       new_hedge_cfg cfg before_loop start_loop
         (fun _ -> constraints_start) ~lbl:"for pv=lo";
       new_hedge_cfg cfg start_loop e_begin
         (fun _ -> constraints_e) ~lbl:"for lo<=pv<=up";

       let vret_pv = create_vreturn manpk Ty.ty_int in
       let res = t_app Ai_logic.ad_int [pv_t; t_nat_const 1] (Some Ty.ty_int) in
       let next_assign =
         t_app ps_equ [t_var vret_pv; res] None
         |> QDom.meet_term manpk in
       let forget_pv = QDom.forget_var manpk pv.pv_vs in
       let vret_equal =
         t_app ps_equ [t_var vret_pv; pv_t] None
         |> QDom.meet_term manpk in
       let forget_vret = QDom.forget_var manpk vret_pv in

       new_hedge_cfg cfg e_end start_loop (fun _ abs ->
          (* vret = k + 1, forget k, k = vret, forget vret *)
           next_assign abs
           |> forget_pv
           |> vret_equal
           |> forget_vret) ~lbl:"for loop next_assign;\n \
                                 forget pv; vret=pv; forget_vret";
       new_hedge_cfg cfg start_loop end_loop_cp (fun _ abs ->
           constraints_post abs
           |> forget_pv) ~lbl:"loop termination";
       before_loop, end_loop_cp, e_exn
    | _ ->
       Format.eprintf "expression not handled, will probably lead to \
                       some errors: %a@." Expr.print_expr expr;
       begin match expr.e_loc with
       | None -> ()
       | Some l -> Loc.report_position Format.err_formatter l; end;
       let node = new_node_cfg cfg expr in
       node, node, []

  let put_expr_with_pre cfg manpk e pre =
    let i = new_node_cfg cfg e in
    let e_start_cp, e_end_cp, e_exn = put_expr_in_cfg cfg manpk e in
    let constraints = QDom.meet_term manpk (t_and_l pre) in
    new_hedge_cfg cfg i e_start_cp (fun _ -> constraints);
    i, e_end_cp, e_exn

  let domain_to_term _ manpk domain =
    QDom.to_term manpk domain

  let vertex_dummy = -1
  (** dummy value *)
  let hedge_dummy= -1
  (** dummy value *)


  (** {2 The fixpoint manager } *)

  let dot_file = open_out "t.dot"
  let dot_fmt = Format.formatter_of_out_channel dot_file

  let get_fixpoint_man cfg man =
    let (manager:(int,int, QDom.t,unit) Fixpoint.manager) = {
      Fixpoint.bottom = begin fun _ -> QDom.bottom man () end;
      Fixpoint.canonical = begin fun _ abs -> QDom.canonicalize man abs end;
      Fixpoint.is_bottom = begin fun _ abs -> QDom.is_bottom man abs end;
      Fixpoint.is_leq = begin fun _ abs1 abs2 -> QDom.is_leq man abs1 abs2 end;
      Fixpoint.join = begin fun _ abs1 abs2 -> QDom.join man abs1 abs2 end;
      Fixpoint.join_list = begin fun _ labs -> QDom.join_list man labs end;
      Fixpoint.widening = begin fun _ abs1 abs2 -> QDom.widening man abs1 abs2 end;
      Fixpoint.odiff = None;
      Fixpoint.apply = (fun a b -> (), cfg.apply man a b);
      Fixpoint.arc_init = begin fun _ -> () end;
      Fixpoint.abstract_init=
        begin fun vertex ->
          if vertex=0 then QDom.top man cfg.env else QDom.bottom man cfg.env
        end;

      Fixpoint.print_abstract = QDom.print;
      Fixpoint.print_arc = (fun _ () -> ());
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
      Fixpoint.dot_vertex = (fun fmt -> Format.fprintf fmt "v%i");
      Fixpoint.dot_hedge  = (fun fmt -> Format.fprintf fmt "h%i");
      Fixpoint.dot_attrvertex = pp_print_int;
      Fixpoint.dot_attrhedge = pp_print_int;
    }
    in manager


  let eval_fixpoints cfg manpk =
    let manager = get_fixpoint_man cfg manpk in
    let compare_no_closured = PSHGraph.stdcompare.PSHGraph.comparev in
    let sinit = PSette.singleton compare_no_closured 0 in
    let make_strategy is_active =
      Fixpoint.make_strategy_default
        ~widening_start:E.widening
        ~widening_descend:(max (E.widening/2) 2)
        ~priority:(PSHGraph.Filter is_active)
        ~vertex_dummy
        ~hedge_dummy
        cfg.psh_graph sinit in
    let output = Fixpoint.analysis_guided manager
                   cfg.psh_graph sinit make_strategy in

    (* Format.printf "output=%a@." (Fixpoint.print_output manager) output;
     * Format.printf "\n\nRESULT:\n";
     * PSHGraph.iter_vertex output
     *   (fun vtx abs ~pred ~succ ->
     *   printf "\tacc(%i) = %a@." vtx QDom.print abs); *)

    (*printf "output=%a@." (Fixpoint.print_output manager) output;*)
    let l = ref [] in
    PSHGraph.iter_vertex output
      (fun vtx abs ~pred:_ ~succ:_ -> l := (vtx, abs) :: !l);

    if Debug.test_flag infer_print_ai_result then
      begin
        let l = List.sort (fun (i, _) (j, _) -> compare i j) !l in
        Format.printf "DOMAIN TERMS (set ai-print-cfg to true and \
                       check inferdbg.dot file to see control points)\n";
        List.iter (fun (vtx, abs) ->
            let t = QDom.to_term manpk abs in
            printf "acc(%i) -> %a@." vtx Pretty.print_term t) l;

        (* Print loop invariants *)

        Format.printf "Loop invariants:@.";
        List.iter (fun (expr, cp) ->
            let abs = PSHGraph.attrvertex output cp in
            Format.printf "For: @[%a@]@\nDOMAIN:@[%a@]@\nInvariant:@[%a@]@."
              Expr.print_expr expr
              QDom.print abs
              Pretty.print_term (Pretty.forget_all (); domain_to_term cfg manpk abs);
          ) cfg.loop_invariants;
      end;
    if Debug.test_flag infer_print_cfg then
      Format.fprintf !debug_fmt "}@.";
    close_out dot_file;
    List.map (fun (expr, cp) ->
        let abs = PSHGraph.attrvertex output cp in
        expr, abs
      ) cfg.loop_invariants
end
