open Format
open Ident
open Domain
open Term
open Expr
open Ity

let dbg_print_cfg =
  Debug.register_flag "ai_print_domains" ~desc:"Print domains to debug"
let ai_cfg_debug =
  Debug.register_flag "ai_cfg_debug" ~desc:"CFG debug"

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

  open Ai_logic

  module Uf_domain =
    Uf_domain.Make(struct
        module    Dom = Domain
        let  th_known = E.th_known
        let mod_known = E.mod_known
        let       env = E.env
      end)

  module QDom = Quant_domain.Make(struct
      module    Dom = Disjunctive_term_domain.Make(Uf_domain)
      let  th_known = E.th_known
      let mod_known = E.mod_known
      let       env = E.env
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
    if Debug.test_flag dbg_print_cfg then
      let d = open_out "inferdbg.dot" in
      ref (formatter_of_out_channel d)
    else ref err_formatter

  let _ = if Debug.test_flag dbg_print_cfg then
            fprintf !debug_fmt "digraph graphname {@."

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
  let new_node_cfg cfg ?label:(l="") expr =
    let id = cfg.control_point_count in
    cfg.control_point_count <- id + 1;
    Hashtbl.add cfg.expr_to_control_point expr id;
    (* save in the cfg *)
    PSHGraph.add_vertex cfg.psh_graph id ();
    (* debug *)
    if Debug.test_flag dbg_print_cfg then begin
      fprintf !debug_fmt "%d [label=\"" id;
      if l <> "" then fprintf !debug_fmt "%s" l
      else Expr.print_expr !debug_fmt expr;
      fprintf !debug_fmt "\"];@."
      end;
    id

  (* Adds a new hyperedge between src and trg, whose effect is
     described in effect *)
  let new_hedge_cfg cfg src trg effect =
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
    if Debug.test_flag dbg_print_cfg then
      fprintf !debug_fmt "%d -> %d@." src trg

  let create_postcondition_equality man pv vreturn =
    if not (ity_equal pv.pv_ity ity_unit) then begin
        let postcondition =
          t_app ps_equ [t_var (pv.pv_vs); t_var vreturn] None in
        if Debug.test_flag ai_cfg_debug then
          Format.eprintf "--> Postcondition for let: %a@."
            Pretty.print_term postcondition;
        QDom.meet_term man postcondition
      end
    else fun x -> x

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

  (* TODO write description *)
  let create_postcondition man pv =
    if not (ity_equal pv.pv_ity ity_unit) then
      let vreturn = create_vreturn man pv.pv_vs.vs_ty in
      create_postcondition_equality man pv vreturn, QDom.forget_var man vreturn
    else
      (fun x -> x), (fun x -> x)

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
      let i, j = new_node_cfg cfg expr, new_node_cfg cfg expr in
      let vreturn = match ret with
        | None -> create_vreturn manpk (t_type t)
        | Some v -> v
      in
      let postcondition = t_app ps_equ [t_var vreturn; t] None in
      let constraints = QDom.meet_term manpk postcondition in
      new_hedge_cfg cfg i j (fun _ abs ->
          constraints abs);
      i, j, []

    | Elet (LDvar (psym, let_expr), c) ->
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
           *  . b_end_cp
           *  | erase every temporary variable
           *  . end_cp
           **)
       if Debug.test_flag ai_cfg_debug then
         Format.eprintf "Computing for Elet: %a = %a@."
           print_pv psym print_expr let_expr;

      add_variable manpk psym;
      let let_begin_cp, let_end_cp, let_exn = put_expr_in_cfg ~ret:(Some psym.pv_vs) cfg manpk let_expr in

      (* let forget_ret manpk abs =
       *   let ty = Ity.(ty_of_ity (psym.pv_ity)) in
       *   if Ty.ty_equal ty Ity.ty_unit then
       *     abs
       *   else
       *     D.forget_var manpk psym.pv_vs abs in *)

      (* compute the child and add an hyperedge, to set the value of psym
       * to the value returned by let_expr *)
      let b_begin_cp, b_end_cp, b_exn = put_expr_in_cfg ~ret cfg manpk c in


      (* Save the effect of the let *)
      new_hedge_cfg cfg let_end_cp b_begin_cp (fun _ abs ->
          (* forget_ret manpk *) abs
        );

      let end_cp = new_node_cfg cfg expr in
      (* erase a *)
      let forget_fun = QDom.forget_var manpk psym.pv_vs in
      new_hedge_cfg cfg b_end_cp end_cp (fun _ abs ->
          forget_fun abs
        );
      let_begin_cp, end_cp, let_exn @ b_exn

    | Evar (psym) ->
      let constraints =
        if not (ity_equal  psym.pv_ity ity_unit) then
          begin
          let ty = (psym.pv_vs.vs_ty) in

          let vreturn = match ret with
            | None -> create_vreturn manpk ty
            | Some v -> v
          in
          let postcondition =
            t_app ps_equ [t_var psym.pv_vs;t_var vreturn] None in

          if Debug.test_flag ai_cfg_debug then
            begin
              Format.eprintf "--> Postcondition for var: ";
              Pretty.print_term Format.err_formatter postcondition;
              Format.eprintf "@.";
            end;
          QDom.meet_term manpk postcondition
          end
        else
          (fun abs -> abs)
      in

      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg ~label:"value returned" expr in
      new_hedge_cfg cfg begin_cp end_cp (fun _ abs ->
          constraints abs
        );
      begin_cp, end_cp, []
    | Econst n ->
      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg ~label:"constant returned" cfg expr in

      let vreturn = match ret with
        | None -> create_vreturn manpk Ty.ty_int
        | Some v -> v
      in
      let postcondition = t_app ps_equ [t_const n Ty.ty_int; t_var vreturn] None in
      let constraints = QDom.meet_term manpk postcondition in

      new_hedge_cfg cfg begin_cp end_cp (fun _ abs ->
          constraints abs
        );
      begin_cp, end_cp, []
    | Eexec ({c_node = Capp (rsym, _); _}, { cty_post = post; cty_effect = effect;  cty_oldies = oldies; _ }) ->
      let eff_write = effect.eff_writes in
      let vars_to_forget, constraint_copy_ghost = Mpv.fold_left (
          fun (vars_to_forget, constraints) k b ->
            add_variable manpk k;
            let new_constraints = create_postcondition_equality manpk b k.pv_vs in
            let forget_var = QDom.forget_var manpk k.pv_vs in
            (fun abs -> vars_to_forget abs |> forget_var), (fun abs -> constraints abs |> new_constraints)
        ) ((fun x -> x), fun x -> x) oldies in

      (* Computing domain from postcondition *)
      if Debug.test_flag ai_cfg_debug then
        begin
          Format.eprintf "Computing domain from postconditions for function: ";
          Expr.print_rs Format.err_formatter rsym;
          List.iter (fun a ->
              Format.eprintf "    ###>  ";
              Pretty.print_term Format.err_formatter a;
              Format.eprintf "@.";
            ) post;

          Format.eprintf "@.";
        end;
      let constraints =
        List.map (remove_eps ~ret manpk) post
        |> List.fold_left t_and t_true
        |> QDom.meet_term manpk
      in
      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg ~label:"function called" cfg expr in

      let forget_writes = Mreg.fold_left (fun constr a b ->

          let forget = QDom.forget_region manpk a b in
          (fun x ->
             constr x |> forget)
        ) (fun x -> x) eff_write in

      new_hedge_cfg cfg begin_cp end_cp (fun _ abs ->
          constraint_copy_ghost abs  |> forget_writes |> constraints |> vars_to_forget
        );
      (* FIXME: handle exceptions *)
      begin_cp, end_cp, []
    | Ewhile (cond, _, _, content) ->
      (* Condition expression *)
      let cond_term =
        match Expr.term_of_expr ~prop:true cond with
        | Some s ->
          s
        | None ->
          Format.eprintf "warning, condition in while could not be translated to term, an imprecise invariant will be generated";
          t_true
      in
      let constraints = QDom.meet_term manpk cond_term in

      let before_loop_cp = new_node_cfg cfg cond in
      cfg.loop_invariants <- (expr, before_loop_cp) :: cfg.loop_invariants;
      let start_loop_cp, end_loop_cp, loop_exn = put_expr_in_cfg cfg manpk content in
      let after_loop_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg before_loop_cp start_loop_cp (fun _ abs ->
          constraints abs
        );
      new_hedge_cfg cfg before_loop_cp after_loop_cp (fun _ abs ->
          (* TODO *)
          abs
        );
      new_hedge_cfg cfg end_loop_cp before_loop_cp (fun _ abs ->
          abs
        );
      (* FIXME: exceptions while inside the condition *)
      before_loop_cp, after_loop_cp, loop_exn
    | Eraise (s, e) ->
      let arg_begin, arg_end_cp, arg_exn = put_expr_in_cfg cfg manpk e in
      let j = new_node_cfg cfg expr in
      let k = new_node_cfg cfg expr in
      new_hedge_cfg cfg j k (fun man _ ->
          QDom.bottom man ());
      arg_begin, k, ((arg_end_cp, s)::arg_exn)

    | Eif (cond, b, c) ->
      (* Condition expression *)
      let cond_term, not_cond_term =
        match Expr.term_of_expr ~prop:true cond with
        | Some s ->
          s, t_not s
        | None ->
          Format.eprintf "warning, condition in if could not be translated to term (not pure), an imprecise invariant will be generated@.";
          Expr.print_expr Format.err_formatter cond;
          Format.eprintf "@.";
          t_true, t_true
      in
      let constraints = QDom.meet_term manpk cond_term in
      let constraints_not = QDom.meet_term manpk not_cond_term in
      let b_begin_cp, b_end_cp, b_exn = put_expr_in_cfg ~ret cfg manpk b in
      let c_begin_cp, c_end_cp, c_exn = put_expr_in_cfg ~ret cfg manpk c in
      let start_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg start_cp b_begin_cp (fun _ abs ->
          constraints abs);
      new_hedge_cfg cfg start_cp c_begin_cp (fun _ abs ->
          constraints_not abs);
      new_hedge_cfg cfg c_end_cp end_cp (fun _ abs ->
          abs);
      new_hedge_cfg cfg b_end_cp end_cp (fun _ abs ->
          abs);
      start_cp, end_cp, b_exn @ c_exn
    | Ematch (case_e, l, mxs) when Mxs.is_empty mxs ->
      let case_e_begin_cp, case_e_end_cp, case_e_exn = put_expr_in_cfg cfg manpk case_e in
      let e_exns = ref [case_e_exn] in
      let case_end_cp = new_node_cfg cfg expr in
      List.iter (fun (p, e) ->
          let constraints, to_forget_before, to_forget_end = match p.pp_pat.pat_node with
            | Pwild -> (fun abs -> abs), (fun abs -> abs), (fun x -> x)
            | Pvar _ -> failwith "pattern"
            | Papp (l, p) ->
              let args = List.map (fun p -> match p.pat_node with
                  | Pvar (vsym) ->
                    let pv = restore_pv vsym in
                    add_variable manpk pv;
                    vsym
                  | Pwild ->
                    create_vreturn manpk p.pat_ty
                  | _ -> failwith "nested pattern or worse"
                ) p in
              let matched_term = t_app l (List.map t_var args) (Some (ty_of_ity (case_e.e_ity))) in
              let vreturn = match ret with
                | None -> create_vreturn manpk (t_type matched_term)
                | Some v -> v
              in
              let postcondition =
                  t_app ps_equ [matched_term; t_var vreturn] None in
              let constr = QDom.meet_term manpk postcondition
              in
              constr, QDom.forget_var manpk vreturn, (List.fold_left (fun c arg ->
                  fun x -> c x |> QDom.forget_var manpk arg) (fun x -> x) args)

            | Por _ -> failwith "pattern or"
            | Pas _ -> failwith "pattern as"
          in
          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg manpk e in
          new_hedge_cfg cfg case_e_end_cp e_begin_cp (fun _ abs ->
              constraints abs |> to_forget_before
            );
          new_hedge_cfg cfg e_end_cp case_end_cp (fun _ abs ->
              to_forget_end abs
            );
          e_exns := e_exn :: !e_exns;
        ) l;
      case_e_begin_cp, case_end_cp, (List.concat !e_exns)
    | Ematch (e, [], exc) ->
      let additional_exn = ref [] in
      let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg ~ret cfg manpk e in
      let i = new_node_cfg cfg expr in
      let exc = Mxs.map (fun (l, e) ->
          List.iter (fun p ->
              add_variable manpk p) l;

          let before_assign_cp = new_node_cfg cfg e in

          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg ~ret cfg manpk e in

          additional_exn := e_exn @ !additional_exn;

          begin
            match l with
            | [p] ->
              let constraints, forget_ret = create_postcondition manpk p in
              new_hedge_cfg cfg before_assign_cp e_begin_cp (fun _ abs ->
                  constraints abs |> forget_ret
                );

              let to_forget = QDom.forget_var manpk p.pv_vs in
              new_hedge_cfg cfg e_end_cp i (fun _ abs ->
                  to_forget abs
                );
            | _ -> Format.eprintf "Multiple constructors exception, not handled by AI.";
              new_hedge_cfg cfg before_assign_cp e_begin_cp (fun _ abs -> abs);
              new_hedge_cfg cfg e_end_cp i (fun _ abs -> abs);
          end;
          l, before_assign_cp, e_end_cp
          ) exc in

      let e_exn = Mxs.fold (fun exc_sym (_, cp_begin, _) e_exn ->
          List.filter (fun (cp, exc_sym_) ->
              if xs_equal exc_sym exc_sym_ then
                begin
                  new_hedge_cfg cfg cp cp_begin (fun _ abs ->
                       abs
                    );
                  false
                end
              else
                true
            ) e_exn) exc e_exn in
      new_hedge_cfg cfg e_end_cp i (fun _ abs ->
          abs
        );
      e_begin_cp, i, !additional_exn @ e_exn
    | Eassert _ | Eabsurd -> (* FIXME: maybe they could be taken into account *)
      let i = new_node_cfg cfg expr in

      i, i, []

    | Eghost e -> put_expr_in_cfg ~ret cfg manpk e

    | Efor (k, (lo, dir, up), _, _, e) ->
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
        (t_var k.pv_vs, t_var lo.pv_vs, t_var up.pv_vs)
      in
      add_variable manpk k;

      let before_loop_cp = new_node_cfg cfg expr in
      let start_loop_cp = new_node_cfg cfg expr in
      cfg.loop_invariants <- (expr, start_loop_cp) :: cfg.loop_invariants;
      let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg manpk e in
      let end_loop_cp = new_node_cfg cfg expr in

      let postcondition_before = t_app ps_equ [k_term; lo] None in
      let constraints_start = QDom.meet_term manpk postcondition_before in

      let precondition_e =
        if dir = Expr.To then
          t_and (t_app le_int [lo; k_term] None) (t_app le_int [k_term; up] None)
        else
          t_and (t_app le_int [up; k_term] None) (t_app le_int [k_term; lo] None)
      in
      let constraints_e = QDom.meet_term manpk precondition_e in

      let postcondition =
          t_app ps_equ [k_term; up] None
      in
      let constraints_post = QDom.meet_term manpk postcondition in

      new_hedge_cfg cfg before_loop_cp start_loop_cp (fun _ -> constraints_start);
      new_hedge_cfg cfg start_loop_cp e_begin_cp (fun _ -> constraints_e);
      let vret_k = create_vreturn manpk Ty.ty_int in
      let forget_vret = QDom.forget_var manpk vret_k in
      let forget_k = QDom.forget_var manpk k.pv_vs in
      let res = t_app ad_int [k_term; t_nat_const 1] (Some Ty.ty_int) in
      let next_assignation = t_app ps_equ [t_var vret_k; res] None |> QDom.meet_term manpk in
      let vret_equal = t_app ps_equ [t_var vret_k; k_term] None |> QDom.meet_term manpk in
      new_hedge_cfg cfg e_end_cp start_loop_cp (fun _ abs ->
          (* vret = k + 1, forget k, k = vret, forget vret *)
          next_assignation abs |> forget_k |> vret_equal |> forget_vret
        );
      new_hedge_cfg cfg start_loop_cp end_loop_cp (fun _ abs ->
          constraints_post abs |> forget_k
        );
      before_loop_cp, end_loop_cp, e_exn

    | _ ->
      Format.eprintf "expression not handled, will probably lead to some errors";
      Expr.print_expr Format.err_formatter expr;
      begin
      match expr.e_loc with
      | None -> ()
      | Some l -> Loc.report_position Format.err_formatter l;
      end;
      let i = new_node_cfg cfg expr in
      i, i, []

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
      Fixpoint.print_arc = (fun fmt () -> pp_print_string fmt "()");
      Fixpoint.print_vertex = pp_print_int;
      Fixpoint.print_hedge = pp_print_int;

      Fixpoint.accumulate = false;
      Fixpoint.print_fmt = Format.std_formatter;
      Fixpoint.print_analysis = true;
      Fixpoint.print_component = true;
      Fixpoint.print_step = true;
      Fixpoint.print_state = true;
      Fixpoint.print_postpre = true;
      Fixpoint.print_workingsets = true;

      Fixpoint.dot_fmt = Some dot_fmt;
      Fixpoint.dot_vertex = (fun fmt -> Format.fprintf fmt "v%i@.");
      Fixpoint.dot_hedge  = (fun fmt -> Format.fprintf fmt "h%i@.");
      Fixpoint.dot_attrvertex = pp_print_int;
      Fixpoint.dot_attrhedge = pp_print_int;
    }
    in manager


  let eval_fixpoints cfg manpk =
    let manager = get_fixpoint_man cfg manpk in
    let compare_no_closured = PSHGraph.stdcompare.PSHGraph.comparev in
    let sinit = PSette.singleton compare_no_closured 0 in
    let make_strategy =
      fun is_active ->
      Fixpoint.make_strategy_default
        ~widening_start:E.widening ~widening_descend:(max (E.widening/2) 2)
        ~priority:(PSHGraph.Filter is_active)
        ~vertex_dummy ~hedge_dummy
        cfg.psh_graph sinit
    in
    let output = Fixpoint.analysis_guided
                   manager cfg.psh_graph sinit make_strategy
    in
    (*printf "output=%a@." (Fixpoint.print_output manager) output;*)
    let l = ref [] in
    PSHGraph.iter_vertex output
      (fun vtx abs ~pred:_ ~succ:_ ->
        l := (vtx, abs) :: !l);

    if Debug.test_flag dbg_print_cfg then
      begin
        let l = List.sort (fun (i, _) (j, _) -> compare i j) !l in
        List.iter (fun (vtx, abs) ->
            let t = QDom.to_term manpk abs in
            printf "acc(%i) -> @." vtx;
            Format.printf "@.";
            Pretty.print_term Format.std_formatter t;
            Format.printf "@.";
          (*let gen = Abstract1.to_generator_array manpk abs in
            Generator1.array_print Format.std_formatter gen;
            let n = Generator1.array_length gen in
            for i = 0 to n - 1 do
            let linexpr = Generator1.array_get  gen i |> Generator1.get_linexpr1 in
            Linexpr1.print Format.std_formatter linexpr;
            Format.printf " = ";
            Coeff.print Format.std_formatter (Linexpr1.get_cst linexpr);
            Format.printf "@.";
            done;
            Format.printf "@.";*)
          ) l;

        let l = ref [] in
        Hashtbl.iter (fun a b ->
            l := (a, b) :: !l;
          ) cfg.expr_to_control_point;
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
            Format.printf "%a@." QDom.print abs;
            Pretty.forget_all ();
            Pretty.print_term Format.std_formatter (domain_to_term cfg manpk abs);
            printf "@."
          ) cfg.loop_invariants;

        if Debug.test_flag dbg_print_cfg then
          Format.fprintf !debug_fmt "}@.";
      end;
    let invs = List.map (fun (expr, cp) ->
        let abs = PSHGraph.attrvertex output cp in
        expr, abs
      ) cfg.loop_invariants in
    (* FixpointType.dot_graph manager cfg.psh_graph; *)
    close_out dot_file;
    invs

end
