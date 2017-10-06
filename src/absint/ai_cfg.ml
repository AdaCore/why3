open Domain

let ai_print_domains = Debug.register_flag "ai_print_domains" ~desc:"Print domains to debug"
let ai_cfg_debug = Debug.register_flag "ai_cfg_debug" ~desc:"CFG debug"

open Format
open Apron

module Make(E: sig
    val env: Env.env
    val pmod: Pmodule.pmodule
    val widening: int
    module D: DOMAIN
  end) = struct

  module Ai_logic = Ai_logic.Make(struct
      let env = E.env
      let pmod = E.pmod
    end)
  open Ai_logic
  
  let debug_fmt =
    if Debug.test_flag ai_print_domains then
      let d = open_out "dbg.dot" in
      Some (Format.formatter_of_out_channel d)
    else
      None

  let _ =
    match debug_fmt with
    | Some debug_fmt -> Format.fprintf debug_fmt "digraph graphname {@."
    | None -> ()
  
  open Term

  module D = Quant_domain.Make(struct
      module A = Disjunctive_term_domain.Make(struct
          module A = Uf_domain.Make(struct
              module A = E.D
              let pmod = E.pmod
              let env = E.env
            end)
          let pmod = E.pmod
          let env = E.env
        end)
      let pmod = E.pmod
      let env = E.env
    end)
  module Domain = D

  (* Apron manager *)
  (*let manpk = PolkaGrid.manager_alloc (Polka.manager_alloc_strict ()) (Ppl.manager_alloc_grid ())
  type apron_domain = Polka.strict PolkaGrid.t*)

  type control_point = int
  type hedge = int

  type domain = D.t 

  (* control flow graph *)
  type cfg = {
    (* Not one to one. Only used for debugging purpose. *)
    expr_to_control_point: (Expr.expr, control_point) Hashtbl.t;

    (* The actual control flow graph *)
    g:(int,int,unit,unit,unit) PSHGraph.t;

    (* If id is the latest node added to the graph, then control_point_count is
     * equal to id+1 *)
    mutable control_point_count: int;

    (* Same but for hyperedge *)
    mutable hedge_count: int;

    (* Domain environment. Holds every variable that is defined in the program FIXME might be out of date *)
    mutable env: D.env;

    (* This function apply the effect of a transition (an hyperedge) to
     * an abstract domain *)
    mutable apply: D.man -> hedge -> D.t array -> unit * D.t;

    (* Used to save the interesting control points, i.e. the beginning of 
     * while and for loops *)
    mutable loop_invariants: (Expr.expr * control_point) list;

    (* A term corresponding to an Apron variable. Because of regions, some
     * terms can represent the same variable (let i = ref 0 in let j = i, terms
     * 'contents j' and 'contents i' are the same apron variable). *)
    variable_mapping: (Apron.Var.t, Term.term) Hashtbl.t;
  
  }
  
  type context = D.man

  let domain_manager x = x

  let empty_context = D.create_manager

  exception Unknown_hedge

  (* Initialize an hedge *)

  let ident_ret = Ident.{pre_name = "$ret"; pre_label = Ident.Slab.empty; pre_loc = None; }
  let cached_vreturn = ref (Ty.Mty.empty)
  let create_vreturn manpk ty =
    assert (not (Ty.ty_equal ty Ity.ty_unit));
    let v =
      try
        Ty.Mty.find ty !cached_vreturn
      with
      | Not_found ->
        let v  = Term.create_vsymbol ident_ret ty in
        cached_vreturn := Ty.Mty.add ty v !cached_vreturn;
        v
    in
    D.add_lvariable_to_env manpk v;
    v

  let start_cfg _ =
    let cfg = { expr_to_control_point = Hashtbl.create 100;
      variable_mapping = Hashtbl.create 100;
      control_point_count = 0;
      hedge_count = 0;
      g = PSHGraph.create PSHGraph.stdcompare 3 ();
      apply = (fun _ _ _ -> raise Unknown_hedge);
      env = ();
      loop_invariants = []; }
    in
    cfg

  (* Adds a new node to the cfg, associated to expr (which is only useful for
   * debugging purpose ATM) *)
  let new_node_cfg cfg ?label:(l="") expr =
    let i = cfg.control_point_count in
    Hashtbl.add cfg.expr_to_control_point expr i;
    cfg.control_point_count <- i + 1;
    (* save in the cfg *)
    PSHGraph.add_vertex cfg.g i ();
    (* debug *)
    begin
      match debug_fmt with
      | Some debug_fmt ->
        Format.fprintf debug_fmt "%d [label=\"" i;
        if l <> "" then
          Format.fprintf debug_fmt "%s" l
        else
          Expr.print_expr debug_fmt expr;
        Format.fprintf debug_fmt "\"];@.";
      | None -> ()
    end;
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
        let abs = D.push_label man () h abs in
        (), f man abs
      else old_apply man h tabs
    end;
    match debug_fmt with
    | Some debug_fmt ->
      Format.fprintf debug_fmt "%d -> %d@." a b
    | None -> ()

  exception Not_handled of Term.term

  let warning_t s t =
    Format.eprintf "-- warning: %s -- triggered by " s;
    Pretty.print_term Format.err_formatter t;
    Format.eprintf " of type ";
    Pretty.print_ty Format.err_formatter (Term.t_type t);
    Format.eprintf "@."
            
  let create_postcondition_equality cfg manpk psym vreturn =
    if not Ity.(ity_equal  psym.pv_ity ity_unit) then
      begin
        let postcondition = 
            t_app ps_equ [t_var Ity.(psym.pv_vs);(t_var vreturn)] None in
        if Debug.test_flag ai_cfg_debug then
          begin
            Format.eprintf "--> Postcondition for let: ";
            Pretty.print_term Format.err_formatter postcondition;
            Format.eprintf "@.";
          end;
        D.meet_term manpk postcondition
      end
    else
      (fun abs -> abs)

  let create_postcondition cfg manpk psym =
    if not Ity.(ity_equal  psym.pv_ity ity_unit) then
      begin
        let ty = Term.(Ity.(psym.pv_vs.vs_ty) ) in

        let vreturn = create_vreturn manpk ty in
        create_postcondition_equality cfg manpk psym vreturn, D.forget_var manpk vreturn
      end
    else
      (fun abs -> abs), (fun abs -> abs)


  let remove_eps ?ret:(ret=None) manpk t =
    match t.t_node with
    | Teps(tb) ->
      let return, t = Term.t_open_bound tb in
      (* Always use the same variable when returning a value, 
       * otherwise variables keep being created and the previous ones (with the
       * good constraints) can not be accessed *)
      if Ty.ty_equal return.vs_ty Ity.ty_unit then
        t
      else
        begin
          match ret with
          | None ->
            let return_var = create_vreturn manpk (return.vs_ty) in
            let return_term = t_var return_var in
            t_subst_single return return_term t
          | Some v -> t_subst_single return (t_var v) t
        end
    | _ ->
      t


  (* Adds expr to the cfg. manpk is the types of the locally defined variable
   * (useful for references, when we need to get the type of a term in a logical formula).
   *
   * Adds multiple node and edges if expr requires so.
   *
   * returns a tuple, whose first element is the entry point of expr in the cfg, and the second
   * one is the ending point. The result of expr is stored is the variable "result"
   * (see var_return) *)
  let rec put_expr_in_cfg cfg (manpk:D.man) ?ret:(ret=None) expr =
    let open Expr in
    match expr.e_node with
    | Epure (t) ->
      let i, j = new_node_cfg cfg expr, new_node_cfg cfg expr in
      let vreturn = match ret with
        | None -> create_vreturn manpk (t_type t)
        | Some v -> v
      in
      let postcondition = t_app ps_equ [t_var vreturn; t] None in
      let constraints = D.meet_term manpk postcondition in
      new_hedge_cfg cfg (i, j) (fun _ abs ->
          constraints abs);
      i, j, []

    | Elet(LDvar(psym, let_expr), b) ->
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
      D.add_variable_to_env manpk psym;
      let let_begin_cp, let_end_cp, let_exn = put_expr_in_cfg ~ret:(Some Ity.(psym.pv_vs)) cfg manpk let_expr in

      (*let forget_ret = D.forget_var manpk cfg.env (create_vreturn Ity.(ty_of_ity (psym.pv_ity))) in*)

      (* compute the child and add an hyperedge, to set the value of psym
       * to the value returned by let_expr *)
      let b_begin_cp, b_end_cp, b_exn = put_expr_in_cfg ~ret cfg manpk b in


      (* Save the effect of the let *)
      new_hedge_cfg cfg (let_end_cp, b_begin_cp) (fun man abs ->
          abs
        );

      let end_cp = new_node_cfg cfg expr in
      (* erase a *)
      let forget_fun = D.forget_var manpk Ity.(psym.pv_vs) in
      new_hedge_cfg cfg (b_end_cp, end_cp) (fun man abs ->
          forget_fun abs
        );
      let_begin_cp, end_cp, let_exn @ b_exn

    | Evar(psym) ->
      let constraints =
        if not Ity.(ity_equal  psym.pv_ity ity_unit) then
          begin
          let ty = Term.(Ity.(psym.pv_vs.vs_ty) ) in

          let vreturn = match ret with
            | None -> create_vreturn manpk ty
            | Some v -> v
          in
          let postcondition = Term.( 
              t_app ps_equ [t_var Ity.(psym.pv_vs);(t_var vreturn)] None) in

          if Debug.test_flag ai_cfg_debug then
            begin
              Format.eprintf "--> Postcondition for var: ";
              Pretty.print_term Format.err_formatter postcondition;
              Format.eprintf "@.";
            end;
          D.meet_term manpk postcondition
          end
        else
          (fun abs -> abs)
      in

      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg ~label:"value returned" expr in
      new_hedge_cfg cfg (begin_cp, end_cp) (fun _ abs ->
          constraints abs
        );
      begin_cp, end_cp, []
    | Econst(n) ->
      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg ~label:"constant returned" cfg expr in

      let vreturn = match ret with
        | None -> create_vreturn manpk Ty.ty_int
        | Some v -> v
      in
      let postcondition = t_app ps_equ [t_const n; t_var vreturn] None in
      let constraints = D.meet_term manpk postcondition in

      new_hedge_cfg cfg (begin_cp, end_cp) (fun _ abs ->
          constraints abs
        );
      begin_cp, end_cp, []
    | Eexec({c_node = Capp(rsym, _); _}, { Ity.cty_post = post; Ity.cty_effect = effect;  Ity.cty_oldies = oldies; _ }) ->
      let eff_write = Ity.(effect.eff_writes) in
      let vars_to_forget, constraint_copy_ghost = Ity.Mpv.fold_left (
          fun (vars_to_forget, constraints) k b ->
            D.add_variable_to_env manpk k;
            let new_constraints = create_postcondition_equality cfg manpk b Ity.(k.pv_vs) in
            let forget_var = D.forget_var manpk Ity.(k.pv_vs) in
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
        |> List.fold_left Term.t_and Term.t_true
        |> D.meet_term manpk
      in
      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg ~label:"function called" cfg expr in
          
      let forget_writes = Ity.Mreg.fold_left (fun constr a b ->

          let forget = D.forget_region manpk a b in
          (fun x ->
             constr x |> forget)
        ) (fun x -> x) eff_write in

      new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
          constraint_copy_ghost abs  |> forget_writes |> constraints |> vars_to_forget
        );
      (* FIXME: handle exceptions *)
      begin_cp, end_cp, []
    | Ewhile(cond, _, _, content) ->
      (* Condition expression *)
      let cond_term, cond_term_not = 
        match Expr.term_of_expr ~prop:true cond with
        | Some s ->
          s, t_not s
        | None ->
          Format.eprintf "warning, condition in while could not be translated to term, an imprecise invariant will be generated";
          Term.t_true, Term.t_true
      in
      let constraints = D.meet_term manpk cond_term in

      let before_loop_cp = new_node_cfg cfg cond in
      cfg.loop_invariants <- (expr, before_loop_cp) :: cfg.loop_invariants;
      let start_loop_cp, end_loop_cp, loop_exn = put_expr_in_cfg cfg manpk content in
      let after_loop_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (before_loop_cp, start_loop_cp) (fun _ abs ->
          constraints abs
        );
      new_hedge_cfg cfg (before_loop_cp, after_loop_cp) (fun _ abs ->
          (* TODO *)
          abs
        );
      new_hedge_cfg cfg (end_loop_cp, before_loop_cp) (fun _ abs ->
          abs
        );
      (* FIXME: exceptions while inside the condition *)
      before_loop_cp, after_loop_cp, loop_exn
    | Etry(e, exc) ->
      let additional_exn = ref [] in
      let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg ~ret cfg manpk e in
      let i = new_node_cfg cfg expr in
      let exc = Ity.Mexn.map (fun (l, e) ->
          List.iter (fun p ->
              D.add_variable_to_env manpk p) l;

          let before_assign_cp = new_node_cfg cfg e in

          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg ~ret cfg manpk e in

          additional_exn := e_exn @ !additional_exn;

          begin
            match l with
            | [p] ->
              let constraints, forget_ret = create_postcondition cfg manpk p in
              new_hedge_cfg cfg (before_assign_cp, e_begin_cp) (fun _ abs ->
                  constraints abs |> forget_ret
                );

              let to_forget = D.forget_var manpk Ity.(p.pv_vs) in
              new_hedge_cfg cfg (e_end_cp, i) (fun _ abs ->
                  to_forget abs
                );
            | _ -> Format.eprintf "Multiple constructors exception, not handled by AI.";
              new_hedge_cfg cfg (before_assign_cp, e_begin_cp) (fun _ abs -> abs);
              new_hedge_cfg cfg (e_end_cp, i) (fun _ abs -> abs);
          end;
          l, before_assign_cp, e_end_cp
          ) exc in
      
      let e_exn = Ity.Mexn.fold (fun exc_sym (_, cp_begin, _) e_exn ->
          List.filter (fun (cp, exc_sym_) ->
              if Ity.xs_equal exc_sym exc_sym_ then
                begin
                  new_hedge_cfg cfg (cp, cp_begin) (fun _ abs ->
                       abs
                    );
                  false
                end
              else
                true
            ) e_exn) exc e_exn in
      new_hedge_cfg cfg (e_end_cp, i) (fun _ abs ->
          abs
        );
      e_begin_cp, i, !additional_exn @ e_exn
    | Eraise(s, e) ->
      let arg_begin, arg_end_cp, arg_exn = put_expr_in_cfg cfg manpk e in
      let j = new_node_cfg cfg expr in
      let k = new_node_cfg cfg expr in
      new_hedge_cfg cfg (j, k) (fun man _ ->
          D.bottom man ());
      arg_begin, k, ((arg_end_cp, s)::arg_exn)

    | Eif(cond, b, c) ->
      (* Condition expression *)
      let cond_term, not_cond_term = 
        match Expr.term_of_expr ~prop:true cond with
        | Some s ->
          s, t_not s
        | None ->
          Format.eprintf "warning, condition in if could not be translated to term (not pure), an imprecise invariant will be generated@.";
          Expr.print_expr Format.err_formatter cond;
          Format.eprintf "@.";
          Term.t_true, Term.t_true
      in
      let constraints = D.meet_term manpk cond_term in
      let constraints_not = D.meet_term manpk not_cond_term in
      let b_begin_cp, b_end_cp, b_exn = put_expr_in_cfg ~ret cfg manpk b in
      let c_begin_cp, c_end_cp, c_exn = put_expr_in_cfg ~ret cfg manpk c in
      let start_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (start_cp, b_begin_cp) (fun _ abs ->
          constraints abs);
      new_hedge_cfg cfg (start_cp, c_begin_cp) (fun _ abs ->
          constraints_not abs);
      new_hedge_cfg cfg (c_end_cp, end_cp) (fun _ abs ->
          abs);
      new_hedge_cfg cfg (b_end_cp, end_cp) (fun _ abs ->
          abs);
      start_cp, end_cp, b_exn @ c_exn
    | Ecase(case_e, l) ->
      let case_e_begin_cp, case_e_end_cp, case_e_exn = put_expr_in_cfg cfg manpk case_e in
      let e_exns = ref [case_e_exn] in
      let case_end_cp = new_node_cfg cfg expr in
      List.iter (fun (p, e) ->
          let open Term in
          let open Expr in
          let constraints, to_forget_before, to_forget_end = match p.pp_pat.pat_node with
            | Pwild -> (fun abs -> abs), (fun abs -> abs), (fun x -> x)
            | Pvar(_) -> failwith "pattern"
            | Papp(l, p) ->
              let args = List.map (fun p -> match p.pat_node with
                  | Pvar(vsym) ->
                    let pv = Ity.restore_pv vsym in
                    D.add_variable_to_env manpk pv;
                    vsym
                  | Pwild ->
                    create_vreturn manpk p.pat_ty
                  | _ -> failwith "nested pattern or worse"
                ) p in
              let matched_term = t_app l (List.map t_var args) (Some (Ity.ty_of_ity (case_e.e_ity))) in
              let vreturn = match ret with
                | None -> create_vreturn manpk (t_type matched_term)
                | Some v -> v
              in
              let postcondition =
                  t_app ps_equ [matched_term; t_var vreturn] None in
              let constr = D.meet_term manpk postcondition
              in
              constr, D.forget_var manpk vreturn, (List.fold_left (fun c arg ->
                  fun x -> c x |> D.forget_var manpk arg) (fun x -> x) args)

            | Por(_) -> failwith "pattern or"
            | Pas(_) -> failwith "pattern as"
          in
          let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg manpk e in
          new_hedge_cfg cfg (case_e_end_cp, e_begin_cp) (fun man abs ->
              constraints abs |> to_forget_before
            );
          new_hedge_cfg cfg (e_end_cp, case_end_cp) (fun man abs ->
              to_forget_end abs
            );
          e_exns := e_exn :: !e_exns;
        ) l;
      case_e_begin_cp, case_end_cp, (List.concat !e_exns)
    | Eassert(_) | Eabsurd -> (* FIXME: maybe they could be taken into account *)
      let i = new_node_cfg cfg expr in

      i, i, []

    | Eghost(e) -> put_expr_in_cfg ~ret cfg manpk e

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
        Ity.(t_var k.pv_vs, t_var lo.pv_vs, t_var up.pv_vs)
      in
      D.add_variable_to_env manpk k;

      let before_loop_cp = new_node_cfg cfg expr in
      let start_loop_cp = new_node_cfg cfg expr in
      cfg.loop_invariants <- (expr, start_loop_cp) :: cfg.loop_invariants;
      let e_begin_cp, e_end_cp, e_exn = put_expr_in_cfg cfg manpk e in
      let end_loop_cp = new_node_cfg cfg expr in

      let postcondition_before = t_app ps_equ [k_term; lo] None in
      let constraints_start = D.meet_term manpk postcondition_before in

      let precondition_e =
        if dir = Expr.To then
          t_and (t_app le_int [lo; k_term] None) (t_app le_int [k_term; up] None)
        else
          t_and (t_app le_int [up; k_term] None) (t_app le_int [k_term; lo] None)
      in
      let constraints_e = D.meet_term manpk precondition_e in

      let postcondition =
          t_app ps_equ [k_term; up] None
      in
      let constraints_post = D.meet_term manpk postcondition in

      new_hedge_cfg cfg (before_loop_cp, start_loop_cp) (fun _ -> constraints_start);
      new_hedge_cfg cfg (start_loop_cp, e_begin_cp) (fun _ -> constraints_e);
      let vret_k = create_vreturn manpk Ty.ty_int in
      let forget_vret = D.forget_var manpk vret_k in
      let forget_k = D.forget_var manpk Ity.(k.pv_vs) in
      let res = t_app ad_int [k_term; Term.t_const ( Number.ConstInt (Number.int_const_bin "1"))] (Some Ty.ty_int) in
      let next_assignation = t_app ps_equ [t_var vret_k; res] None |> D.meet_term manpk in
      let vret_equal = t_app ps_equ [t_var vret_k; k_term] None |> D.meet_term manpk in
      new_hedge_cfg cfg (e_end_cp, start_loop_cp) (fun man abs ->
          (* vret = k + 1, forget k, k = vret, forget vret *)
          next_assignation abs |> forget_k |> vret_equal |> forget_vret
        );
      new_hedge_cfg cfg (start_loop_cp, end_loop_cp) (fun man abs ->
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
    let constraints = D.meet_term manpk (t_and_l pre) in
    new_hedge_cfg cfg (i, e_start_cp) (fun _ -> constraints);
    i, e_end_cp, e_exn

  module Apron_to_term = Apron_to_term.Apron_to_term (E)
  let domain_to_term cfg manpk domain =
    D.to_term manpk domain

  let vertex_dummy = -1
  (** dummy value *)
  let hedge_dummy= -1
  (** dummy value *)


  (** {2 The fixpoint manager } *)

  let dot_file = open_out "t.dot";;
  let dot_fmt = Format.formatter_of_out_channel dot_file;;

  let get_fixpoint_man cfg man =
    let (manager:(int,int, D.t,unit) Fixpoint.manager) = {
      Fixpoint.bottom = begin fun _ -> D.bottom man () end;
      Fixpoint.canonical = begin fun _ abs -> D.canonicalize man abs end;
      Fixpoint.is_bottom = begin fun _ abs -> D.is_bottom man abs end;
      Fixpoint.is_leq = begin fun _ abs1 abs2 -> D.is_leq man abs1 abs2 end;
      Fixpoint.join = begin fun _ abs1 abs2 -> D.join man abs1 abs2 end;
      Fixpoint.join_list = begin fun _ labs -> D.join_list man labs end;
      Fixpoint.widening = begin fun _ abs1 abs2 -> D.widening man abs1 abs2 end;
      Fixpoint.odiff = None;
      Fixpoint.apply = cfg.apply man;
      Fixpoint.arc_init = begin fun _ -> () end;
      Fixpoint.abstract_init=
        begin fun vertex ->
          if vertex=0 then D.top man cfg.env else D.bottom man cfg.env
        end;

      Fixpoint.print_abstract = D.print;
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
      Fixpoint.dot_vertex = (fun fmt v -> Format.fprintf fmt "v%i@." v);
      Fixpoint.dot_hedge = (fun fmt h -> Format.fprintf fmt "h%i" h);
      Fixpoint.dot_attrvertex = (fun _ -> Format.printf "%d");
      Fixpoint.dot_attrhedge = (fun _ -> Format.printf "%d");
    }
    in manager
  
  
  let eval_fixpoints cfg manpk =
    begin
      let manager = get_fixpoint_man cfg manpk in
      let compare_no_closured = PSHGraph.stdcompare.PSHGraph.comparev in
      let sinit = PSette.singleton compare_no_closured 0 in
      let make_strategy =
        fun is_active ->
          Fixpoint.make_strategy_default
            ~widening_start:E.widening ~widening_descend:(max (E.widening/2) 2)
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
        (fun vtx abs ~pred:_ ~succ:_ ->
           l := (vtx, abs) :: !l);

      if Debug.test_flag ai_print_domains then
        begin
          let l = List.sort (fun (i, _) (j, _) -> compare i j) !l in
          List.iter (fun (vtx, abs) ->
             let t = D.to_term manpk abs in
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
              Format.printf "%a@." D.print abs;
              Pretty.forget_all ();
              Pretty.print_term Format.std_formatter (domain_to_term cfg manpk abs);
              printf "@."
            ) cfg.loop_invariants;

          match debug_fmt with
          | Some debug_fmt -> Format.fprintf debug_fmt "}@.";
          | None -> ()
        end;
      List.map (fun (expr, cp) ->
          let abs = PSHGraph.attrvertex output cp in
          expr, abs
        ) cfg.loop_invariants
    end

  let add_variable cfg a pvs =
    D.add_variable_to_env a pvs

end
