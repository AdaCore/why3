
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

let extract_fields variable_type = 
  let open Ity in
  match Ity.(variable_type.ity_node) with
  | Ity.Ityvar(_) -> []
  | Ity.Ityreg({reg_args = a; reg_regs = b; reg_name = n; reg_its = its }) ->
    begin
      match its with
      | { its_mfields = fldl; _ } ->
        let open Term in
        let open Ident in
        List.map (fun p ->
            try
              Hashtbl.find hc p
            with
            | Not_found ->
                let r = Expr.create_projection its p in
                let varinst = Ity.its_match_args its a in
                let ity = Expr.(r.rs_cty.cty_result) in
                let ity = Ity.ity_full_inst varinst ity in
                Expr.print_rs Format.err_formatter r;
                let res = p, r, ity in
                Hashtbl.add hc p res;
                res) fldl
    end
  | Ity.Ityapp(its, a, b) -> []

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
      region_ident: Ity.pvsymbol Ity.Mreg.t
  }

  let empty_local_ty = { ident_ty = Ident.Mid.empty; region_ident = Ity.Mreg.empty }

  exception Unknown_hedge

  (* Some useful constants to express return values and linear expressions *)
  let zero = Coeff.Scalar (Scalar.of_int 0) 
  let one = Coeff.Scalar (Scalar.of_int 1)
  let neg_one = Coeff.Scalar (Scalar.of_int (-1))
  let var_return = Var.of_string "result"

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

  let var_of_field_region cfg reg t (c, a, ity_field) =
    ignore (Format.flush_str_formatter ());
    Ity.print_pv Format.str_formatter c;
    Format.fprintf Format.str_formatter "(";
    Ity.print_reg_name Format.str_formatter reg;
    Format.fprintf Format.str_formatter ")";
    let s = Format.flush_str_formatter () in
    let v = Var.of_string s in
    let unwrap = function
      | Some s -> s
      | None -> raise Not_found
    in
    let t = unwrap (Expr.term_of_expr (Expr.e_exec @@  Expr.c_app a [t] [] ity_field) ~prop:false) in
    ensure_variable cfg v t;
    v

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

  let unepsilon_term var_string = 7

  exception Not_handled of Term.term

  let th_int = Env.read_theory E.env ["int"] "Int"
  let le_int = Theory.(ns_find_ls th_int.th_export ["infix <="])
  let ge_int = Theory.(ns_find_ls th_int.th_export ["infix >="])
  let lt_int = Theory.(ns_find_ls th_int.th_export ["infix <"])
  let gt_int = Theory.(ns_find_ls th_int.th_export ["infix >"])
  let ad_int = Theory.(ns_find_ls th_int.th_export ["infix +"])
  let min_int = Theory.(ns_find_ls th_int.th_export ["infix -"])
  let min_u_int = Theory.(ns_find_ls th_int.th_export ["prefix -"])

  (* Get a set of (apron) linear expressions from a constraint stated in why3 logic.
   * ATM it only works for conjunction, and if there is not that much uninterpreted function.
   * In the worst case, it returns an empty list.
   *
   * The resulting list of linear expressions is weaker than the original why3
   * formula. *)
  let linear_expressions_from_term: cfg -> local_ty -> Term.term -> (domain -> domain)  = fun cfg local_ty t ->
    let open Term in

    (* First inline everything, for instance needed for references
     * where !i is (!) i *)
    let t = t_replace_all t in
    let return_var = ref None in

    (* Assuming that t is an arithmetic term, this computes the number of ocurrence of variables
     * to constr, and set cst to the constant of the arithmetic expression.
     * constr is a reference of list of (var, number_of_ocurrence).
     *
     * For instance, 4 + x + y set cst to 4, and constr to [(x, 1), (y, 1)]
     * *)
    let rec term_to_int coeff cst constr t = match t.t_node with
      | Tvar(a) ->
        begin
          let var =
            match !return_var with
            | Some s when Term.vs_equal a s -> var_return
            | _ -> vs_to_var a
          in
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
      | Tapp(func, [a;b]) when Term.ls_equal func min_int ->
        term_to_int coeff cst constr a; term_to_int (-coeff) cst constr b;
      | Tapp(func, [a]) when Term.ls_equal func min_u_int ->
        term_to_int (-coeff) cst constr a;
      | Tapp(func, [arg]) -> (* record access *)
        let rec term_to_string t = match t.t_node with
          | Tapp(func, [arg]) ->
            begin

              (* this check might not be needed, as everyting is supposed to
               * have been inlined *)
              match (Ident.Mid.find func.ls_name known_logical_ident).Decl.d_node with
              | Decl.Ddata(_) ->
                begin
                  try
                    ignore (Format.flush_str_formatter ());
                    let rs = Expr.restore_rs func in
                    let pv = match Expr.(rs.rs_field) with
                      | Some p -> p
                      | None -> raise Not_found
                    in
                    Ity.print_pv Format.str_formatter pv;
                    let func_str = (Format.flush_str_formatter ()) in
                    Format.sprintf "%s(%s)" func_str (term_to_string arg)
                  with
                  | Not_found -> raise (Not_handled t)
                end
              | _ ->  raise (Not_handled t)
            end
          | Tvar(a) ->
            begin
              try
                let ity = Ident.Mid.find Term.(a.vs_name) local_ty.ident_ty in
                match Ity.(ity.ity_node) with
                | Ity.Ityreg(a) ->
                  ignore (Format.flush_str_formatter ());
                  Ity.print_reg_name Format.str_formatter a;
                  let func_str = (Format.flush_str_formatter ()) in
                  func_str
                | _ -> raise (Not_handled t)
              with
              | Not_found -> raise (Not_handled t)
            end
          | _ -> raise (Not_handled t)
        in
        let n = term_to_string t in
        let v = Var.of_string n in
        ensure_variable cfg v t;
        constr := (v, coeff) :: !constr
      | _ -> raise (Not_handled t)
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
        | Tapp(func, args) -> (* ATM, this is handled only for equality and integer comparison *)

          let cst = ref 0 in
          let constr = ref [] in
          (* FIXME: >, <=, >=, booleans *)
          if ls_equal ps_equ func ||
             ls_equal lt_int func ||
             ls_equal gt_int func ||
             ls_equal le_int func ||
             ls_equal ge_int func
          then
            match args with
            | [a; b] ->
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
              term_to_int (-base_coeff) cst constr a; term_to_int base_coeff cst constr b;
              let expr = Linexpr1.make cfg.env in
              let constr = List.map (fun (var, coeff) ->
                  Coeff.Scalar (Scalar.of_int coeff), var) !constr in
              Linexpr1.set_list expr constr None;
              let cons = Lincons1.make expr eq_type in
              Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int !cst));
              let arr = Lincons1.array_make cfg.env 1 in
              Lincons1.array_set arr 0 cons;
              (fun d ->
                 Abstract1.meet_lincons_array manpk d arr)
            | _ -> raise (Not_handled t)
          else
            raise (Not_handled t)
        | Tif(a, b, c) ->
          let fa = aux a in
          let fb = aux b in
          let fc = aux c in
          (fun d ->
             let d1 = fb (fa d) in
             let d2 = fc d in
             Abstract1.join manpk d1 d2)
        | Ttrue -> (fun d -> d)
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
      match t.t_node with
      | Teps(tb) ->
        let return, t = Term.t_open_bound tb in
        return_var := Some return;
        aux t
      | _ ->
        aux t
    with
    | e ->
      Format.eprintf "error while computing domain for post conditions: ";
      Pretty.print_term Format.err_formatter t;
      Format.eprintf "@.";
      raise e

  let add_typed_variable cfg local_ty psym variable_type =
    let variable_ident = (Ity.(Term.(psym.pv_vs.vs_name))) in
    let local_ty = { local_ty with ident_ty = Ident.Mid.add variable_ident variable_type local_ty.ident_ty } in
    match Ity.(variable_type.ity_node) with
    | Ity.Ityreg(reg) ->
      let fields = extract_fields variable_type in
      let vars = List.map (var_of_field_region cfg reg psym) fields in
      ignore vars;
      { local_ty with region_ident = Ity.Mreg.add reg psym local_ty.region_ident }
    | _ when Ity.(ity_equal variable_type ity_int) ->
      add_variable cfg psym;
      local_ty
    | _ when  extract_fields variable_type = [] -> local_ty
    | _ -> failwith "fields for a variable whose type is not a region?"


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
      let let_begin_cp, let_end_cp = put_expr_in_cfg cfg local_ty let_expr in

      let local_ty = add_typed_variable cfg local_ty psym variable_type in

      (* compute the child and add an hyperedge, to set the value of psym
       * to the value returned by let_expr *)
      let b_begin_cp, b_end_cp = put_expr_in_cfg cfg local_ty b in

      (* Save the effect of the let *)
      new_hedge_cfg cfg (let_end_cp, b_begin_cp) (fun man abs ->
          let abs =
            match Ity.(variable_type.ity_node) with
            | _ when Ity.(ity_equal variable_type ity_int) ->
              let expr = Linexpr1.make cfg.env in
              Linexpr1.set_list expr [(one, var_return)] (Some(zero));
              let p = pv_to_var psym in
              Abstract1.assign_linexpr man abs p expr None
            | _ -> abs
          in
          Abstract1.forget_array man abs [|var_return|] false
        );
      let end_cp = new_node_cfg cfg expr in
      (* erase a *)
      new_hedge_cfg cfg (b_end_cp, end_cp) (fun man abs ->
          match Ity.(variable_type.ity_node) with
          | _ when Ity.(ity_equal variable_type ity_int) ->
            Abstract1.forget_array man abs [|pv_to_var psym|] false
          | _ -> abs
        );


      let_begin_cp, end_cp
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
    | Eexec({c_node = Capp(rsym, args); _}, { Ity.cty_post = post; Ity.cty_result = ity; Ity.cty_effect = effect;  _ }) ->
      let eff_write = Ity.(effect.eff_writes) in

      (* Computing domain from postcondition *)
      Format.eprintf "Computing domain from postconditions for function: ";
      Expr.print_rs Format.err_formatter rsym;
      Format.eprintf "@.";
      let constraints =
        List.map (linear_expressions_from_term cfg local_ty) post
        |> List.fold_left (fun f a ->
            (fun d -> f (a d))) (fun x -> x)
      in
      List.iter (fun a ->
          Format.eprintf "  ->  ";
          Pretty.print_term Format.err_formatter a;
          Format.eprintf "@.";
        ) post;

      let begin_cp = new_node_cfg cfg expr in
      let end_cp = new_node_cfg cfg expr in
      new_hedge_cfg cfg (begin_cp, end_cp) (fun man abs ->
          (* effects *)
          let abs = ref (Abstract1.forget_array man abs [|var_return|] false) in
          ignore @@ Ity.Mreg.mapi (fun a b ->
              Ity.Mpv.mapi (fun c () ->
                  let open Ity in
                  let var = Ity.Mreg.find a local_ty.region_ident in
                  let proj = get_proj c in
                  let v = var_of_field_region cfg a var proj in
                  abs :=  Abstract1.forget_array man !abs [|v|] false; abs
                ) b;
            ) eff_write;

          constraints !abs
        );
      begin_cp, end_cp
    | Ewhile(cond, inv, var, content) ->
      let open Expr in
      begin
      match expr.e_loc  with
      | Some s ->
        let s, a, b, c = Loc.get s in
        Format.printf "%s, %d, %d, %d@." s a b c;
      | None -> ()
      end;

      (* Condition expression *)
      let cond_term = 
        match Expr.term_of_expr ~prop:true cond with
        | Some s ->
          s
        | None ->
          Format.eprintf "warning, condition in while could not be translated to term, an imprecise invariant will be generated";
          Term.t_true
      in
      let constraints = linear_expressions_from_term cfg local_ty cond_term in

      let before_loop_cp = new_node_cfg cfg cond in
      let start_loop_cp, end_loop_cp = put_expr_in_cfg cfg local_ty content in
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
      before_loop_cp, after_loop_cp
    (*| Etry(e, exc) ->
      Ity.Mexn.mapi (fun a b ->
          () ) exc;*)
    | _ ->
      Expr.print_expr Format.err_formatter expr;
      Format.eprintf "unhandled expr@.";

      let i = new_node_cfg cfg expr in

      i, i

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
    PSHGraph.iter_vertex output
      (begin fun vtx abs ~pred ~succ ->
         printf "acc(%i) = %a@."
           vtx (Abstract1.print) abs
       end);
    
 Hashtbl.iter (fun a b ->
        Format.eprintf "%d -> " b;
        Expr.print_expr Format.err_formatter a;
        Format.eprintf "@."
        ) cfg.expr_to_control_point;

    (* Print loop invariants *)

    Format.printf "Loop invariants:\n@.";

    (*List.iter (fun (expr, cp) ->
        Format.printf "For:@.";
        Expr.print_expr Format.std_formatter expr;
        Format.printf "@.";
        let abs = PSHGraph.attrvertex output cp in
        Format.printf "%a@." Abstract1.print abs;
      Pretty.forget_all ();
        Pretty.print_term Format.std_formatter (domain_to_term cfg abs);
        printf "@."
      ) cfg.loop_invariants;*)
    
    List.map (fun (expr, cp) ->
        let abs = PSHGraph.attrvertex output cp in
        expr, abs
      ) cfg.loop_invariants

end
