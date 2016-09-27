
open Format
open Apron

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
let var_return = Var.of_string "$return"

(* Initialize an hedge *)
let start_cfg rs =
  { expr_to_control_point = Hashtbl.create 100;
    control_point_count = 0;
    hedge_count = 0;
    g = PSHGraph.create PSHGraph.stdcompare 3 ();
    apply = (fun _ _ a -> raise Unknown_hedge);
    env = Environment.make [|var_return|] [||]; }

let vs_to_var vs =
  Var.of_string Ident.(Term.(vs.vs_name.id_string))

let pv_to_var psym =
  vs_to_var Ity.(psym.pv_vs)

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

exception Not_handled

let linear_expressions_from_term cfg t =
  let open Term in

  match t.t_node with
  | Teps(tb) ->
    let return, t = Term.t_open_bound tb in

    let rec aux t =
      try
        match t.t_node with
        | Tbinop(Tand, a, b) ->
          aux a @ aux b
        | Tapp(func, args) ->

          let cst = ref 0 in
          let constr = ref [] in
          if ls_equal ps_equ func then
            match args with
            | [a; b] ->
              let term_to_int coeff t = match t.t_node with
                | Tvar(a) ->
                  begin
                  let var = vs_to_var a in
                  try
                    let c = List.assoc var !constr in
                    constr := (var, c+coeff) :: (List.remove_assoc var !constr);
                  with
                  | Not_found ->
                    constr := (var, coeff) :: !constr
                  end
                | _ -> raise Not_handled
              in
              term_to_int 1 a; term_to_int (-1) b;
              let expr = Linexpr1.make cfg.env in
              let constr = List.map (fun (var, coeff) ->
                  Coeff.Scalar (Scalar.of_int coeff), var) !constr in
              Linexpr1.set_list expr constr None;
              let cons = Lincons1.make expr Lincons1.EQ in
              Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int !cst));
              [cons]
            | _ -> raise Not_handled
          else
            raise Not_handled

        | _ ->
          raise Not_handled
      with
      | Not_handled ->
        Format.eprintf "Couldn't understand the entire post condition: ";
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
        let let_begin_cp, let_end_cp = put_expr_in_cfg cfg let_expr in

        (* compute the child and add an hyperedge, to set the value of psym
         * to the value returned by let_expr *)
        let b_begin_cp, b_end_cp = put_expr_in_cfg cfg b in
        (* Save the effect of the let *)
        new_hedge_cfg cfg (let_end_cp, b_begin_cp) (fun man abs ->
            let expr = Linexpr1.make cfg.env in
            Linexpr1.set_list expr [(one, var_return)] (Some(zero));
            let p = pv_to_var psym in
            Abstract1.assign_linexpr man abs p expr None
          );
        let_begin_cp, b_end_cp
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
        let constraints =
          List.map (linear_expressions_from_term cfg) post
          |> List.concat
        in
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

let eval_fixpoints cfg = ()

let get_domain cfg control_point = ()

let domain_to_logic domain = ()

let domain_to_string domain = ""


(* Define the two APRON variables we are about to use *)
let var_x = Var.of_string "x";;
let var_y = Var.of_string "y";;

(* Define the APRON environment *)
let env = Environment.make
  [|var_x; var_y|] (* integer variables *)
  [||] (* real variables *)
;;

(* Define the application function for each edge of the hyper graph
    i.e. how to label the hyper edges
*)
let apply man hedge tabs =
  let abs = tabs.(0) in
  let nabs hedge =
    let zero = Coeff.Scalar (Scalar.of_int 0) and
    one = Coeff.Scalar (Scalar.of_int 1)  and
    neg_one = Coeff.Scalar (Scalar.of_int (-1))
    in
    let expr = Linexpr1.make env in
    match hedge with
    | 01 -> (* x = 0; *)
      Linexpr1.set_list expr [(zero, var_x); (zero, var_y)] (Some(zero));
      Abstract1.assign_linexpr man abs var_x expr None
    | 12 -> (* y = 0; *)
      Linexpr1.set_list expr [(zero, var_x); (zero, var_y)] (Some(zero));
      Abstract1.assign_linexpr man abs var_y expr None
    | 23 -> (* -x >= -99; *)
      Linexpr1.set_list expr [(neg_one, var_x); (zero, var_y)] None;
      let cons = Lincons1.make expr Lincons1.SUPEQ in
      Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (99)));
      let cons_arr = Lincons1.array_make env 1 in
      Lincons1.array_set cons_arr 0 cons;
      Abstract1.meet_lincons_array man abs cons_arr;
    | 210 -> (* x >= 100 *)
      Linexpr1.set_list expr [(one, var_x); (zero, var_y)] None;
      let cons = Lincons1.make expr Lincons1.SUPEQ in
      Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (-100)));
      let cons_arr = Lincons1.array_make env 1 in
      Lincons1.array_set cons_arr 0 cons;
      Abstract1.meet_lincons_array man abs cons_arr;
    | 34 -> (* x := x+1 *)
      Linexpr1.set_list expr [(one, var_x); (zero, var_y)] (Some(one));
      Abstract1.assign_linexpr man abs var_x expr None
    | 45 -> (* -x >= -49; *)
      Linexpr1.set_list expr [(neg_one, var_x); (zero, var_y)] None;
      let cons = Lincons1.make expr Lincons1.SUPEQ in
      Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (49)));
      let cons_arr = Lincons1.array_make env 1 in
      Lincons1.array_set cons_arr 0 cons;
      Abstract1.meet_lincons_array man abs cons_arr;
    | 59 -> (* y := y+1 *)
      Linexpr1.set_list expr [(zero, var_x); (one, var_y)] (Some(one));
      Abstract1.assign_linexpr man abs var_y expr None
    | 47 -> (* x >= 50 *)
      Linexpr1.set_list expr [(one, var_x); (zero, var_y)] None;
      let cons = Lincons1.make expr Lincons1.SUPEQ in
      Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (-50)));
      let cons_arr = Lincons1.array_make env 1 in
      Lincons1.array_set cons_arr 0 cons;
      Abstract1.meet_lincons_array man abs cons_arr;
    | 79 -> (* y := y-1 *)
      Linexpr1.set_list expr [(zero, var_x); (one, var_y)] (Some(neg_one));
      Abstract1.assign_linexpr man abs var_y expr None
    | 92 -> abs
    | _ -> failwith ""
  in
  let arc_label = () in (arc_label, (nabs hedge))

let vertex_dummy =(-1);;
    (** dummy value *)
let hedge_dummy=(-1);;
    (** dummy value *)


(** {2 The fixpoint manager } *)

let dot_file = open_out "t.dot";;
let dot_fmt = Format.formatter_of_out_channel dot_file;;

let get_fixpoint_man man =
  let (manager:(int,int,'a Abstract1.t,unit) Fixpoint.manager) = {
    Fixpoint.bottom = begin fun vertex -> Abstract1.bottom man env end;
    Fixpoint.canonical = begin fun vertex abs -> Abstract1.canonicalize man abs end;
    Fixpoint.is_bottom = begin fun vertex abs -> Abstract1.is_bottom man abs end;
    Fixpoint.is_leq = begin fun vertex abs1 abs2 -> Abstract1.is_leq man abs1 abs2 end;
    Fixpoint.join = begin fun vertex abs1 abs2 -> Abstract1.join man abs1 abs2 end;
    Fixpoint.join_list = begin fun vertex labs -> Abstract1.join_array man (Array.of_list labs) end;
    Fixpoint.widening = begin fun vertex abs1 abs2 -> Abstract1.widening man abs1 abs2 end;
    Fixpoint.odiff = None;
    Fixpoint.apply = apply man;
    Fixpoint.arc_init = begin fun hedge -> () end;
    Fixpoint.abstract_init=
      begin fun vertex ->
	if vertex=0 then Abstract1.top man env else Abstract1.bottom man env
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
    Fixpoint.dot_vertex = (fun fmt v -> Format.printf "v%i" v);
    Fixpoint.dot_hedge = (fun fmt h -> Format.printf "h%i" h);
    Fixpoint.dot_attrvertex = (fun _ -> Format.printf "%d");
    Fixpoint.dot_attrhedge = (fun _ -> Format.printf "%d");
  }
  in manager
;;

(*
let essai1 man =
  let manager = get_fixpoint_man man in
  let compare_no_closured = PSHGraph.stdcompare.PSHGraph.comparev in
  let sinit = PSette.singleton compare_no_closured 0 in
  let strategy = Fixpoint.make_strategy_default
    ~widening_start:1 ~widening_descend:2
    ~vertex_dummy ~hedge_dummy
    g sinit in
  printf "strategy=%a@." (Fixpoint.print_strategy manager) strategy;

  let output = Fixpoint.analysis_std manager g sinit strategy in
  printf "output=%a@." (Fixpoint.print_output manager) output;
  printf "\n\nRESULT:\n";
  PSHGraph.iter_vertex output
    (begin fun vtx abs ~pred ~succ ->
      printf "\tacc(%i) = %a@."
	vtx (Abstract1.print) (abs)
     end)
  ;
  ()

let essai2 man =
  let manager = get_fixpoint_man man in
  let compare_no_closured = PSHGraph.stdcompare.PSHGraph.comparev in
  let sinit = PSette.singleton compare_no_closured 0 in
  let make_strategy =
    fun is_active ->
      Fixpoint.make_strategy_default
	~widening_start:1 ~widening_descend:2
	~priority:(PSHGraph.Filter is_active)
	~vertex_dummy ~hedge_dummy
	g sinit
  in
  let output = Fixpoint.analysis_guided
    manager g sinit make_strategy
  in
  printf "output=%a@." (Fixpoint.print_output manager) output;
  PSHGraph.iter_vertex output
    (begin fun vtx abs ~pred ~succ ->
      printf "acc(%i) = %a@."
	vtx (Abstract1.print) abs
    end)
  ;
  ()

let essai3 man =
  let manager = get_fixpoint_man man in
  let compare_no_closured = PSHGraph.stdcompare.PSHGraph.comparev in
  let sinit = PSette.singleton compare_no_closured 0 in
  let equation = Fixpoint.equation_of_graph g in
  let make_strategy (graph:(int,int,'a,'b,'c) PSHGraph.t) =
    Fixpoint.make_strategy_default
      ~widening_start:1 ~widening_descend:2
      ~vertex_dummy ~hedge_dummy graph sinit
  in
  let output = Fixpoint.analysis_dyn
    PSHGraph.stdcompare
    ~guided:false
    manager equation sinit make_strategy
  in
  printf "output=%a@." (Fixpoint.print_output manager) output;
  PSHGraph.iter_vertex output
    (begin fun vtx abs ~pred ~succ ->
      printf "acc(%i) = %a@."
	vtx (Abstract1.print) abs
    end)
  ;
  ()

let launch () =
  essai3 manpk;
  ()
*)
