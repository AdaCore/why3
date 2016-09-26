
open Format
open Apron

(* Apron manager *)
let manpk = Polka.manager_alloc_strict()

type control_point = int

type domain

type cfg = {
  expr_to_control_point: (Expr.expr, control_point) Hashtbl.t;
  mutable control_point_count: control_point;
  mutable vars: Var.t list;
}

let start_cfg rs =
  { expr_to_control_point = Hashtbl.create 100;
    control_point_count = 0;
    vars = []; }

let rec put_expr_in_cfg cfg expr =
  let open Expr in
  match expr.e_node with
  | Elet(LDsym(_), b) ->
    let i = cfg.control_point_count in
    cfg.control_point_count <- i + 1;
    put_expr_in_cfg cfg b
  | _ ->
    Format.eprintf "unhandled expr";
    cfg.control_point_count - 1

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

(** {2 The equation system, modelled as an hypergraph} *)

(* Creation of the following equation graph:
   X0: x=0;
   X1: y=0;
   X2: while (x<=99) do
   X3:   incr x;
   X4:   if (x<=49) then
   X5:     incr y;
	else
   X7      decr y;
	endif
   X9  done
   X10

*)

(* Define the structure of the hypergraph (wrt our code) *)
let initial_info = ();;
let (g:(int,int,unit,unit,unit) PSHGraph.t) = PSHGraph.create PSHGraph.stdcompare 10 initial_info;;

let attr_vertex = () and attr_hedge = () in
for i=0 to 10 do PSHGraph.add_vertex g i attr_vertex done;
PSHGraph.add_hedge g 01 attr_hedge ~pred:[|0|] ~succ:[|1|];
PSHGraph.add_hedge g 12 attr_hedge ~pred:[|1|] ~succ:[|2|];
PSHGraph.add_hedge g 23 attr_hedge ~pred:[|2|] ~succ:[|3|];
PSHGraph.add_hedge g 210 attr_hedge ~pred:[|2|] ~succ:[|10|];
PSHGraph.add_hedge g 34 attr_hedge ~pred:[|3|] ~succ:[|4|];
PSHGraph.add_hedge g 45 attr_hedge ~pred:[|4|] ~succ:[|5|];
PSHGraph.add_hedge g 59 attr_hedge ~pred:[|5|] ~succ:[|9|];
PSHGraph.add_hedge g 47 attr_hedge ~pred:[|4|] ~succ:[|7|];
PSHGraph.add_hedge g 79 attr_hedge ~pred:[|7|] ~succ:[|9|];
PSHGraph.add_hedge g 92 attr_hedge ~pred:[|9|] ~succ:[|2|];
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
	      begin
		Linexpr1.set_list expr [(zero, var_x); (zero, var_y)] (Some(zero));
		Abstract1.assign_linexpr man abs var_x expr None
	      end;
      | 12 -> (* y = 0; *)
	      begin
		Linexpr1.set_list expr [(zero, var_x); (zero, var_y)] (Some(zero));
		Abstract1.assign_linexpr man abs var_y expr None
	      end;
      | 23 -> (* -x >= -99; *)
	      begin
		Linexpr1.set_list expr [(neg_one, var_x); (zero, var_y)] None;
		let cons = Lincons1.make expr Lincons1.SUPEQ in
		begin
		  Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (99)));
		  let cons_arr = Lincons1.array_make env 1 in
		  begin
		    Lincons1.array_set cons_arr 0 cons;
		    Abstract1.meet_lincons_array man abs cons_arr;
		  end;
		end;
	      end;

      | 210 -> (* x >= 100 *)
	       begin
		 Linexpr1.set_list expr [(one, var_x); (zero, var_y)] None;
		 let cons = Lincons1.make expr Lincons1.SUPEQ in
		 begin
		   Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (-100)));
		   let cons_arr = Lincons1.array_make env 1 in
		   begin
		     Lincons1.array_set cons_arr 0 cons;
		     Abstract1.meet_lincons_array man abs cons_arr;
		   end;
		 end;
	       end;
      | 34 -> (* x := x+1 *)
	      begin
		Linexpr1.set_list expr [(one, var_x); (zero, var_y)] (Some(one));
		Abstract1.assign_linexpr man abs var_x expr None
	      end;
      | 45 -> (* -x >= -49; *)
	      begin
		Linexpr1.set_list expr [(neg_one, var_x); (zero, var_y)] None;
		let cons = Lincons1.make expr Lincons1.SUPEQ in
		begin
		  Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (49)));
		  let cons_arr = Lincons1.array_make env 1 in
		  begin
		    Lincons1.array_set cons_arr 0 cons;
		    Abstract1.meet_lincons_array man abs cons_arr;
		  end;
		end;
	      end;
    | 59 -> (* y := y+1 *)
	    begin
	      Linexpr1.set_list expr [(zero, var_x); (one, var_y)] (Some(one));
	      Abstract1.assign_linexpr man abs var_y expr None
	    end;
    | 47 -> (* x >= 50 *)
	       begin
		 Linexpr1.set_list expr [(one, var_x); (zero, var_y)] None;
		 let cons = Lincons1.make expr Lincons1.SUPEQ in
		 begin
		   Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int (-50)));
		   let cons_arr = Lincons1.array_make env 1 in
		   begin
		     Lincons1.array_set cons_arr 0 cons;
		     Abstract1.meet_lincons_array man abs cons_arr;
		   end;
		 end;
	       end;
    | 79 -> (* y := y-1 *)
	    begin
	      Linexpr1.set_list expr [(zero, var_x); (one, var_y)] (Some(neg_one));
	      Abstract1.assign_linexpr man abs var_y expr None
	    end;
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
