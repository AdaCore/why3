
(**

{1 Inference of loop invariants for WhyML code, using BDDinfer
   subcomponent}

*)

(*open Why3*) (* to comment out when inside Why3 *)


val infer_loop_invs_for_mlw_expr :
  Ident.Sattr.t ->
  Env.env ->
  Decl.known_map ->
  Pdecl.known_map ->
  Expr.expr -> Ity.cty -> (Expr.expr * Term.term) list
(** [infer_loop_invs_for_mlw_expr attrs env tkn mkn e cty] infers loop
   invariants for the given WhyML expression [e]. [e] is assumed to be
   the body of a WhyML function which attributes are [attrs] and
   computation type is [cty]. The other parameters [env], [tkn] and
   [mkn] are respectively the environment, the theory known map and
   the module known map of that function.

  The set [attrs] is checked for the presence of the [[@bddinfer]]
   attribute. Without it, the empty list is immediately returned.

  The environment [env] is needed to access the builtin functions such
   as the integer operators.

  The known maps [tkn] and [mkn] are needed to access to the contracts
   of the WhyML functions called inside [e].

  The type [cty] is needed to get the preconditions of the execution
   of [e].

  The returned list contains pairs [(ei,ti)] where the [ei] are each
   of the loops occuring inside [e] and [ti] is the corresonding loop
   invariant generated.

  The inference does not support the full WhyML language. If any
   unsupported feature is met, this function will just return the
   empty list. The reason should be queried using function
   [report_on_last_call] below.

 *)

type domains = Abstract.domain Term.Mvs.t

type engine_report = {
    engine_error : (string * string) option;
    (* An exception possibly raised by the engine *)
    engine_running_time : float;
    (* The cpu time spent in inference *)
    engine_num_bool_vars : int;
    (* The number of Boolean variables used *)
    engine_invariants_and_domains : (Term.term * domains) Wstdlib.Mstr.t;
    (* The invariants that were produced *)
    engine_subreport : Infer.interp_report option;
    (* The low-level report of inference sub-engine *)
  }

val report_on_last_call : unit -> engine_report
(** provides info about the last call *)

val report : verbosity:int -> engine_report -> unit
(** prints the report on standard output *)

val register_hook : (engine_report -> unit) -> unit
(** registers a function to be applied on the report *)
