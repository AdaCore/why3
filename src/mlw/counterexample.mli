
open Format
open Pinterp

val check_model : rac_reduce_config -> Env.env -> Pmodule.pmodule -> Model_parser.model -> check_model_result
(** [check_model env pm m] checks if model [m] is valid, i.e. the abstract
    execution using the model values triggers a RAC contradiction in the
    corresponding location. The function returns true if the corresponding
    program definition cannot be identified, or if there is an error during
    RAC execution.

    Optional arguments [rac_trans] and [rac_prover] as in [eval_global_fundef]. *)

type ce_summary

val print_counterexample : ?check_ce:bool -> formatter ->
                           Model_parser.model * ce_summary -> unit

val select_model : ?check:bool -> rac_reduce_config -> Env.env -> Pmodule.pmodule ->
('a * Model_parser.model) list -> (Model_parser.model * ce_summary) option
