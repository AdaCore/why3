
open Why
open Theory

val file : theory_uc -> Pgm_ttree.file -> theory
  (** takes as input the result of [Pgm_typing.file] and produces
      a theory containing the verification conditions as goals,
      one for each function *)
