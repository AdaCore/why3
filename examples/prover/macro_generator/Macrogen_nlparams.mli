
open Macrogen_params

include module type of Macrogen_nlparams_sig

module MakeDefaultP : functor(D0:Decls) -> NLParameters

