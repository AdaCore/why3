
module type Inv_gen = sig
  val infer_loop_invariants:
    ?widening:int -> Env.env -> Pmodule.pmodule -> Pmodule.pmodule
end

module Make (D: Domain.DOMAIN) : Inv_gen

module InvGenPolyhedra : Inv_gen
module InvGenBox       : Inv_gen
module InvGenOct       : Inv_gen
