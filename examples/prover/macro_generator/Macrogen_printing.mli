
open Format
open Macrogen_params
open Macrogen_decls

include module type of Macrogen_printing_sig

module Helper : functor (P0:Parameters) -> HelperType

module MakePP : functor (P0:Parameters) -> PrintParameters with module P = P0



