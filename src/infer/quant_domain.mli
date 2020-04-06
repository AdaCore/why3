open Domain
open Infer_why3

module Make(S:sig
    module       TDom : TERM_DOMAIN
    module Infer_why3 : INFERWHY3
  end) : TERM_DOMAIN
