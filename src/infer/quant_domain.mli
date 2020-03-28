open Domain
open Ai_logic

module Make(S:sig
    module   TDom   : TERM_DOMAIN
    module Ai_logic : AI_LOGIC
  end) : TERM_DOMAIN
