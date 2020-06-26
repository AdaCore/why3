(** Several useful utilities to preprocess logic terms before analysing them
    for AI *)

open Apron
open Term
open Decl


module type INFERWHY3 = sig

  val env       : Env.env
  val th_known  : known_map
  val mod_known : Pdecl.known_map

  val le_int : lsymbol
  val ge_int : lsymbol
  val lt_int : lsymbol
  val gt_int : lsymbol

  val ad_int      : lsymbol
  val min_int     : lsymbol
  val min_u_int   : lsymbol
  val mult_int    : lsymbol
  val zero_int    : term
  val one_int     : term
  val int_add     : term list -> term
  val int_minus_u : term list -> term
  val int_minus   : term list -> term
  val int_mult    : term list -> term

  val varlist_to_term :
    ('a -> term) -> (Coeff.union_5 * 'a) list * Coeff.union_5 -> term

  val t_push_negation : term -> term
  (* push negations deeper in the term *)

  val t_inline_all : term -> term
  (* inline all lsymbols applications *)

end

module Make(S : sig
         val       env : Env.env
         val  th_known : known_map
         val mod_known : Pdecl.known_map
       end) : INFERWHY3
