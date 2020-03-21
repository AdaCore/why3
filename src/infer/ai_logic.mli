open Apron
open Ident
open Term
open Decl


module type AI_LOGIC = sig

  type coeff
  type env

  exception Cannot_be_expressed
  exception Recursive_logical_definition

  val env : Env.env
  val known_logical_ident : known_map
  val known_pdecl : Pdecl.known_map
  val th_int : Theory.theory

  val le_int : lsymbol
  val ge_int : lsymbol
  val lt_int : lsymbol
  val gt_int : lsymbol

  val ad_int : lsymbol
  val min_int : lsymbol
  val min_u_int : lsymbol
  val mult_int : lsymbol
  val zero_int : term
  val one_int : term
  val int_add : term list -> term
  val int_minus_u : term list -> term
  val int_minus : term list -> term
  val int_mult : term list -> term

  val coeff_to_term : Coeff.union_5 -> coeff
  val varlist_to_term :
    ('a -> term) -> (Coeff.union_5 * 'a) list * Coeff.union_5 -> term
  val t_descend_nots : ?way:bool -> term -> term
  val find_global_definition : decl Mid.t -> lsymbol -> logic_decl option
  val find_definition : env -> Mls.key -> logic_decl option
  val t_unfold : 'a -> Mls.key -> term list -> Ty.ty option -> term
  val t_replace_all : term -> term
end

module Make(S : sig
         val       env : Env.env
         val  th_known : known_map
         val mod_known : Pdecl.known_map
       end) : AI_LOGIC
