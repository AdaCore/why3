
open Why
open Util
open Ident
open Ty
open Theory
open Term
open Decl

(* types *)

type effect = Pgm_effect.t
type reference = Pgm_effect.reference

type pre = Term.fmla

type post_fmla = Term.vsymbol (* result *) * Term.fmla
type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla

type post = post_fmla * (Term.lsymbol * exn_post_fmla) list

type type_v = private
  | Tpure of Ty.ty
  | Tarrow of binder list * type_c

and type_c =
  { c_result_type : type_v;
    c_effect      : effect;
    c_pre         : pre;
    c_post        : post; }

and binder = Term.vsymbol * type_v

val tpure : Ty.ty -> type_v
val tarrow : binder list -> type_c -> type_v

(* symbols *)

type psymbol = private {
  p_ls : lsymbol;
  p_tv : type_v;
}

val create_psymbol : preid -> type_v -> psymbol

type esymbol = lsymbol

(* program types -> logic types *)

val ts_arrow : tysymbol

val purify : type_v -> ty

(* operations on program types *)

val apply_type_v     : type_v -> vsymbol   -> type_c
val apply_type_v_ref : type_v -> reference -> type_c

val occur_type_v : reference -> type_v -> bool

val v_result : ty -> vsymbol
val exn_v_result : Why.Term.lsymbol -> Why.Term.vsymbol option

val post_map : (fmla -> fmla) -> post -> post

val subst1 : vsymbol -> term -> term Mvs.t

val eq_type_v : type_v -> type_v -> bool

(* pretty-printers *)

val print_type_v : Format.formatter -> type_v -> unit
val print_type_c : Format.formatter -> type_c -> unit
val print_post   : Format.formatter -> post   -> unit

