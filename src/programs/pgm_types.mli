
open Why
open Ty
open Theory
open Term
open Decl

(* types *)

type effect = Pgm_effect.t

type pre = Term.fmla

type post_fmla = Term.vsymbol (* result *) * Term.fmla
type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla

type post = post_fmla * (Term.lsymbol * exn_post_fmla) list

type type_v = 
  | Tpure of Ty.ty
  | Tarrow of binder list * type_c

and type_c = 
  { c_result_type : type_v;
    c_effect      : effect;
    c_pre         : pre;
    c_post        : post; }

and binder = Term.vsymbol * type_v

type env = private {
  uc      : theory_uc;
  globals : type_v Mls.t;
  locals  : type_v Mvs.t;
  (* predefined symbols *)
  ts_arrow: tysymbol;
  ts_label: tysymbol;
  ts_ref  : tysymbol;
  ls_at   : lsymbol;
  ls_bang : lsymbol;
  ls_old  : lsymbol;
}

val ls_ref    : theory_uc -> lsymbol (* ref: 'a -> 'a ref *)
val ls_assign : theory_uc -> lsymbol (* := : 'a ref -> 'a -> unit *)

val purify : theory_uc -> type_v -> ty

val apply_type_v : env -> type_v -> vsymbol -> type_c

val empty_env : theory_uc -> env

val add_local : vsymbol -> type_v -> env -> env

val add_global : lsymbol -> type_v -> env -> env

val add_decl : decl -> env -> env

val v_result : ty -> vsymbol

val post_map : (fmla -> fmla) -> post -> post

val subst1 : vsymbol -> vsymbol -> term Mvs.t

(* pretty-printers *)

val print_type_v : Format.formatter -> type_v -> unit

