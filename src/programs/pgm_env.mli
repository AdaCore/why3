
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

(* environments *)

type env = private {
  uc      : theory_uc;
  globals : (lsymbol * type_v) Mstr.t;
  exceptions : lsymbol Mstr.t;
  (* predefined symbols *)
  ts_arrow: tysymbol;
  ts_bool : tysymbol;
  ts_label: tysymbol;
  ts_ref  : tysymbol;
  ts_exn  : tysymbol;
  ts_unit : tysymbol;
  ls_at   : lsymbol;
  ls_bang : lsymbol;
  ls_old  : lsymbol;
  ls_True : lsymbol;
  ls_False: lsymbol;
  ls_andb : lsymbol;
  ls_orb  : lsymbol;
  ls_unit : lsymbol;
}

val empty_env : theory_uc -> env

val add_global : preid -> type_v -> env -> lsymbol * env

val add_decl : decl -> env -> env

val logic_lexpr : Lexing.position * string -> Ptree.lexpr

val logic_decls : Lexing.position * string -> Env.env -> env -> env

val add_exception : preid -> ty option -> env -> lsymbol * env

val t_True : env -> term

val type_v_unit : env -> type_v

val purify : env -> type_v -> ty

val apply_type_v     : env -> type_v -> vsymbol   -> type_c
val apply_type_v_ref : env -> type_v -> reference -> type_c

val occur_type_v : reference -> type_v -> bool

val v_result : ty -> vsymbol

val post_map : (fmla -> fmla) -> post -> post

val subst1 : vsymbol -> term -> term Mvs.t

val eq_type_v : type_v -> type_v -> bool


(* pretty-printers *)

val print_type_v : Format.formatter -> type_v -> unit
val print_type_c : Format.formatter -> type_c -> unit
val print_post   : Format.formatter -> post   -> unit
