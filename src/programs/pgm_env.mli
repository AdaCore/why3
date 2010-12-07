
open Why
open Util
open Ident
open Ty
open Theory
open Term
open Decl


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
  ls_notb : lsymbol;
  ls_unit : lsymbol;
  ls_lt   : lsymbol;
  ls_gt   : lsymbol;
  ls_le   : lsymbol;
  ls_ge   : lsymbol;
  ls_add  : lsymbol;
}

val empty_env : theory_uc -> env

val add_global : preid -> type_v -> env -> lsymbol * env

val add_decl : decl -> env -> env

val logic_lexpr : Loc.position * string -> Ptree.lexpr

val logic_decls : Loc.position * string -> Env.env -> env -> env

val add_exception : preid -> ty option -> env -> lsymbol * env

val t_True : env -> term

val type_v_unit : env -> type_v

