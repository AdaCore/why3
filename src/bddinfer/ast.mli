(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**

   {1 Abstract syntax trees}

TODO list:

- separate integer expressions and Boolean expressions in two
   different types

- do not use a separate type [atomic_condition]

*)

(** {2 Variables} *)

type var_type =
  | Tunit
  | Tint
  | Tbool

type label = Here | Old


(** {2 Expressions} *)

type expression = private
    | Evar of Abstract.why_var * label
    | Ecst of string
    | Eadd of expression * expression
    | Esub of expression * expression
    | Emul of expression * expression
    | Ediv of expression * expression
    | Emod of expression * expression
    | Ebwtrue
    | Ebwfalse
    | Ebwnot of expression
    | Ebwand of expression * expression
    | Ebwor of expression * expression

val e_var : Abstract.why_var -> label -> expression
val e_cst : string -> expression

val e_add : expression -> expression -> expression
val e_sub : expression -> expression -> expression
val e_mul : expression -> expression -> expression
val e_div : expression -> expression -> expression
val e_mod : expression -> expression -> expression

val e_bwtrue : expression
val e_bwfalse : expression

val bwnot_simp : expression -> expression
val bwand_simp : expression -> expression -> expression
val bwor_simp : expression -> expression -> expression

val e_let_in_expression : Abstract.why_var -> expression -> expression -> expression


(** {2 Conditions} *)

type atomic_condition = private
    | Ceq of expression * expression
    | Cne of expression * expression
    | Clt of expression * expression
    | Cle of expression * expression
    | Cgt of expression * expression
    | Cge of expression * expression
    | C_is_true of expression

val c_eq_int : expression -> expression -> atomic_condition
val c_ne_int : expression -> expression -> atomic_condition

val c_le : expression -> expression -> atomic_condition
val c_lt : expression -> expression -> atomic_condition
val c_ge : expression -> expression -> atomic_condition
val c_gt : expression -> expression -> atomic_condition

val c_is_true : expression -> atomic_condition
val c_is_false : expression -> atomic_condition

val c_eq_bool : expression -> expression -> atomic_condition
val c_ne_bool : expression -> expression -> atomic_condition


type condition = private
    | BTrue
    | BFalse
    | BAnd of condition * condition
    | BOr of condition * condition
    | BAtomic of atomic_condition
    | Bite of condition * condition * condition (* For printing only ! *)

val true_cond : condition
val false_cond : condition

val atomic_cond : atomic_condition -> condition

val neg_cond : condition -> condition
val or_cond : condition -> condition -> condition
val and_cond : condition -> condition -> condition

val e_let_in_condition : Abstract.why_var -> expression -> condition -> condition

val ternary_condition : condition -> condition -> condition -> condition

val ternary_condition_no_simpl : condition -> condition -> condition -> condition


(** {2 Statements} *)


type fun_id = private {
    fun_name : string;
    fun_tag : int;
  }

module FuncMap : Map.S with type key = fun_id

val create_fun_id : string -> fun_id

val print_fun_id : Format.formatter -> fun_id -> unit

type memo_env = Abstract.why_env * condition

type statement_node = private
    | Swhile of condition * (string option * condition) list * statement
    | Sfcall of (Abstract.why_var * statement * Abstract.var_value) option *
                (Abstract.why_var * Abstract.var_value * expression) list *
                fun_id * expression list * memo_env option ref *
                Abstract.memo_add_env option ref * Abstract.memo_add_env option ref *
                Abstract.memo_havoc option ref * statement option ref
    (** First argument is [None] for procedures. For functions
       returning values, the triple [(v,s,av)] denotes the program
       variable [v] in which the result is stored, the statement [s]
       to execute afterwards, in which [v] is bound, and an abstract
       variable [av] used when interpreting this call. Second argument
       is a list of local bindings for the arguments. *)
    | Site of condition * statement * statement
    | Sblock of statement list
    | Sassert of condition
    | Sassume of condition
    | Shavoc of Abstract.why_env * condition * Abstract.memo_havoc option ref
    (** first argument is the set of written variables, each of them
       being associated to an abstract variable needed during
       interpretation of this havoc instruction.*)
    | Sletin of Abstract.why_var * Abstract.var_value * expression * statement
    (** first argument is the bound variable, second argument is a fresh
       abstract value to be used for interpretation *)
    | Sbreak
    (** break statement inside loops *)

and statement = private {
    stmt_tag : string;
    stmt_node : statement_node;
  }

val mk_stmt : string -> statement_node -> statement
(** low-level constructor for statements, from statement nodes *)

val s_assign : string -> var_type -> Abstract.why_var -> expression -> statement
(** [s_assign t ty v e] builds the assignment statement [v : ty <- e] with tag [t] *)

val s_assert : string -> condition -> statement
(** [s_assert t c] builds the assertion statement [assert c] with tag [t] *)

val s_assume : string -> condition -> statement
(** [s_assume t c] builds the assumption statement [assume c] with tag [t] *)

val s_sequence : string -> statement -> statement -> statement

val s_block : string -> statement list -> statement
(** [s_block t [s1;..;sk]] builds the sequence of statements
   [s1;..;sk] with tag [t] *)

val s_ite : string -> condition -> statement -> statement -> statement
(** [s_ite t c e1 e2] builds the conditional statement [if c then e1
   else e2] with tag [t] *)

val s_while : string -> condition -> (string option * condition) list -> statement -> statement
(** [s_while t c invs e] builds the loop statement [while c do e] with
   tag [t] and a possibly empty list of user invariants [invs] *)

val s_call : string -> (var_type * Abstract.why_var * statement) option ->
             (var_type * Abstract.why_var * expression) list ->
             fun_id -> expression list -> statement
(** [s_call t None lets f el] builds the procedure call [f el], with
   tag [t]. [lets] is a list of local assignments of variables for the
   arguments [el].  The variant [s_call (Some(ty,v,e)) lets f el]
   builds the function call [let v:ty = (local lets in) f el in e] *)

val s_havoc : string -> var_type Abstract.VarMap.t -> condition -> statement
(** [s_havoc t w c] builds the non-deterministic statement [any unit
   writes w ensures c], with tag [t].  *)

val s_let_in : string -> var_type -> Abstract.why_var -> expression -> statement -> statement
(** [s_let_in t ty v e s] builds the local binding statement [let v:ty
   = e in s], with tag [t].  *)

val s_break : string -> statement
(** [s_break] creates the break statement. *)

val copy_stmt : statement -> statement

type fun_kind = private
  | Fun_let of statement * expression option
  (** functions defined with a body and possibly a returned expression *)
  | Fun_val of Abstract.why_env * (Abstract.why_var * Abstract.var_value) option * condition
  (** functions declared with a contract: a writes clause,
      an optional result variable, and a post-condition *)

type param_value =
  | Param_ref of var_type
  (** parameter passed by reference *)
  | Param_noref of Abstract.var_value
  (** other parameters, with associated abstract variable *)

type func = private {
    func_name : fun_id;
    func_params : (Abstract.why_var * param_value) list;
    (** parameters *)
    func_def : fun_kind
  }
(** function declarations. *)

val declare_function_let :
  name:fun_id ->
  params:(bool * var_type * Abstract.why_var) list ->
  body:statement ->
  return:(var_type * expression) option ->
  func

val declare_function_val :
  name:fun_id ->
  params:(bool * var_type * Abstract.why_var) list ->
  writes:var_type Abstract.VarMap.t ->
  result:(var_type * Abstract.why_var) option ->
  post:condition ->
  func

type why1program = private
  { name : string;
    vars : Abstract.why_env;
    functions : func FuncMap.t;
    statements : statement }
(** whole programs *)

val mk_program :
  name:string ->
  variables:var_type Abstract.VarMap.t ->
  functions:func FuncMap.t ->
  main:statement ->
  why1program

val reset_ast_generation : unit -> unit
(** once [mk_program] has been called, it is not allowed anymore to
   create new AST nodes. Calling this function will restore this
   possibility, but any existing AST so far should be discarded *)

(** {2 Printing} *)

val print_type : Format.formatter -> var_type -> unit

val print_expression : Format.formatter -> expression -> unit

val print_condition : Format.formatter -> condition -> unit

val print_statement : Format.formatter -> statement -> unit

val print_program : Format.formatter -> why1program -> unit
