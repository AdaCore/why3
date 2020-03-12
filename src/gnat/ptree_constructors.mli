(** {1 Smart constructors for [Why3.Ptree]} *)

(** {2 General and auxiliary constructors} *)

val get_pos : ?loc:Why3.Loc.position -> unit -> Why3.Loc.position

val mk_ident : Why3.Ptree.attr list -> string -> Why3.Ptree.ident

val mk_qualid : Why3.Ptree.ident list -> Why3.Ptree.qualid

val mk_qualid' : string list -> Why3.Ptree.qualid

(** {3 Attributes} *)

val mk_pos : Why3.Loc.position -> Why3.Ptree.attr

val mk_str : string -> Why3.Ptree.attr

(** {3 Construct nodes from descriptions} *)

val mk_expr :
  ?loc:Why3.Loc.position -> Why3.Ptree.expr_desc -> Why3.Ptree.expr

val mk_term :
  ?loc:Why3.Loc.position -> Why3.Ptree.term_desc -> Why3.Ptree.term

val mk_pat :
  ?loc:Why3.Loc.position -> Why3.Ptree.pat_desc -> Why3.Ptree.pattern

(** {2 Smart constructors for [Ptree.pty]} *)

module Ty :
  sig
    type t = Why3.Ptree.pty
    val mk_var : Why3.Ptree.ident -> Why3.Ptree.pty
    val mk_idapp : Why3.Ptree.qualid -> Why3.Ptree.pty list -> Why3.Ptree.pty
    val mk_atomic_type : string list -> Why3.Ptree.pty
    val mk_tuple : Why3.Ptree.pty list -> Why3.Ptree.pty
    val mk_ref : Why3.Ptree.pty list -> Why3.Ptree.pty
    val mk_arrow : Why3.Ptree.pty -> Why3.Ptree.pty -> Why3.Ptree.pty
    val mk_scope : Why3.Ptree.qualid -> Why3.Ptree.pty -> Why3.Ptree.pty
    val mk_paren : Why3.Ptree.pty -> Why3.Ptree.pty
    val mk_pure : Why3.Ptree.pty -> Why3.Ptree.pty
  end

(** {2 Smart constructors for [Ptree.expr] and [Ptree.term]} *)

module type E_or_T =
  sig
    type t
    val target : [ `Expr | `Term ]
    val mk_const : ?loc:Why3.Loc.position -> Why3.Constant.constant -> t
    val mk_idapp : ?loc:Why3.Loc.position -> Why3.Ptree.qualid -> t list -> t
    val mk_apply : ?loc:Why3.Loc.position -> t -> t -> t
    val mk_var : ?loc:Why3.Loc.position -> Why3.Ptree.qualid -> t
    val mk_cast : ?loc:Why3.Loc.position -> t -> Why3.Ptree.pty -> t
    val mk_case :
      ?loc:Why3.Loc.position -> t -> (Why3.Ptree.pattern * t) list -> t
    val mk_tuple : ?loc:Why3.Loc.position -> t list -> t
    val mk_record :
      ?loc:Why3.Loc.position -> (Why3.Ptree.qualid * t) list -> t
    val mk_update :
      ?loc:Why3.Loc.position -> t -> (Why3.Ptree.qualid * t) list -> t
    val mk_binop :
      ?loc:Why3.Loc.position -> t -> [ `And_asym | `Or_asym ] -> t -> t
    val mk_not : ?loc:Why3.Loc.position -> t -> t
    val mk_infix : ?loc:Why3.Loc.position -> t -> Why3.Ptree.ident -> t -> t
    val mk_innfix : ?loc:Why3.Loc.position -> t -> Why3.Ptree.ident -> t -> t
    val mk_let : ?loc:Why3.Loc.position -> Why3.Ptree.ident -> t -> t -> t
    val mk_scope : ?loc:Why3.Loc.position -> Why3.Ptree.qualid -> t -> t
    val mk_if : ?loc:Why3.Loc.position -> t -> t -> t -> t
    val mk_truth : ?loc:Why3.Loc.position -> bool -> t
    val mk_attr : ?loc:Why3.Loc.position -> Why3.Ptree.attr -> t -> t
    val mk_attrs : ?loc:Why3.Loc.position -> Why3.Ptree.attr list -> t -> t

    (** Specialize constructor *)
    val expr_or_term :
      ?expr:(unit -> Why3.Ptree.expr) ->
      ?term:(unit -> Why3.Ptree.term) -> unit -> t
  end

(** {2 Smart constructors for [Ptree.expr]} *)

module E :
  sig
    include E_or_T with type t = Why3.Ptree.expr
    val mk :
      ?loc:Why3.Loc.position -> Why3.Ptree.expr_desc -> Why3.Ptree.expr
    val mk_assert :
      ?loc:Why3.Loc.position ->
      Why3.Expr.assertion_kind -> Why3.Ptree.term -> Why3.Ptree.expr
    val mk_seq :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.expr -> Why3.Ptree.expr -> Why3.Ptree.expr
    val mk_any :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.param list ->
      Why3.Expr.rs_kind ->
      Why3.Ptree.pty option ->
      Why3.Ptree.pattern ->
      Why3.Ity.mask -> Why3.Ptree.spec -> Why3.Ptree.expr
    val mk_fun :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.binder list ->
      Why3.Ptree.pty option ->
      Why3.Ptree.pattern ->
      Why3.Ity.mask -> Why3.Ptree.spec -> Why3.Ptree.expr -> Why3.Ptree.expr
    val mk_match :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.expr ->
      Why3.Ptree.reg_branch list ->
      Why3.Ptree.exn_branch list -> Why3.Ptree.expr
    val mk_raise :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.qualid -> Why3.Ptree.expr option -> Why3.Ptree.expr
    val mk_while :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.expr ->
      Why3.Ptree.invariant ->
      Why3.Ptree.variant -> Why3.Ptree.expr -> Why3.Ptree.expr
    val mk_assign :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.expr ->
      Why3.Ptree.qualid option -> Why3.Ptree.expr -> Why3.Ptree.expr
    val mk_absurd : ?loc:Why3.Loc.position -> unit -> Why3.Ptree.expr
    val expr_or_term :
      ?expr:(unit -> Why3.Ptree.expr) ->
      ?term:(unit -> Why3.Ptree.term) -> unit -> Why3.Ptree.expr
  end

(** {2 Smart constructors for [Ptree.term]} *)

module T :
  sig
    include E_or_T with type t = Why3.Ptree.term
    val target : [> `Term ]
    val mk :
      ?loc:Why3.Loc.position -> Why3.Ptree.term_desc -> Why3.Ptree.term
    val mk_binop :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.term ->
      [< `And | `And_asym | `By | `Iff | `Implies | `Or | `Or_asym | `So ] ->
      Why3.Ptree.term -> Why3.Ptree.term
    val mk_binnop :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.term ->
      [< `And | `And_asym | `By | `Iff | `Implies | `Or | `Or_asym | `So ] ->
      Why3.Ptree.term -> Why3.Ptree.term
    val mk_at :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.term -> Why3.Ptree.ident -> Why3.Ptree.term
    val mk_quant :
      ?loc:Why3.Loc.position ->
      Why3.Dterm.dquant ->
      Why3.Ptree.binder list ->
      Why3.Ptree.term list list -> Why3.Ptree.term -> Why3.Ptree.term
    val mk_eps :
      ?loc:Why3.Loc.position ->
      Why3.Ptree.ident ->
      Why3.Ptree.pty ->
      Why3.Ptree.term -> Why3.Ptree.term
    val name_term : string -> Why3.Ptree.term -> Why3.Ptree.term
    val expr_or_term :
      ?expr:(unit -> Why3.Ptree.expr) ->
      ?term:(unit -> Why3.Ptree.term) -> unit -> Why3.Ptree.term
  end

(** {2 Smart constructors for [Ptree.pattern]} TODO complete *)

module P :
sig
  val mk :
    ?loc:Why3.Loc.position -> Why3.Ptree.pat_desc -> Why3.Ptree.pattern
  val mk_wild : ?loc:Why3.Loc.position -> unit -> Why3.Ptree.pattern
  val mk_var :
    ?loc:Why3.Loc.position -> Why3.Ptree.ident -> Why3.Ptree.pattern
end

(** {2 Smart constructors for [Ptree.decl]} *)

module D :
  sig
    type t = Why3.Ptree.decl
    val mk_type : Why3.Ptree.type_decl list -> Why3.Ptree.decl
    val mk_logic : Why3.Ptree.logic_decl list -> Why3.Ptree.decl
    val mk_ind :
      Why3.Decl.ind_sign -> Why3.Ptree.ind_decl list -> Why3.Ptree.decl
    val mk_prop :
      Why3.Decl.prop_kind ->
      Why3.Ptree.ident -> Why3.Ptree.term -> Why3.Ptree.decl
    val mk_let :
      Why3.Ptree.ident ->
      Why3.Ptree.ghost ->
      Why3.Expr.rs_kind -> Why3.Ptree.expr -> Why3.Ptree.decl
    val mk_rec : Why3.Ptree.fundef list -> Why3.Ptree.decl
    val mk_exn :
      Why3.Ptree.ident -> Why3.Ptree.pty -> Why3.Ity.mask -> Why3.Ptree.decl
    val mk_meta :
      Why3.Ptree.ident -> Why3.Ptree.metarg list -> Why3.Ptree.decl
    val mk_cloneexport :
      Why3.Ptree.qualid -> Why3.Ptree.clone_subst list -> Why3.Ptree.decl
    val mk_useexport : Why3.Ptree.qualid -> Why3.Ptree.decl
    val mk_cloneimport :
      ?loc:Why3.Loc.position ->
      bool ->
      Why3.Ptree.qualid ->
      Why3.Ptree.ident option ->
      Why3.Ptree.clone_subst list -> Why3.Ptree.decl
    val mk_useimport :
      ?loc:Why3.Loc.position ->
      bool ->
      (Why3.Ptree.qualid * Why3.Ptree.ident option) list -> Why3.Ptree.decl
    val mk_import : Why3.Ptree.qualid -> Why3.Ptree.decl
    val mk_scope :
      ?loc:Why3.Loc.position ->
      bool -> Why3.Ptree.ident -> Why3.Ptree.decl list -> Why3.Ptree.decl
  end

(** {2 Constructors of elements as produced by the parser} *)

val result_ident : Why3.Ptree.ident

val requires : Why3.Ptree.term -> Why3.Ptree.term

val ensures :
  ?loc:Why3.Loc.position ->
  Why3.Ptree.term ->
  Why3.Loc.position * (Why3.Ptree.pattern * Why3.Ptree.term) list

val mk_spec :
  ?pre:Why3.Ptree.pre list ->
  ?post:Why3.Ptree.post list ->
  ?xpost:Why3.Ptree.xpost list ->
  ?reads:Why3.Ptree.qualid list ->
  ?writes:Why3.Ptree.term list ->
  ?alias:(Why3.Ptree.term * Why3.Ptree.term) list ->
  ?variant:Why3.Ptree.variant ->
  ?checkrw:bool -> ?diverge:bool -> ?partial:bool -> unit -> Why3.Ptree.spec
