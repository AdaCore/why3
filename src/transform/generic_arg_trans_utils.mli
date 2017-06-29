open Term

exception Arg_trans of string
exception Arg_trans_term of (string * term * term)
exception Arg_trans_pattern of (string * pattern * pattern)
exception Arg_trans_type of (string * Ty.ty * Ty.ty)
exception Arg_bad_hypothesis of (string * term)
exception Cannot_infer_type of string

val gen_ident : ?label:Ident.Slab.t -> ?loc:Loc.position -> string -> Ident.preid

val replace_in_term: term -> term -> term -> term

val subst_quant: quant -> term_quant -> term -> term

(* Transform the term (exists v, f) into f[x/v] *)
val subst_exist: term -> term -> term

(* Transform the term (forall v, f) into f[x/v] *)
val subst_forall: term -> term -> term
