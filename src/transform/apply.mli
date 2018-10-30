

val intros: Term.term ->
  Term.term list * Term.vsymbol list * (Term.vsymbol * Term.term) list * Term.term
(* intros returns a tuple containing:
   - list of premises of the term,
   - list of universally quantified variables at head of the terms,
   - list of let-binding at head of the term,
   - the term without premises/let-binding and forall variables at head.
*)

val rewrite_list: bool -> bool -> Decl.prsymbol list ->
  Decl.prsymbol option -> Task.task list Trans.trans
(* [rewrite_list with_terms rev opt hl h1]
   @param opt: If set, all the rewritings are optional
   @param rev: If set, all the rewritings are from right to left
   @param hl: list of rewrite hypothesis
   @param h1: hypothesis to rewrite in
*)

val term_decl: Theory.tdecl -> Term.term
(* Return the term associated to a prop declaration or raise an error in every
   other cases *)
