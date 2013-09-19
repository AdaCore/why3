(* Boolean flag to decide if generated applications of inrange functions
   should be inlined whenever possible. *)
val inline_inrange : bool

(* Boolean flag to decide if a warning should be generated when a constraint
   is forgotten. *)
val output_warning : bool

(* Generic transformation.
   Should be called with theories of the form:
     type t "ty_lab"
     predicate inrange "p_lab" (x : base) = ...
     function of_base "f_lab" (x : base) : t
     function to_base "f_lab" (x : t) : base
     axiom to_base__def "ax_lab": ...
     ...
   Replace t every where with base and generates applications of inrange
   if needed.
   Remove applications of of_base and to_base.
   Remove axiom to_base__def.
*)
val generic_eliminate_bounded_types : Ident.Slab.elt ->
  Ident.Slab.elt -> Ident.Slab.elt -> Ident.Slab.elt -> Task.task Trans.trans

(* Label "bounded_type" *)
val bounded_type_label : Ident.Slab.elt

(* Generic_eliminate_bounded_types instantiated with bounded_type_label *)
val eliminate_bounded_types : Task.task Trans.trans
