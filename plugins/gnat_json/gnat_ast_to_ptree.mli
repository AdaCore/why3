(* {1 Conversion of [Gnat_ast] to [Why3.Ptree]} *)

val gnat_json_format : string

val mk_pty_of_type : Gnat_ast.type_id -> Why3.Ptree.pty

val mk_effects : Gnat_ast.effects_id ->
  Why3.Ptree.qualid list * Why3.Ptree.term list *
  (Why3.Loc.position * (Why3.Ptree.qualid * 'a option) list) list

val mk_expr_of_expr : Gnat_ast.expr_id -> Why3.Ptree.expr

val mk_term_of_expr : Gnat_ast.expr_id -> Why3.Ptree.term

val mk_expr_of_prog : Gnat_ast.prog_id -> Why3.Ptree.expr

val mk_term_of_pred : Gnat_ast.pred_id -> Why3.Ptree.term

val mk_function_decl : Gnat_ast.function_decl_id -> Why3.Ptree.decl list

val mk_record_binder : Gnat_ast.record_binder_id -> Why3.Ptree.field

val mk_declaration : Gnat_ast.declaration_id -> Why3.Ptree.decl list

val mk_generic_theory :
  Gnat_ast.generic_theory_id -> (Why3.Ptree.ident * Why3.Ptree.decl list) list

val mlw_file : Gnat_ast.generic_theory_id list -> Why3.Ptree.mlw_file

val debug : Why3.Debug.flag
