open Format
open Gnat_ast

let pp_symbol fmt s =
  match s with
  | No_symbol -> ()
  | Symbol s -> Format.fprintf fmt "%s" s

let pp_symbol_label fmt s =
  match s with
  | No_symbol -> ()
  | Symbol s -> Format.fprintf fmt "[%s]" s

let pp_symbol_set_label fmt s =
  pp_print_list ~pp_sep:Why3.Pp.space pp_symbol_label fmt s

let pp_source_ptr fmt p =
  match p with
  | No_location -> ()
  | Source_ptr r ->
    Format.fprintf fmt "[sloc:%s:%d]" r.filename r.line

let pp_theory_type fmt k =
  match k with
  | Theory -> Format.fprintf fmt "%s" "theory"
  | Module -> Format.fprintf fmt "%s" "module"

let pp_clone_type fmt c =
  match c with
  | Import -> Format.fprintf fmt        "import"
  | Export ->  Format.fprintf fmt       "export"
  | Clone_default -> Format.fprintf fmt "      "

let pp_subst_type fmt s =
  match s with
  | Type_subst -> Format.fprintf fmt "type"
  | Function -> Format.fprintf fmt "function"
  | Predicate -> Format.fprintf fmt "predicate"
  | Namepace -> Format.fprintf fmt "namespace"
  | Lemma -> Format.fprintf fmt "lemma"
  | Goal -> Format.fprintf fmt "goal"

let pp_uint fmt (Uint s) =
  Format.fprintf fmt "%s" s

let pp_literal_base fmt l =
  match l with
  | True -> Format.fprintf fmt "True"
  | False -> Format.fprintf fmt "False"

let pp_connector fmt c =
  match c with
  | Or_else -> Format.fprintf fmt "||"
  | And_then -> Format.fprintf fmt "&&"
  | Imply -> Format.fprintf fmt "->"
  | Equivalent -> Format.fprintf fmt "<->"
  | Or -> Format.fprintf fmt "\\/"
  | And -> Format.fprintf fmt "/\\"

let pp_assert_kind fmt (k : Gnat_ast.assert_kind) =
  match k with
  | Assert -> Format.fprintf fmt "assert"
  | Check -> Format.fprintf fmt "check"
  | Assume -> Format.fprintf fmt "assume"

let get_infix name args =
  match name.desc with
  | Identifier { name = { desc = Name { infix = true }}} ->
    begin match args with
    | [x;y] -> Some (x,y)
    | _ -> assert false
    end
  | _ -> None

let pp_ureal fmt (Ureal z) =
  Format.fprintf fmt "%c%a/%ab%d" (if z.negative then '-' else '+')
    pp_uint z.numerator pp_uint z.denominator z.base

let rec pp_why_node : type a . Format.formatter -> a why_node -> unit =
  fun fmt n ->
  match n with
  | { desc = Type _ } as n -> pp_type fmt n
  | { desc = Name _ } as n -> pp_name fmt n
  | { desc = Effects _ } as n -> pp_effects fmt n
  | { desc = Binder _ } as n -> pp_binder fmt n
  | { desc = Transparent_type_definition _ } as n -> pp_transparent_type_definition fmt n
  | { desc = Record_binder _ } as n -> pp_record_binder fmt n
  | { desc = Record_definition _ } as n -> pp_record_definition fmt n
  | { desc = Range_type_definition _ } as n -> pp_range_type_definition fmt n
  | { desc = Triggers _ } as n -> pp_triggers fmt n
  | { desc = Trigger _ } as n -> pp_trigger fmt n
  | { desc = Handler _ } as n -> pp_handler fmt n
  | { desc = Field_association _ } as n -> pp_field_association fmt n
  | { desc = Variant _ } as n -> pp_variant fmt n
  | { desc = Variants _ } as n -> pp_variants fmt n
  | { desc = Universal_quantif _ } as n -> pp_universal_quantif fmt n
  | { desc = Existential_quantif _ } as n -> pp_existential_quantif fmt n
  | { desc = Not _ } as n -> pp_not fmt n
  | { desc = Connection _ } as n -> pp_connection fmt n
  | { desc = Label _ } as n -> pp_label fmt n
  | { desc = Loc_label _ } as n -> pp_loc_label fmt n
  | { desc = Identifier _ } as n -> pp_identifier fmt n
  | { desc = Tagged _ } as n -> pp_tagged fmt n
  | { desc = Call _ } as n -> pp_call fmt n
  | { desc = Literal _ } as n -> pp_literal fmt n
  | { desc = Binding _ } as n -> pp_binding fmt n
  | { desc = Elsif _ } as n -> pp_elsif fmt n
  | { desc = Epsilon _ } as n -> pp_epsilon fmt n
  | { desc = Conditional _ } as n -> pp_conditional fmt n
  | { desc = Integer_constant _ } as n -> pp_integer_constant fmt n
  | { desc = Range_constant _ } as n -> pp_range_constant fmt n
  | { desc = Modular_constant _ } as n -> pp_modular_constant fmt n
  | { desc = Fixed_constant _ } as n -> pp_fixed_constant fmt n
  | { desc = Real_constant _ } as n -> pp_real_constant fmt n
  | { desc = Float_constant _ } as n -> pp_float_constant fmt n
  | { desc = Comment _ } as n -> pp_comment fmt n
  | { desc = Deref _ } as n -> pp_deref fmt n
  | { desc = Record_access _ } as n -> pp_record_access fmt n
  | { desc = Record_update _ } as n -> pp_record_update fmt n
  | { desc = Record_aggregate _ } as n -> pp_record_aggregate fmt n
  | { desc = Any_expr _ } as n -> pp_any_expr fmt n
  | { desc = Assignment _ } as n -> pp_assignment fmt n
  | { desc = Binding_ref _ } as n -> pp_binding_ref fmt n
  | { desc = Loop _ } as n -> pp_loop fmt n
  | { desc = Statement_sequence _ } as n -> pp_statement_sequence fmt n
  | { desc = Abstract_expr _ } as n -> pp_abstract_expr fmt n
  | { desc = Assert _ } as n -> pp_assert fmt n
  | { desc = Raise _ } as n -> pp_raise fmt n
  | { desc = Try_block _ } as n -> pp_try_block fmt n
  | { desc = Function_decl _ } as n -> pp_function_decl fmt n
  | { desc = Axiom _ } as n -> pp_axiom fmt n
  | { desc = Goal _ } as n  -> pp_goal fmt n
  | { desc = Type_decl _ } as n -> pp_type_decl fmt n
  | { desc = Global_ref_declaration _ } as n -> pp_global_ref_declaration fmt n
  | { desc = Namespace_declaration _ } as n -> pp_namespace_declaration fmt n
  | { desc = Exception_declaration _ } as n -> pp_exception_declaration fmt n
  | { desc = Include_declaration _ } as n -> pp_include_declaration fmt n
  | { desc = Meta_declaration _ } as n -> pp_meta_declaration fmt n
  | { desc = Clone_declaration _ } as n -> pp_clone_declaration fmt n
  | { desc = Clone_substitution _ } as n -> pp_clone_substitution fmt n
  | { desc = Theory_declaration _ } as n -> pp_theory_declaration fmt n
  | { desc = Custom_substitution _ } as n -> pp_custom_substitution fmt n
  | { desc = Custom_declaration _ } as n -> pp_custom_declaration fmt n
  | { desc = Module _ } as n -> pp_module fmt n

and pp_why_node_option : type a . Format.formatter -> a why_node option -> unit =
  fun fmt n ->
  match n with
  | None -> ()
  | Some x -> pp_why_node fmt x

and pp_why_node_list : type a . Format.formatter -> a why_node list -> unit =
  fun fmt l ->
  pp_print_list ~pp_sep:Why3.Pp.space pp_why_node fmt l

and pp_comment fmt (n : comment_id) =
  match n.desc with
  | Comment r ->
    Format.fprintf fmt "@[<hov>(* %a *)@]" pp_symbol r.comment

and pp_name fmt (n : name_id) =
  match n.desc with
  | Name r ->
    begin if not r.infix then
      begin match r.module_ with | None -> () | Some x -> Format.fprintf fmt "%a." pp_why_node x end;
      begin if r.namespace = No_symbol then () else Format.fprintf fmt "%a." pp_symbol r.namespace end;
    end;
    Format.fprintf fmt "%a" pp_symbol r.symb

and pp_type fmt (n : type_id) =
  match n.desc with
  | Type r ->
    Format.fprintf fmt "%a%s"
      pp_why_node r.name (if r.is_mutable then "__ref" else "")

and pp_theory_declaration fmt (n : theory_declaration_id) =
  match n.desc with
  | Theory_declaration r ->
    Format.fprintf fmt "(* %a *)@\n@[<hov 2>%a %a@\n@\n%a@\n@\n%a@]@\n@\nend"
      pp_symbol r.comment pp_theory_type r.kind pp_symbol r.name
      pp_include_declaration_list r.includes pp_declaration_list r.declarations

and pp_include_declaration_list fmt l =
  pp_print_list ~pp_sep:Why3.Pp.newline pp_why_node fmt l

and pp_declaration_list fmt l =
  pp_print_list ~pp_sep:Why3.Pp.newline2 pp_why_node fmt l

and pp_include_declaration fmt (n : include_declaration_id) =
  match n.desc with
  | Include_declaration r ->
    Format.fprintf fmt "use %a %a" pp_clone_type r.use_kind pp_module r.module_

and pp_module fmt (n : module_id) =
  match n.desc with
  | Module r ->
    if r.file = No_symbol then Format.fprintf fmt "%a" pp_symbol r.name
    else Format.fprintf fmt "%a.%a" pp_symbol r.file pp_symbol r.name

and pp_axiom fmt (n : axiom_id) =
  match n.desc with
  | Axiom r ->
    Format.fprintf fmt "axiom %a : @[<hov 2>%a@]" pp_symbol r.name pp_why_node r.def

and pp_goal fmt (n : goal_id) =
  match n.desc with
  | Goal r ->
    Format.fprintf fmt "axiom %a : @[<hov 2>%a@]" pp_symbol r.name pp_why_node r.def

and pp_global_ref_declaration fmt (n : global_ref_declaration_id) =
  match n.desc with
  | Global_ref_declaration r ->
    Format.fprintf fmt "val %a %a %a: %a" pp_why_node r.name
      pp_symbol_set_label r.labels pp_source_ptr r.location pp_why_node r.ref_type

and pp_type_decl fmt (n : type_decl_id) =
  match n.desc with
  | Type_decl r ->
    Format.fprintf fmt "@[<hov 2>type %a %a %a"
      pp_why_node r.name pp_symbol_set_label r.labels pp_why_node_list r.args;
    begin match r.definition with
    | None -> ()
    | Some x -> Format.fprintf fmt "= @[<hov 2>%a@]" pp_why_node x
    end;
    Format.fprintf fmt "@]"

and pp_clone_declaration fmt (n : clone_declaration_id) =
  match n.desc with
  | Clone_declaration r ->
    Format.fprintf fmt "@[<hov 2>clone %a %a"
      pp_clone_type r.clone_kind pp_module r.origin;
    if r.as_name = No_symbol then ()
    else Format.fprintf fmt " as %a" pp_symbol r.as_name;
    Format.fprintf fmt " with axiom . %a@]" pp_clone_substitution_list r.substitutions

and pp_clone_substitution_list fmt l =
  pp_print_list ~pp_sep:Why3.Pp.comma pp_why_node fmt l

and pp_clone_substitution fmt (n : clone_substitution_id) =
  match n.desc with
  | Clone_substitution r ->
    Format.fprintf fmt "%a %a = %a" pp_subst_type r.kind
      pp_why_node r.orig_name pp_why_node r.image

and pp_namespace_declaration fmt (n : namespace_declaration_id) =
  match n.desc with
  | Namespace_declaration r ->
    Format.fprintf fmt "@[<hov 2>scope %a %a @]end"
      pp_symbol r.name pp_why_node_list r.declarations

and pp_range_type_definition fmt (n : range_type_definition_id) =
  match n.desc with
  | Range_type_definition r ->
    Format.fprintf fmt "<range %a %a>" pp_uint r.first pp_uint r.last

and pp_function_decl fmt (n : function_decl_id) =
  match n.desc with
  | Function_decl r ->
    Format.fprintf fmt "@[<hov 2>function@ %a@ %a@ %a@ %a@ requires@ { %a }@ ensures @ { %a }@ returns@ %a"
    pp_symbol_set_label r.labels pp_source_ptr r.location pp_why_node r.name pp_binder_list r.binders
    pp_why_node_option r.pre pp_why_node_option r.post pp_why_node_option r.return_type;
    begin match r.def with
    | None -> ()
    | Some x -> Format.fprintf fmt " =@[<hov 2> %a@]" pp_why_node x
    end;
    Format.fprintf fmt "@]"

and pp_identifier fmt (n : identifier_id) =
  match n.desc with
  | Identifier r ->
    if r.labels = [] then Format.fprintf fmt "%a" pp_why_node r.name
    else Format.fprintf fmt "(%a %a)" pp_symbol_set_label r.labels pp_why_node r.name

and pp_binder_list fmt l =
  Format.fprintf fmt "@[(";
  pp_print_list ~pp_sep:Why3.Pp.space pp_binder fmt l;
  Format.fprintf fmt "@])"

and pp_literal fmt (n : literal_id) =
  match n.desc with
  | Literal r -> Format.fprintf fmt "%a" pp_literal_base r.value

and pp_binder fmt (n : binder_id) =
  match n.desc with
  | Binder r ->
    Format.fprintf fmt "%a : %a" pp_why_node_option r.name pp_why_node r.arg_type

and pp_integer_constant fmt (n : integer_constant_id) =
  match n.desc with
  | Integer_constant r -> Format.fprintf fmt "%a" pp_uint r.value

and pp_connection fmt (n : connection_id) =
  match n.desc with
  | Connection r ->
    Format.fprintf fmt "(@[<hov 2>";
    Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ %a@ " pp_connector r.op)
      pp_why_node fmt (r.left :: r.right :: r.more_right);
    Format.fprintf fmt "@])"

and pp_call fmt (n : call_id) =
  match n.desc with
  | Call r ->
    match get_infix r.name r.args with
    | Some (a, b) ->
      Format.fprintf fmt "(@[<hov 2>%a@ %a %a@])"
        pp_why_node a pp_why_node r.name pp_why_node b
    | None ->
      Format.fprintf fmt "(@[<hov 2>%a@ %a@])" pp_why_node r.name pp_why_node_list r.args

and pp_record_definition fmt (n : record_definition_id) =
  match n.desc with
  | Record_definition r ->
    Format.fprintf fmt "@[<hov 2>{ %a }@]" pp_record_binder_list r.fields

and pp_record_binder_list fmt (l : record_binder_list) =
  let l = l.elt0 :: l.elts in
  Format.pp_print_list ~pp_sep:Why3.Pp.semi pp_why_node fmt l

and pp_record_binder fmt (n : record_binder_id) =
  match n.desc with
  | Record_binder r ->
    Format.fprintf fmt "%a%s%a : %a"
      pp_symbol_set_label r.labels
      (if r.is_mutable then "mutable " else "")
      pp_why_node_option r.name pp_why_node r.arg_type

and pp_record_access fmt (n : record_access_id) =
  match n.desc with
  | Record_access r ->
    Format.fprintf fmt "%a.%a" pp_why_node r.name pp_why_node r.field

and pp_meta_declaration fmt (n : meta_declaration_id) =
  match n.desc with
  | Meta_declaration r ->
    Format.fprintf fmt "meta %a %a" pp_symbol r.name pp_symbol r.parameter

and pp_conditional fmt (n : conditional_id) =
  match n.desc with
  | Conditional  r ->
    Format.fprintf fmt "@[(if@ %a@ then@ @[%a@]@ %a"
      pp_why_node r.condition pp_why_node r.then_part
      pp_why_node_list r.elsif_parts;
    begin match r.else_part with
    | None -> ()
    | Some x -> Format.fprintf fmt "@ else@ @[%a@]" pp_why_node x
    end;
    Format.fprintf fmt "@])"

and pp_loc_label fmt (n : loc_label_id) =
  match n.desc with
  | Loc_label r ->
    Format.fprintf fmt "@[(%a %a)@]"
      pp_source_ptr r.sloc pp_why_node r.def

and pp_label fmt (n : label_id) =
  match n.desc with
  | Label r ->
    Format.fprintf fmt "@[(%a %a)@]"
      pp_symbol_set_label r.labels pp_why_node r.def

and pp_deref fmt (n : deref_id) =
  match n.desc with
  | Deref r -> Format.fprintf fmt "!%a" pp_why_node r.right

and pp_statement_sequence fmt (n : statement_sequence_id) =
  match n.desc with
  | Statement_sequence r ->
    let sep fmt () = Format.fprintf fmt ";@\n" in
    Format.pp_print_list ~pp_sep:sep pp_why_node fmt (r.statements.elt0 :: r.statements.elts)

and pp_assert fmt (n : assert_id) =
  match n.desc with
  | Assert r ->
    Format.fprintf fmt "%a@ @[<hov 2>{ %a }@]"
      pp_assert_kind r.assert_kind pp_why_node r.pred

and pp_abstract_expr fmt (n : abstract_expr_id) =
  match n.desc with
  | Abstract_expr r ->
    Format.fprintf fmt "abstract@ ensures@ @[{ %a }@] begin @[ %a @] end"
      pp_why_node r.post pp_why_node r.expr

and pp_binding fmt (n : binding_id) =
  match n.desc with
  | Binding r ->
     Format.fprintf fmt "(let %a@ =@ @[<hov2 >%a@]@ in@ %a)"
      pp_why_node r.name pp_why_node r.def pp_why_node r.context

and pp_try_block fmt (n : try_block_id) =
  match n.desc with
  | Try_block r ->
    Format.fprintf fmt "(try@ @[<hov 2>%a@] with@ @[%a@])"
      pp_why_node r.prog pp_handler_list r.handler

and pp_handler_list fmt (l : handler_list) =
  pp_print_list ~pp_sep:Why3.Pp.newline pp_why_node fmt (l.elt0 :: l.elts)

and pp_handler fmt (n : handler_id) =
  match n.desc with
  | Handler r ->
    Format.fprintf fmt "| %a %a@ ->@ @[%a@]"
      pp_why_node r.name pp_why_node_option r.arg pp_why_node r.def

and pp_assignment fmt (n : assignment_id) =
  match n.desc with
  | Assignment r ->
     Format.fprintf fmt "(%a@ %a@ :=@ @[<hov 2>%a@])"
      pp_symbol_set_label r.labels pp_why_node r.name pp_why_node r.value

and pp_raise fmt (n : raise_id) =
  match n.desc with
  | Raise r ->
     Format.fprintf fmt "raise %a" pp_why_node r.name

and pp_elsif fmt (n : elsif_id) =
  match n.desc with
  | Elsif r ->
    Format.fprintf fmt "@[(if@ %a@ then@ @[%a@]@@])"
      pp_why_node r.condition pp_why_node r.then_part

and pp_range_constant fmt (n : range_constant_id) =
  match n.desc with
  | Range_constant r ->
    Format.fprintf fmt "%a" pp_uint r.value

and pp_modular_constant fmt (n : modular_constant_id) =
  match n.desc with
  | Modular_constant r ->
    Format.fprintf fmt "%a" pp_uint r.value

and pp_fixed_constant fmt (n : fixed_constant_id) =
  match n.desc with
  | Fixed_constant r ->
    Format.fprintf fmt "%a" pp_uint r.value

and pp_real_constant fmt (n : real_constant_id) =
  match n.desc with
  | Real_constant r ->
    Format.fprintf fmt "%a" pp_ureal r.value

and pp_float_constant fmt (n : float_constant_id) =
  match n.desc with
  | Float_constant r ->
    Format.fprintf fmt "%a" pp_ureal r.value

and pp_loop fmt (n : loop_id) =
  match n.desc with
  | Loop r ->
    Format.fprintf fmt "@[<hov 2>loop@ %a@\n%a@\n%a@\n%a@\n end loop@]"
      pp_why_node r.code_before pp_invariant_list r.invariants
      pp_variants_list r.variants pp_why_node r.code_after

and pp_invariant_list fmt (n : pred_olist) =
  let print_inv fmt n = Format.fprintf fmt "invariant@ {@[%a@]}" pp_why_node n in
  pp_print_list ~pp_sep:Why3.Pp.newline print_inv fmt n

and pp_variants_list fmt (n : variants_olist) =
  pp_print_list ~pp_sep:Why3.Pp.newline pp_why_node fmt n

and pp_variants fmt (n : variants_id) =
  match n.desc with
  | Variants r ->
    Format.fprintf fmt "variant @ {@[%a@]}"
      (pp_print_list ~pp_sep:Why3.Pp.newline pp_why_node)
      (r.variants.elt0 :: r.variants.elts)

and pp_variant fmt (n : variant_id) =
  match n.desc with
  | Variant r ->
    Format.fprintf fmt "%a@ =>@ @[%a@]"
      pp_why_node r.cmp_op pp_why_node r.expr

and pp_any_expr fmt (n : any_expr_id) =
  let Any_expr r = n.desc in
  Format.fprintf fmt "(@[<hov 2>%a any@ %a@ pre@ {@[%a@]@]}@ post@ {@[%a@]}@ return@ %a)@]"
  pp_symbol_set_label r.labels pp_why_node_option r.effects
  pp_why_node_option r.pre pp_why_node_option r.post
  pp_why_node r.return_type

and pp_epsilon fmt (n : epsilon_id) =
  let Epsilon r = n.desc in
  Format.fprintf fmt "@[(epsilon %a : %a {@[%a@]})@]"
    pp_why_node r.name pp_why_node r.typ pp_why_node r.pred

and pp_effects fmt (n : effects_id) = Format.fprintf fmt "--pp_effects NOT IMPLEMENTED"
and pp_transparent_type_definition fmt (n : transparent_type_definition_id) = Format.fprintf fmt "--pp_transparent_type_definition NOT IMPLEMENTED"
and pp_triggers fmt (n : triggers_id) = Format.fprintf fmt "--pp_triggers NOT IMPLEMENTED"
and pp_trigger fmt (n : trigger_id) = Format.fprintf fmt "--pp_trigger NOT IMPLEMENTED"
and pp_field_association fmt (n : field_association_id) = Format.fprintf fmt "--pp_field_association NOT IMPLEMENTED"
and pp_universal_quantif fmt (n : universal_quantif_id) = Format.fprintf fmt "--pp_universal_quantif NOT IMPLEMENTED"
and pp_existential_quantif fmt (n : existential_quantif_id) = Format.fprintf fmt "--pp_existential_quantif NOT IMPLEMENTED"
and pp_not fmt (n : not_id) = Format.fprintf fmt "--pp_not NOT IMPLEMENTED"
and pp_tagged fmt (n : tagged_id) = Format.fprintf fmt "--pp_tagged NOT IMPLEMENTED"
and pp_record_update fmt (n : record_update_id) = Format.fprintf fmt "--pp_record_update NOT IMPLEMENTED"
and pp_record_aggregate fmt (n : record_aggregate_id) = Format.fprintf fmt "--pp_record_aggregate NOT IMPLEMENTED"
and pp_binding_ref fmt (n : binding_ref_id) = Format.fprintf fmt "--pp_binding_ref NOT IMPLEMENTED"
and pp_exception_declaration fmt (n : exception_declaration_id) = Format.fprintf fmt "--pp_exception_declaration NOT IMPLEMENTED"
and pp_custom_substitution fmt (n : custom_substitution_id) = Format.fprintf fmt "--pp_custom_substitution NOT IMPLEMENTED"
and pp_custom_declaration fmt (n : custom_declaration_id) = Format.fprintf fmt "--pp_custom_declaration NOT IMPLEMENTED"

let pp_file fmt f =
  pp_print_list ~pp_sep:Why3.Pp.newline2 pp_why_node fmt f.theory_declarations
