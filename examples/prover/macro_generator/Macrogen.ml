
open Format
open Macrogen_decls
open Macrogen_transform
open Macrogen_params
open Macrogen_printing

let (<<) f x = f x
(*
let lambda_def = {
    var_parameters = [] ;
    binder_types = [ TypeDefinition ( "lambda" ,
        [ Var ;
          BCons ("App" , [] , [ DeclaredType "lambda" ; DeclaredType "lambda" ] ) ;
          BCons ( "Lam" , [ "lambda" , [] ] , [ DeclaredType "lambda" ] ) ;
          BCons ( "Fix" , [ "lambda" , [] ; "lambda" , [] ] , [ DeclaredType "lambda" ] ) ] ,
        [] ) ]
  }

let first_order_def = {
    var_parameters = [ "function_symbol" ; "predicate_symbol" ] ;
    binder_types = [ TypeDefinition ( "fo_term" ,
        [ Var ;
          BCons ("FOApp" , [] , [ TypeVar "function_symbol" ; DeclaredType "fo_term_list" ] ) ] ,
        [] ) ;
      TypeDefinition ( "fo_term_list" ,
        [ BCons ("FONil" , [] , [] ) ;
          BCons ("FOCons" , [] , [ DeclaredType "fo_term" ; DeclaredType "fo_term_list" ] ) ] ,
        [] ) ;
      TypeDefinition ( "fo_formula" ,
        [ BCons ( "FOForall" , [ "fo_term" , [] ] , [ DeclaredType "fo_formula" ] ) ;
          BCons ( "FOExists" , [ "fo_term" , [] ] , [ DeclaredType "fo_formula" ] ) ;
          BCons ( "FOAnd" , [] , [ DeclaredType "fo_formula" ; DeclaredType "fo_formula" ] ) ;
          BCons ( "FOOr" , [] , [ DeclaredType "fo_formula" ; DeclaredType "fo_formula" ] ) ;
          BCons ( "FONot" , [] , [ DeclaredType "fo_formula" ] ) ;
          BCons ( "FOPred" , [] , [ TypeVar "predicate_symbol" ; DeclaredType "fo_term_list" ] ) ] ,
        [] ) ]
  }

let coc_def = {
  var_parameters = [] ;
  binder_types = [ TypeDefinition ( "coc_term" ,
      [ Var ;
        BCons ( "App" , [] , [ DeclaredType "coc_term" ; DeclaredType "coc_term" ] ) ;
        BCons ( "Lam" , [ "coc_term" , [ DeclaredType "coc_term" ] ] , [ DeclaredType "coc_term" ] ) ;
        BCons ( "Forall" , [ "coc_term" , [ DeclaredType "coc_term" ] ] , [ DeclaredType "coc_term" ] ) ;
        BCons ( "Type" , [] , [ DeclaredType "integer" ] ) ] , [] ) ;
      TypeDefinition ( "integer" ,
      [ BCons ( "O" , [] , [] ) ;
        BCons ( "S" , [] , [ DeclaredType "integer" ] ) ] , [] ) ]
  }
*)
let fsub_def = {
  var_parameters = [] ;
  binder_types = [ TypeDefinition ( "fsub_type" ,
      [ Var ;
        BCons ( "Arrow" , [] , [ DeclaredType "fsub_type" ; DeclaredType "fsub_type" ] ) ;
        BCons ( "Top" , [] , [] ) ;
        BCons ( "Forall" , [ "fsub_type" , [ DeclaredType "fsub_type" ] ] , [ DeclaredType "fsub_type" ] ) ] ,
      [] ) ;
      TypeDefinition ( "fsub_term" ,
      [ Var ;
        BCons ( "App" , [] , [ DeclaredType "fsub_term" ; DeclaredType "fsub_term" ] ) ;
        BCons ( "Lam" , [ "fsub_term" , [ DeclaredType "fsub_type" ] ] , [ DeclaredType "fsub_term" ] ) ;
        BCons ( "TLam" , [ "fsub_type" , [ DeclaredType "fsub_type" ] ] , [ DeclaredType "fsub_term" ] ) ;
        BCons ( "TApp" , [] , [ DeclaredType "fsub_term" ; DeclaredType "fsub_type" ] ) ] ,
      [] ) ]
  }
(*
let horror_def = {
  var_parameters = [ "t1" ; "t2" ; "t3" ] ;
  binder_types = [ TypeDefinition ( "t4" , [ Var ] , [] ) ;
    TypeDefinition ( "t8" , [ BCons ( "W" , [] , [] ) ;
      BCons ( "V" , [] , [ DeclaredType "t8" ] ) ] , [] ) ;
    TypeDefinition ( "t5" , [ Var ;
      BCons ( "U" , [ "t5" , [ DeclaredType "t4" ; DeclaredType "t5" ; TypeVar "t2" ] ;
        "t4" , [ TypeVar "t3" ; DeclaredType "t4" ; DeclaredType "t5" ; DeclaredType "t6" ] ;
        "t6" , [ TypeVar "t1" ; DeclaredType "t7" ; DeclaredType "t8" ; DeclaredType "t7" ] ] ,
        [ TypeVar "t3" ; DeclaredType "t5" ; DeclaredType "t5" ; DeclaredType "t6" ; DeclaredType "t6" ] ) ;
      BCons ( "ZZ" , [] , [ DeclaredType "t7" ; DeclaredType "t5" ; DeclaredType "t6" ] ) ]
      , [] ) ;
    TypeDefinition ( "t6" , [ Var ;
      BCons ( "X" , [ "t7" , [ DeclaredType "t8" ] ] , [ DeclaredType "t6" ] ) ] , [] ) ;
    TypeDefinition ( "t7" , [ BCons ( "Y" , [ "t5" , [] ; "t5" , [ DeclaredType "t6" ] ;
      "t5" , [ DeclaredType "t5" ] ] , [ DeclaredType "t5" ; DeclaredType "t6" ] ) ] , [] ) ]
  }*)

let dfoterm = DeclaredType "fo_term"
let dfoterml = DeclaredType "fo_term_list"
let dfoformula = DeclaredType "fo_formula"
let dfoformulal = DeclaredType "fo_formula_list"
(*let dfsymb = (*DeclaredType*) TypeVar "function_symbol"
let dpsymb = (*DeclaredType*) TypeVar "predicate_symbol"*)
let dlsymb = DeclaredType "symbol"
let foterm_var = [ (*"function_symbol" ; "predicate_symbol"*) ]

(* For some reason, going that way do not work at all-
   why3ide do not even terminates the task generation for the
   provers I normally use for some goal-and goals
   for those two cases are abnormally hard ! *)

(*let function_symbol = TypeDefinition ( "function_symbol" ,
  [ Var ] , [] )

let function_symbol_sig = TypeAssumption ( "function_symbol" ,
  [ "function_symbol" ] )

let predicate_symbol = TypeDefinition ( "predicate_symbol" ,
  [ Var ] , [] )

let predicate_symbol_sig = TypeAssumption ( "predicate_symbol" ,
  [ "predicate_symbol" ] )*)

let symbol = TypeDefinition ( "symbol" , [ Var ] , [] )

let symbol_sig = TypeAssumption ( "symbol" , [ "symbol" ] )

let foterm = TypeDefinition ( "fo_term" ,
  [ Var ; BCons ( "App" , [] ,
    [ dlsymb ; dfoterml ] ) ] , [] )

let foterm_sig = TypeAssumption ( "fo_term" ,
  [ "symbol" ; "fo_term" ] )

let foterm_list = TypeDefinition ( "fo_term_list" ,
  [ BCons ( "FONil" , [] , [] ) ;
    BCons ( "FOCons" , [] , [ dfoterm ; dfoterml ] ) ] , [] )

let foterm_list_sig = TypeAssumption ( "fo_term_list" ,
  [ "symbol" ; "fo_term" ] )

let foformula = TypeDefinition ( "fo_formula" ,
  [ BCons ( "Forall" , [ "fo_term" , [] ] , [ dfoformula ] ) ;
    BCons ( "Exists" , [ "fo_term" , [] ] , [ dfoformula ] ) ;
    BCons ( "And" , [] , [ dfoformula ; dfoformula ] ) ;
    BCons ( "Or" , [] , [ dfoformula ; dfoformula ] ) ;
    (*BCons ( "Imply" , [] , [ dfoformula ; dfoformula ] ) ;
    BCons ( "Equiv" , [] , [ dfoformula ; dfoformula ] ) ;*)
    BCons ( "Not" , [] , [ dfoformula ] ) ;
    BCons ( "FTrue" , [] , [] ) ;
    BCons ( "FFalse" , [] , [] ) ;
    BCons ( "PApp" , [] , [ dlsymb ; dfoterml ] ) ] , [] )

let foformula_sig = TypeAssumption ( "fo_formula" ,
  [ "symbol" ; "fo_term" ] )

let foformula_list = TypeDefinition ( "fo_formula_list" ,
  [ BCons ( "FOFNil" , [] , [] ) ;
    BCons ( "FOFCons" , [] , [ dfoformula ; dfoformulal ] ) ] , [] )

let foformula_list_sig = TypeAssumption ( "fo_formula_list" ,
  [ "symbol" ; "fo_term" ] )

let fo_tableau = TypeDefinition ( "tableau" ,
  [ BCons ( "Root" , [] , [] ) ;
    BCons ( "Node" , [] , [ DeclaredType "tableau" ;
      DeclaredType "fo_formula" ;
      DeclaredType "fo_formula_list" ] ) ] , [] )

let fo_tableau_sig = TypeAssumption ( "tableau" ,
  [ "symbol" ; "fo_term" ] )

(*let _ =
  let dbase = fsub_def in
  let dm = convert dbase in
  let module D = struct let dm = dm let indent = 2 end in
  let module PP = MakePP(MakeDefaultP(D)) in
  let module PT = Macrogen_theory.Printer(PP) in
  let module PNP = Macrogen_nlparams.MakeDefaultP(D) in
  let module PNL = Macrogen_nameless.Printer(PP)(PNP) in
  fprintf std_formatter "%tmodule A@\n\
    %t%t%t%t@]@ end@\n@\n%tmodule B@\n\
    %tuse import A@\n%t@]@ end@\n@\n%tmodule C@\n\
    %tuse import A@\nuse import B@\n%t@]@ end@\n%tmodule D@\n\
    %tuse import A@\nuse import B@\nuse import C@\n%t@]@ end@\n@\n"
    << PP.H.indent
    << PT.required_imports
    << PT.base_defs_printer
    << PT.subst_lemmae_defs_printer
    << PT.free_var_lemmae_defs_printer
    << PP.H.indent
    << PT.required_imports
    << PNL.types_defs_printer
    << PP.H.indent
    << PT.required_imports
    << PNL.logics_defs_printer
    << PP.H.indent
    << PT.required_imports
    << PNL.impls_defs_printer
*)
let p othimp1 n1 othimp2 n2 dbase =
  let dm = convert dbase in
  let module D = struct let dm = dm let indent = 2 end in
  let module PP = MakePP(MakeDefaultP(D)) in
  let module PT = Macrogen_theory.Printer(PP) in
  let module PNP = Macrogen_nlparams.MakeDefaultP(D) in
  let module PNL = Macrogen_nameless.Printer(PP)(PNP) in
  let c1 = open_out_bin (n1^".mlw") in
  let _ = try let fmt1 = formatter_of_out_channel c1 in
    fprintf fmt1 "%tmodule Spec@\n\
      %t%t%t%t%t@]@ end@\n@\n@."
      << PP.H.indent
      << PT.required_imports
      << othimp1
      << PT.base_defs_printer
      << PT.subst_lemmae_defs_printer
      << PT.free_var_lemmae_defs_printer
  with e -> close_out c1 ; raise e in close_out c1 ;
  let c2 = open_out_bin (n2^".mlw") in
  let _ = try let fmt2 = formatter_of_out_channel c2 in
    fprintf fmt2 "%tmodule Types@\n\
      %t%tuse import %s.Spec@\n%t@]@ end@\n@\n\
      %tmodule Logic@\n\
      %t%tuse import %s.Spec@\n\
      use import Types@\n%t@]@ end@\n@\n%tmodule Impl@\n\
      %t%tuse import %s.Spec@\n\
      use import Types@\nuse import Logic@\n%t@]@ end@\n@\n@."
      << PP.H.indent
      << PT.required_imports
      << othimp2
      << n1
      << PNL.types_defs_printer
      << PP.H.indent
      << PT.required_imports
      << othimp2
      << n1
      << PNL.logics_defs_printer
      << PP.H.indent
      << PT.required_imports
      << othimp2
      << n1
      << PNL.impls_defs_printer
  with e -> close_out c2 ; raise e in close_out c2

let _ =
  let nextothimp1 othimp1 n1 fmt =
    fprintf fmt "%tuse import %s.Spec@\n" othimp1 n1 in
  let nextothimp2 othimp2 n1 n2 fmt = fprintf fmt "%tuse import %s.Spec@\n\
    use import %s.Types@\n\
    use import %s.Logic@\n\
    use import %s.Impl@\n" othimp2 n1 n2 n2 n2 in
  let dbase = { var_parameters = foterm_var ;
    binder_types = [ symbol ] } in
  let n1 = "Firstorder_symbol_spec" in
  let n2 = "Firstorder_symbol_impl" in
  let _ = p ignore n1 ignore n2 dbase in
  let othimp1 = nextothimp1 ignore n1 in
  let othimp2 = nextothimp2 ignore n1 n2 in
  let dbase = { var_parameters = foterm_var ;
    binder_types = [ symbol_sig ; foterm ; foterm_list ] } in
  let n1 = "Firstorder_term_spec" in
  let n2 = "Firstorder_term_impl" in
  let _ = p othimp1 (*ignore*) n1 othimp2 (*ignore*) n2 dbase in
  let othimp2 = nextothimp2 othimp2 (*ignore*) n1 n2 in
  let othimp1 = nextothimp1 othimp1 (*ignore*) n1 in
  (*let dbase = { var_parameters = foterm_var ;
    binder_types = [ predicate_symbol ] } in
  let n1 = "Firstorder_predicate_symbol_spec" in
  let n2 = "Firstorder_predicate_symbol_impl" in
  let _ = p ignore n1 ignore n2 dbase in
  let othimp1 = nextothimp1 othimp1 n1 in
  let othimp2 = nextothimp2 othimp2 n1 n2 in*)
  let dbase = { var_parameters = foterm_var ;
    binder_types = [ symbol_sig ; foterm_sig ; foterm_list_sig ; foformula ] } in
  let n1 = "Firstorder_formula_spec" in
  let n2 = "Firstorder_formula_impl" in
  let _ = p othimp1 n1 othimp2 n2 dbase in
  let othimp1 = nextothimp1 othimp1 n1 in
  let othimp2 = nextothimp2 othimp2 n1 n2 in
  let dbase = { var_parameters = foterm_var ;
    binder_types = [ symbol_sig ; foterm_sig ; foformula_sig ; foformula_list ] } in
  let n1 = "Firstorder_formula_list_spec" in
  let n2 = "Firstorder_formula_list_impl" in
  let _ = p othimp1 n1 othimp2 n2 dbase in
  let othimp1 = nextothimp1 othimp1 n1 in
  let othimp2 = nextothimp2 othimp2 n1 n2 in
  let dbase = { var_parameters = foterm_var ;
    binder_types = [ symbol_sig ; foterm_sig ; foformula_sig ; foformula_list_sig ;
      fo_tableau ] } in
  let n1 = "Firstorder_tableau_spec" in
  let n2 = "Firstorder_tableau_impl" in
  let _ = p othimp1 n1 othimp2 n2 dbase in
  ()






(*
let _ =
  let dbase = fsub_def in
  let dm = convert dbase in
  let module D = struct let dm = dm let indent = 2 end in
  let module PP = MakePP(MakeDefaultP(D)) in
  let module PT = Macrogen_theory.Printer(PP) in
  let module PNP = Macrogen_nlparams.MakeDefaultP(D) in
  let module PNL = Macrogen_nameless.Printer(PP)(PNP) in
  fprintf std_formatter "%tmodule A@\nuse import option.Option@\n\
    use import int.Int@\nuse import Nat.Nat@\n\
    use import Functions.Func@\nuse import OptionFuncs.Funcs@\n\
    use import Sum.Sum@\n
    %t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t\
    %t%t%t%t%t%t%t%t%t%t%t%t%t%t%t\
    \
    %t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t%t@]@\nend@\n@\n"
    << PP.H.indent
    << PT.type_defs_printer
    << PT.size_defs_printer
    << PT.size_lemma_printer
    << PT.subst_defs_printer false
    << PT.composition_lemma_printer false false
    << PT.identity_lemma_printer false
    << PT.subst_composition_def_printer false
    << PT.associativity_lemma_printer (false,true,false)
    << PT.associativity_lemma_printer (true,false,false)
    << PT.right_identity_lemma_printer false
    << PT.subst_lifting_printer
    << PT.lifting_composition_lemma_printer (false,true)
    << PT.lifting_composition_lemma_printer (true,false)
    << PT.subst_defs_printer true
    << PT.composition_lemma_printer false true
    << PT.composition_lemma_printer true false
    << PT.subst_composition_def_printer true
    << PT.associativity_lemma_printer (false,true,true)
    << PT.associativity_lemma_printer (true,false,true)
    << PT.associativity_lemma_printer (true,true,false)
    << PT.lifting_composition_lemma_printer (true,true)
    << PT.composition_lemma_printer true true
    << PT.associativity_lemma_printer (true,true,true)
    << PT.subst_identity_printer
    << PT.left_identity_lemma_printer false
    << PT.identity_lemma_printer true
    << PT.left_identity_lemma_printer true
    << PT.right_identity_lemma_printer true
    << PT.free_var_def_printer
    << PT.subst_free_var_inversion_printer false
    << PT.rename_free_var_propagation_lemma_printer
    << PT.subst_free_var_inversion_printer true
    << PT.subst_free_var_propagation_lemma_printer
    << PT.free_var_equivalence_lemma_printer true
    << PT.free_var_equivalence_lemma_printer false
    << PT.open_close_defs_printer
    << PT.size_preservation_lemma_printer
    
    << PNL.type_defs_printer
    << PNL.size_defs_printer
    << PNL.size_lemma_printer
    << PNL.shift_defs_printer
    << PNL.shift_lemma_printer
    << PNL.model_defs_printer
    << PNL.model_subst_commutation_lemma_printer
    << PNL.model_rename_commutation_lemma_printer
    << PNL.correct_indexes_printer
    << PNL.bound_depth_printer
    << PNL.bound_depth_lemma_printer
    << PNL.model_equal_lemma_printer
    << PNL.bind_var_printer
    << PNL.unbind_var_printer
    << PNL.implementation_type_printer
    << PNL.invariant_printer
    << PNL.constructor_type_printer
    << PNL.constructor_invariant_printer
    << PNL.constructor_relation_printer
    << PNL.constructor_open_relation_printer
    << PNL.construction_operator_printer
    << PNL.destruction_operator_printer
    << PNL.subst_operator_printer*)


