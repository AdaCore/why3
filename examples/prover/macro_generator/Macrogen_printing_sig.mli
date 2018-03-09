
open Macrogen_params
open Macrogen_decls

module type HelperType = sig
  
  (* ~fun fmt -> fprintf fmt "@[<hov indent>" *)
  val indent : printer
  val string_printer : string -> printer
  val params_printer : printer
  val level : TName.t -> int TMap.t -> int
  val inc_level : TName.t -> int TMap.t -> int TMap.t
  val tindex_printer : TName.t -> printer
  val tname_printer : TName.t -> printer
  
  (* rpapply_printer p1 p2 n : print the n-times application
     of p1 to p2, inside parenthesis if n>= 1 *)
  val rpapply_printer : printer -> printer -> int -> printer
  
  (* operation : option _ *)
  val options_printer : printer -> int -> printer
  (* operation : Some _ *)
  val somes_printer : printer -> int -> printer
  (* operation : compose some _,with identity at the bottom.*)
  val csomes_printer : int -> printer
  
  val list_printer : ('a -> printer) -> 'a list -> printer
  val sep_list_printer : ('a -> printer) -> printer -> 'a list -> printer
  
  (* print binding type parameter inside the correct amount of options,
     given base prefix. *)
  val binding_type_printer :
    ?blevels:int TMap.t -> printer -> TName.t -> printer
  val type_app_printer : ?blevels:int TMap.t -> printer -> TName.t -> printer
  val type_printer : ?blevels:int TMap.t -> printer -> internal_types -> printer
  
  (* make_first_case_printer p1 p2 : print p1 the first time,
     p2 the others. *)
  val make_first_case_printer : printer -> printer -> printer
  (* variant for recursive logic functions *)
  val rec_fun_printer : unit -> printer
  (* variant for recursive types *)
  val rec_type_printer : unit -> printer
  (* variant for recursive procedures *)
  val rec_val_printer : unit -> printer
  (* variant for inductive predicates *)
  val rec_ind_printer : unit -> printer
  
  val match_variables : ?blevels:int TMap.t -> ?vbase:printer ->
    constr -> ( printer * int TMap.t * internal_types ) list
  
  (* cons_case_printer ~blevels ~vbase ccase cs :
     generate the match case for normal constructor cs,
     under binding context blevels, using vbase to generate
     bound variables in the pattern.
     call ccase with the left-to-right list of variables,
     together with correct binding context and type. *)
  val cons_case_printer :
    ?blevels:int TMap.t -> ?vbase:printer ->
    ( ( printer * int TMap.t * internal_types ) list -> printer ) ->
    constr -> printer
  
  (* var_case_printer ~vbase vcase tn : generate variable
     match case for type tn, with code given by
     vcase called over generated variable. Use vbase as base to
     generate variables in pattern-matching, default "v". *)
  val var_case_printer :
    ?vbase:printer -> (printer -> printer) -> TName.t -> printer
  
  (* match_printer _ _ tn vcase ccase t :
     print pattern-matching over t,using vcase for variable
     case and ccase for constructor case. *)
  val match_printer :
    ?blevels:int TMap.t -> ?vbase:printer -> TName.t ->
    ( printer -> printer ) ->
    ( constr -> ( printer * int TMap.t * internal_types ) list -> printer ) ->
    printer -> printer
  
  (* make_for_defs f : call f for each defined type, together
     with its constructors and its binding parameter list. *)
  val make_for_defs : (TName.t -> constructors -> TName.t list -> unit) -> unit
  
  (* make_for_bdefs f : as make_for_defs, but filter out
     types that do not have any binding parameter *)
  val make_for_bdefs : (TName.t -> constructors -> TName.t list -> unit) -> unit
  
  (* make_for_vdefs f : as make_for_defs, but filter out
     types that do not have the variable case
     (* = cannot be substituted *) *)
  val make_for_vdefs : (TName.t -> constructors -> TName.t list -> unit) -> unit
  
  val lemma_cons_case :
    ( printer -> int TMap.t -> TName.t -> printer ) ->
    ( constr -> ( printer * int TMap.t * internal_types ) list -> printer )
  
  val blemma_cons_case :
    ( printer -> int TMap.t -> TName.t -> printer ) ->
    ( constr -> ( printer * int TMap.t * internal_types ) list -> printer )
  
  val reconstruct_cons_case :
    ( printer -> int TMap.t -> TName.t -> printer ) ->
    ( constr -> ( printer * int TMap.t * internal_types ) list -> printer )
  
  val lift_printer :
    bool -> printer -> int TMap.t -> TName.t -> printer
  
  val subst_type_printer :
    bool -> ?blevels:int TMap.t -> printer -> printer -> TName.t -> printer
  
  val print_composition :
    bool -> bool -> TName.t -> printer -> ( TName.t -> printer ) -> printer
  
  val typed_identity_printer : bool -> printer -> TName.t -> printer
  
  val typed_sor_printer : printer -> printer -> TName.t -> printer
  
end

module type PrintParameters = sig
  
  module P : Parameters
  module H : HelperType
  
end


