


open Format
open Ident
open Ty
open Term
open Decl
open Theory
open Task

module type Printer = sig

    val forget_all : unit -> unit     (* flush id_unique *)
    val forget_tvs : unit -> unit     (* flush id_unique for type vars *)
    val forget_var : vsymbol -> unit  (* flush id_unique for a variable *)

    val print_id_labels : formatter -> ident -> unit  (* labels and location *)

    val print_tv : formatter -> tvsymbol -> unit      (* type variable *)
    val print_vs : formatter -> vsymbol -> unit       (* variable *)

    val print_ts : formatter -> tysymbol -> unit      (* type symbol *)
    val print_ls : formatter -> lsymbol -> unit       (* logic symbol *)
    val print_cs : formatter -> lsymbol -> unit       (* constructor symbol *)
    val print_pr : formatter -> prsymbol -> unit      (* proposition name *)
    val print_th : formatter -> theory -> unit        (* theory name *)

    val print_ty : formatter -> ty -> unit            (* type *)
    val print_vsty : formatter -> vsymbol -> unit     (* variable : type *)

    val print_quant : formatter -> quant -> unit      (* quantifier *)
    val print_binop : asym:bool -> formatter -> binop -> unit (* binary operator *)
    val print_pat : formatter -> pattern -> unit      (* pattern *)
    val print_term : formatter -> term -> unit        (* term *)

    val print_label : formatter -> label -> unit
    val print_loc : formatter -> Loc.position -> unit
    val print_pkind : formatter -> prop_kind -> unit
    val print_meta_arg : formatter -> meta_arg -> unit
    val print_meta_arg_type : formatter -> meta_arg_type -> unit

    val print_ty_decl : formatter -> tysymbol -> unit
    val print_data_decl : formatter -> data_decl -> unit
    val print_param_decl : formatter -> lsymbol -> unit
    val print_logic_decl : formatter -> logic_decl -> unit
    val print_ind_decl : formatter -> ind_sign -> ind_decl -> unit
    val print_next_data_decl : formatter -> data_decl -> unit
    val print_next_logic_decl : formatter -> logic_decl -> unit
    val print_next_ind_decl : formatter -> ind_decl -> unit
    val print_prop_decl : formatter -> prop_decl -> unit

    val print_decl : formatter -> decl -> unit
    val print_tdecl : formatter -> tdecl -> unit

    val print_task : formatter -> task -> unit
    val print_sequent : formatter -> task -> unit

    val print_theory : formatter -> theory -> unit

    val print_namespace : formatter -> string -> theory -> unit

  end
