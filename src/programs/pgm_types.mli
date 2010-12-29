
open Why
open Util
open Ident
open Ty
open Theory
open Term
open Decl

(* mutable type symbols *)

type mtsymbol = private {
  mt_name  : ident;
  mt_args  : tvsymbol list;
  mt_model : ty option;
  mt_abstr : tysymbol;
}

val create_mtsymbol : preid -> tvsymbol list -> ty option -> mtsymbol

val mt_equal : mtsymbol -> mtsymbol -> bool

exception NotMutable

val get_mtsymbol : tysymbol -> mtsymbol
  (** raises [NotMutable] if [ts] is not a mutable type *)

val is_mutable_ts : tysymbol -> bool
val is_mutable_ty : ty       -> bool

val ts_arrow : tysymbol

(* program types *)
module rec T : sig

  type pre = Term.fmla

  type post_fmla = Term.vsymbol (* result *) * Term.fmla
  type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla
      
  type esymbol = lsymbol

  type post = post_fmla * (esymbol * exn_post_fmla) list
      
  type type_v = private
  | Tpure    of ty
  | Tarrow   of pvsymbol list * type_c

  and type_c = { 
    c_result_type : type_v;
    c_effect      : E.t;
    c_pre         : pre;
    c_post        : post; 
  }

  and pvsymbol = private {
    pv_name : ident;
    pv_tv   : type_v;
    pv_ty   : ty;      (* as a logic type, for typing purposes only *)
    pv_vs   : vsymbol; (* for use in the logic *)
  }

  val tpure  : ty -> type_v
  val tarrow : pvsymbol list -> type_c -> type_v

  val create_pvsymbol : preid -> ?vs:vsymbol -> type_v -> pvsymbol

  (* program symbols *)

  type psymbol = private {
    p_name : ident;
    p_tv   : type_v;
    p_ty   : ty;      (* as a logic type, for typing purposes only *)
    p_ls   : lsymbol; (* for use in the logic *) 
  }
      
  val create_psymbol : preid -> type_v -> psymbol

  val p_equal : psymbol -> psymbol -> bool

  (* program types -> logic types *)

  val purify : ty -> ty
  val purify_type_v : ?logic:bool -> type_v -> ty
    (** when [logic] is [true], mutable types are turned into their models *)
    
  (* operations on program types *)
    
  val apply_type_v_var : type_v -> pvsymbol -> type_c
  val apply_type_v_sym : type_v -> psymbol  -> type_c
  val apply_type_v_ref : type_v -> R.t      -> type_c
    
  val occur_type_v : R.t -> type_v -> bool
    
  val v_result : ty -> vsymbol
  val exn_v_result : Why.Term.lsymbol -> Why.Term.vsymbol option
    
  val post_map : (fmla -> fmla) -> post -> post
    
  val subst1 : vsymbol -> term -> term Mvs.t
    
  val eq_type_v : type_v -> type_v -> bool

  (* pretty-printers *)

  val print_type_v : Format.formatter -> type_v -> unit
  val print_type_c : Format.formatter -> type_c -> unit
  val print_post   : Format.formatter -> post   -> unit

end 

and Mpv :  sig include Map.S with type key = T.pvsymbol end

(* references *)
and R : sig

  type t = 
    | Rlocal  of T.pvsymbol
    | Rglobal of T.psymbol

  val type_of : t -> ty

  val name_of : t -> ident

end 
and Sref : sig include Set.S with type elt = R.t end
and Mref : sig include Map.S with type key = R.t end
and Sexn : sig include Set.S with type elt = T.esymbol end

(* effects *)
and E : sig

  type t = private {
    reads  : Sref.t;
    writes : Sref.t;
    raises : Sexn.t;
  }

  val empty : t

  val add_read  : R.t -> t -> t
  val add_write : R.t -> t -> t
  val add_raise : T.esymbol -> t -> t

  val remove_reference : R.t -> t -> t    
  val filter : (R.t -> bool) -> t -> t

  val remove_raise : T.esymbol -> t -> t

  val union : t -> t -> t

  val equal : t -> t -> bool
    
  val no_side_effect : t -> bool
    
  val subst : R.t Mpv.t -> t -> t

  val occur : R.t -> t -> bool

end 


