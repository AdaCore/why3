(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

(** Program types *)

type dity =
  | Dvar of dvar ref
  | Dutv of tvsymbol
  | Dapp of itysymbol * dity list * dreg list
  | Dpur of tysymbol  * dity list

and dvar =
  | Dtvs of tvsymbol
  | Dval of dity

and dreg =
  | Rreg of region * dity
  | Rvar of rvar ref

and rvar =
  | Rtvs of tvsymbol * dity
  | Rval of dreg

let create_dreg dity =
  Rvar (ref (Rtvs (create_tvsymbol (id_fresh "rho"), dity)))

let dity_of_ity ity =
  let hreg = Hreg.create 5 in
  let rec dity_of_ity ity = match ity.ity_node with
    | Ityvar tv -> Dutv tv
    | Itypur (ts,tl) -> Dpur (ts, List.map dity_of_ity tl)
    | Ityapp (its,tl,rl) ->
        Dapp (its, List.map dity_of_ity tl, List.map dreg_of_reg rl)
  and dreg_of_reg r =
    try Hreg.find hreg r with Not_found ->
    let dreg = create_dreg (dity_of_ity r.reg_ity) in
    Hreg.add hreg r dreg;
    dreg
  in
  dity_of_ity ity

let ity_of_dity ~strict dity =
  let rec ity_of_dity = function
    | Dvar { contents = Dval dty } -> ity_of_dity dty
    | Dvar _ when strict -> Loc.errorm "undefined type variable"
    | Dvar r ->
        let tv = create_tvsymbol (id_fresh "xi") in
        r := Dval (Dutv tv);
        ity_var tv
    | Dapp (ts,dl,rl) ->
        ity_app ts (List.map ity_of_dity dl) (List.map reg_of_dreg rl)
    | Dpur (ts,dl) ->
        ity_pur ts (List.map ity_of_dity dl)
    | Dutv tv ->
        ity_var tv
  and reg_of_dreg = function
    | Rvar { contents = Rval dreg } -> reg_of_dreg dreg
    | Rvar ({ contents = Rtvs (tv,dty) } as r) ->
        let reg = create_region (id_clone tv.tv_name) (ity_of_dity dty) in
        r := Rval (Rreg (reg,dty));
        reg
    | Rreg (reg,_) -> reg
  in
  ity_of_dity dity

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

(** Destructive type unification *)

let rec occur_check tv = function
  | Dvar { contents = Dval d } -> occur_check tv d
  | Dapp (_,dl,_) | Dpur (_,dl) -> List.iter (occur_check tv) dl
  | Dvar { contents = Dtvs tv' } | Dutv tv' ->
      if tv_equal tv tv' then raise Exit

let rec unify d1 d2 = match d1,d2 with
  | Dvar { contents = Dval d1 }, d2
  | d1, Dvar { contents = Dval d2 } ->
      unify d1 d2
  | Dvar { contents = Dtvs tv1 },
    Dvar { contents = Dtvs tv2 } when tv_equal tv1 tv2 ->
      ()
  | Dvar ({ contents = Dtvs tv } as r), d
  | d, Dvar ({ contents = Dtvs tv } as r) ->
      occur_check tv d;
      r := Dval d
  | Dutv tv1, Dutv tv2 when tv_equal tv1 tv2 ->
      ()
  | Dapp (its1,dl1,_), Dapp (its2,dl2,_) when its_equal its1 its2 ->
      List.iter2 unify dl1 dl2
  | Dpur (ts1,dl1), Dpur (ts2,dl2) when ts_equal ts1 ts2 ->
      List.iter2 unify dl1 dl2
  | _ -> raise Exit

(** Reunify regions *)

let dtvs_queue : dvar ref Queue.t = Queue.create ()

let unify_queue : (dity * dity) Queue.t = Queue.create ()

let dity_fresh () =
  let r = ref (Dtvs (create_tvsymbol (id_fresh "a"))) in
  Queue.add r dtvs_queue;
  Dvar r

let its_app_fresh s dl =
  let htv = Htv.create 5 in
  let hreg = Hreg.create 5 in
  let rec inst ity = match ity.ity_node with
    | Ityvar v -> Htv.find htv v
    | Itypur (s,tl) -> Dpur (s, List.map inst tl)
    | Ityapp (s,tl,rl) -> Dapp (s, List.map inst tl, List.map fresh rl)
  and fresh r =
    try Hreg.find hreg r with Not_found ->
    let reg = create_dreg (inst r.reg_ity) in
    Hreg.add hreg r reg;
    reg in
  List.iter2 (Htv.add htv) s.its_ts.ts_args dl;
  match s.its_def with
  | None -> Dapp (s, dl, List.map fresh s.its_regs)
  | Some ity -> inst ity

let rec dity_refresh = function
  | Dvar { contents = Dval dty } -> dity_refresh dty
  | Dvar { contents = Dtvs _ } as dity -> dity
  | Dutv _ as dity -> dity
  | Dpur (ts,dl) -> Dpur (ts, List.map dity_refresh dl)
  | Dapp (its,dl,_) -> its_app_fresh its (List.map dity_refresh dl)

let unify ?(weak=false) d1 d2 =
  unify d1 d2;
  if not weak then Queue.add (d1,d2) unify_queue

let rec reunify d1 d2 = match d1,d2 with
  | Dvar { contents = Dval d1 }, d2
  | d1, Dvar { contents = Dval d2 } -> reunify d1 d2
  | Dvar _, Dvar _ | Dutv _, Dutv _ -> ()
  | Dapp (_,dl1,rl1), Dapp (_,dl2,rl2) ->
      List.iter2 reunify dl1 dl2;
      List.iter2 unify_reg rl1 rl2
  | Dpur (_,dl1), Dpur (_,dl2) ->
      List.iter2 reunify dl1 dl2
  | _ -> assert false

and unify_reg r1 r2 = match r1,r2 with
  | Rvar { contents = Rval r1 }, r2
  | r1, Rvar { contents = Rval r2 } ->
      unify_reg r1 r2
  | Rvar { contents = Rtvs (tv1,_) },
    Rvar { contents = Rtvs (tv2,_) } when tv_equal tv1 tv2 ->
      ()
  | Rvar ({ contents = Rtvs (_,d1) } as r),
    (Rvar { contents = Rtvs (_,d2) } as d)
  | Rvar ({ contents = Rtvs (_,d1) } as r), (Rreg (_,d2) as d)
  | (Rreg (_,d1) as d), Rvar ({ contents = Rtvs (_,d2) } as r) ->
      reunify d1 d2;
      r := Rval d
  | Rreg _, Rreg _ -> ()
    (* we don't check whether the regions are the same,
       because we won't have a good location for the error.
       Let the core API raise the exception later. *)

let reunify_regions () =
  Queue.iter (fun r -> match !r with
    | Dval d -> r := Dval (dity_refresh d)
    | Dtvs _ -> ()) dtvs_queue;
  Queue.clear dtvs_queue;
  Queue.iter (fun (d1,d2) -> reunify d1 d2) unify_queue;
  Queue.clear unify_queue

(* Pretty-printing *)

let debug_print_reg_types = Debug.register_info_flag "print_reg_types"
  ~desc:"Print@ types@ of@ regions@ (mutable@ fields)."

let print_dity fmt dity =
  let protect_on x s = if x then "(" ^^ s ^^ ")" else s in
  let print_rtvs fmt tv = Mlw_pretty.print_reg fmt
    (create_region (id_clone tv.tv_name) Mlw_ty.ity_unit) in
  let rec print_dity inn fmt = function
    | Dvar { contents = Dtvs tv }
    | Dutv tv -> Pretty.print_tv fmt tv
    | Dvar { contents = Dval dty } -> print_dity inn fmt dty
    | Dpur (ts,tl) when is_ts_tuple ts -> Format.fprintf fmt "(%a)"
        (Pp.print_list Pp.comma (print_dity false)) tl
    | Dpur (ts,[]) -> Pretty.print_ts fmt ts
    | Dpur (ts,tl) -> Format.fprintf fmt (protect_on inn "%a@ %a")
        Pretty.print_ts ts (Pp.print_list Pp.space (print_dity true)) tl
    | Dapp (its,[],rl) -> Format.fprintf fmt (protect_on inn "%a@ <%a>")
        Mlw_pretty.print_its its (Pp.print_list Pp.comma print_dreg) rl
    | Dapp (its,tl,rl) -> Format.fprintf fmt (protect_on inn "%a@ <%a>@ %a")
        Mlw_pretty.print_its its (Pp.print_list Pp.comma print_dreg) rl
          (Pp.print_list Pp.space (print_dity true)) tl
  and print_dreg fmt = function
    | Rreg (r,_) when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" Mlw_pretty.print_reg r
          Mlw_pretty.print_ity r.reg_ity
    | Rreg (r,_) -> Mlw_pretty.print_reg fmt r
    | Rvar { contents = Rtvs (tv,dity) }
      when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" print_rtvs tv (print_dity false) dity
    | Rvar { contents = Rtvs (tv,_) } -> print_rtvs fmt tv
    | Rvar { contents = Rval dreg } -> print_dreg fmt dreg
  in
  print_dity false fmt dity

(** Patterns *)

type dpattern = {
  dp_pat  : pre_ppattern;
  dp_dity : dity;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid
  | DPlapp of lsymbol * dpattern list
  | DPpapp of plsymbol * dpattern list
  | DPor   of dpattern * dpattern
  | DPas   of dpattern * preid

(** Specifications *)

type ghost = bool

type opaque = Stv.t

type dbinder = preid * ghost * opaque * dity

type 'a later = vsymbol Mstr.t -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec = {
  ds_pre     : pre;
  ds_post    : post;
  ds_xpost   : xpost;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_variant : variant list;
}

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec later

(** Expressions *)

type dlazy_op = DEand | DEor

type dexpr = {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEgpvar of pvsymbol
  | DEgpsym of psymbol
  | DEplapp of plsymbol * dexpr list
  | DElsapp of lsymbol * dexpr list
  | DEapply of dexpr * dexpr list
  | DEconstant of Number.constant
  | DEval of dval_decl * dexpr
  | DElet of dlet_defn * dexpr
  | DEfun of dfun_defn * dexpr
  | DErec of dfun_defn list * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEmatch of dexpr * (dpattern * dexpr) list
  | DEassign of plsymbol * dexpr * dexpr
  | DElazy of dlazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEtrue
  | DEfalse
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEfor of preid * dexpr * for_direction * dexpr * invariant later * dexpr
  | DEloop of variant list later * invariant later * dexpr
  | DEabsurd
  | DEassert of assertion_kind * term later
  | DEabstract of dexpr * dspec later
  | DEmark of preid * dexpr
  | DEghost of dexpr
  | DEany of dtype_c
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dval_decl = preid * ghost * dtype_v

and dlet_defn = preid * ghost * dexpr

and dfun_defn = preid * ghost * dbinder list * dity * dexpr * dspec later

(** Environment *)

type denv = {
  frozen : dity list;
  locals : (Stv.t option * dvty) Mstr.t;
}

let denv_empty = { frozen = []; locals = Mstr.empty }

let denv_add_val _ = assert false (* denv -> dval_decl -> denv *)

let denv_add_let _ = assert false (* denv -> dlet_defn -> denv *)

let denv_add_fun _ = assert false (* denv -> dfun_defn -> denv *)

let denv_prepare_rec _ = assert false (* denv -> preid -> dbinder list -> dity -> denv *)

let denv_verify_rec  _ = assert false (* denv -> preid -> unit *)

let denv_add_args _ = assert false (* denv -> dbinder list -> denv *)

let denv_add_pat _ = assert false (* denv -> dpattern -> denv *)

let denv_get _ = assert false (* denv -> string -> dexpr_node (** raises UnboundVar *) *)

let denv_get_opt _ = assert false (* denv -> string -> dexpr_node option *)

(** Constructors *)

let dpattern ?loc _ = ignore(loc); assert false (* ?loc:Loc.position -> dpattern_node -> dpattern *)

let dexpr ?loc _ = ignore (loc); assert false (* ?loc:Loc.position -> dexpr_node -> dexpr *)

(** Final stage *)

let expr     ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dexpr -> expr *)
let val_decl ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dval_decl -> let_sym *)
let let_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dlet_defn -> let_defn *)
let fun_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dfun_defn -> fun_defn *)
let rec_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dfun_defn list -> fun_defn list *)
