(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Wstdlib
open Term
open Ident
open Ty
open Pretty
open Ity
open Expr

let debug_trace_exec =
  Debug.register_info_flag "trace_exec"
    ~desc:"trace execution of code given by --exec or --eval"
(* print debug information during the interpretation of an expression *)

let debug_rac_values =
  Debug.register_info_flag "rac-values"
    ~desc:"print values that are taken into account during interpretation"

let debug_rac_check_sat =
  Debug.register_info_flag "rac-check-term-sat"
    ~desc:"satisfiability of terms in rac"
(* print debug information when checking the satisfiability of terms
   during rac *)

let debug_rac_check_term_result =
  Debug.register_info_flag "rac-check-term-result"
    ~desc:"print the result when terms are checked for validity"

let debug_disable_builtin_mach =
  Debug.register_flag "execute-no-builtin-mach"
    ~desc:"don't register builtins for modules under stdlib/mach"

let debug_array_as_update_chains_not_epsilon =
  Debug.register_flag "rac-array-as-update-chains"
    ~desc:"represent arrays in terms for RAC as chains of updates, not epsilons"

let pp_bindings ?(sep = Pp.semi) ?(pair_sep = Pp.arrow) ?(delims = Pp.(lbrace, rbrace))
    pp_key pp_value fmt l =
  let pp_binding fmt (k, v) =
    fprintf fmt "@[<h>%a%a%a@]" pp_key k pair_sep () pp_value v in
  fprintf fmt "%a%a%a" (fst delims) ()
    (Pp.print_list sep pp_binding)
    l (snd delims) ()

let pp_indent fmt =
  match Printexc.(backtrace_slots (get_callstack 100)) with
  | None -> ()
  | Some a ->
      let n = Pervasives.max 0 (Array.length a - 25) in
      let s = String.make (2 * n) ' ' in
      pp_print_string fmt s

(* Test for declarations program constants with logical counterparts. These values are
   kept in the [rsenv] environment *)
let is_prog_constant d =
  let open Pdecl in
  match d.pd_node with
  | PDlet (LDsym (_, {c_cty= {cty_args= []}})) -> true
  | _ -> false

let ity_components ity = match ity.ity_node with
  | Ityapp (ts, l1, l2)
  | Ityreg {reg_its= ts; reg_args= l1; reg_regs= l2} ->
      ts, l1, l2
  | _ -> failwith "ity_components"

let is_range_ty ty =
  let its, _, _ = ity_components (ity_of_ty ty) in
  Ty.is_range_type_def its.its_def

(******************************************************************************)
(*                              EXCEPTIONS                                    *)
(******************************************************************************)

exception NoMatch
exception Undetermined
exception CannotCompute of {reason: string}
exception NotNum
exception CannotFind of (Env.pathname * string * string)

let cannot_compute f =
  kasprintf (fun reason -> raise (CannotCompute {reason})) f

(******************************************************************************)
(*                                VALUES                                      *)
(******************************************************************************)

type float_mode = Mlmpfr_wrapper.mpfr_rnd_t

type big_float = Mlmpfr_wrapper.mpfr_float

let mode_to_string m =
  let open Mlmpfr_wrapper in
  match m with
  | To_Nearest -> "RNE"
  | Away_From_Zero -> "RNA"
  | Toward_Plus_Infinity -> "RTP"
  | Toward_Minus_Infinity -> "RTN"
  | Toward_Zero -> "RTZ"
  | Faithful -> assert false

module rec Value : sig
  type value = {v_desc: value_desc; v_ty: ty}
  and value_desc =
    | Vconstr of rsymbol * rsymbol list * field list
    | Vnum of BigInt.t
    | Vreal of Big_real.real
    | Vfloat_mode of float_mode
    | Vfloat of big_float
    | Vstring of string
    | Vbool of bool
    | Vproj of lsymbol * value
    | Varray of value array
    | Vfun of value Mvs.t (* closure *) * vsymbol * expr
    | Vpurefun of ty (* keys *) * value Mv.t * value
    | Vterm of term (* ghost values *)
    | Vundefined
  and field = Field of value ref
  val compare_values : value -> value -> int
end = struct
  type value = {v_desc: value_desc; v_ty: ty}
  and value_desc =
    | Vconstr of rsymbol * rsymbol list * field list
    | Vnum of BigInt.t
    | Vreal of Big_real.real
    | Vfloat_mode of float_mode
    | Vfloat of big_float
    | Vstring of string
    | Vbool of bool
    | Vproj of lsymbol * value
    | Varray of value array
    | Vfun of value Mvs.t (* closure *) * vsymbol * expr
    | Vpurefun of ty (* keys *) * value Mv.t * value
    | Vterm of term
    | Vundefined
  and field = Field of value ref

  open Util

  let rec compare_values v1 v2 =
    if v1.v_desc = Vundefined then
      cannot_compute "undefined value of type %a cannot be compared" print_ty v1.v_ty;
    if v2.v_desc = Vundefined then
      cannot_compute "undefined value of type %a cannot be compared" print_ty v2.v_ty;
    let v_ty v = v.v_ty and v_desc v = v.v_desc in
    cmp [cmptr v_ty ty_compare; cmptr v_desc compare_desc] v1 v2
  and compare_desc d1 d2 =
    match d1, d2 with
    | Vproj (ls1, v1), Vproj (ls2, v2) ->
        cmp [cmptr fst ls_compare; cmptr snd compare_values] (ls1, v1) (ls2, v2)
    | Vproj _, _ -> -1 | _, Vproj _ -> 1
    | Vconstr (rs1, _, fs1), Vconstr (rs2, _, fs2) ->
        let field_get (Field f) = !f in
        let cmp_fields = cmp_lists [cmptr field_get compare_values] in
        cmp [cmptr fst rs_compare; cmptr snd cmp_fields] (rs1, fs1) (rs2, fs2)
    | Vconstr _, _ -> -1 | _, Vconstr _ -> 1
    | Vnum i1, Vnum i2 ->
        BigInt.compare i1 i2
    | Vnum _, _ -> -1 | _, Vnum _ -> 1
    | Vreal r1, Vreal r2 ->
        Big_real.(if eq r1 r2 then 0 else if lt r1 r2 then -1 else 1)
    | Vreal _, _ -> -1 | _, Vreal _ -> 1
    | Vfloat_mode m1, Vfloat_mode m2 ->
        compare m1 m2
    | Vfloat_mode _, _ -> -1 | _, Vfloat_mode _ -> 1
    | Vfloat f1, Vfloat f2 ->
        Mlmpfr_wrapper.(if equal_p f1 f2 then 0 else if less_p f1 f2 then -1 else 1)
    | Vfloat _, _ -> -1 | _, Vfloat _ -> 1
    | Vstring s1, Vstring s2 ->
        String.compare s1 s2
    | Vstring _, _ -> -1 | _, Vstring _ -> 1
    | Vbool b1, Vbool b2 ->
        compare b1 b2
    | Vbool _, _ -> -1 | _, Vbool _ -> 1
    | Vfun _, Vfun _ ->
        failwith "Value.compare: Vfun"
    | Vfun _, _ -> -1 | _, Vfun _ -> 1
    | Vpurefun (ty1, mv1, v1), Vpurefun (ty2, mv2, v2) ->
        cmp [
          cmptr (fun (x,_,_) -> x) ty_compare;
          cmptr (fun (_,x,_) -> x) (Mv.compare compare_values);
          cmptr (fun (_,_,x) -> x) compare_values;
        ] (ty1, mv1, v1) (ty2, mv2, v2)
    | Vpurefun _, _ -> -1 | _, Vpurefun _ -> 1
    | Vterm t1, Vterm t2 ->
        t_compare t1 t2
    | Vterm _, _ -> -1 | _, Vterm _ -> 1
    | Varray a1, Varray a2 ->
        cmp [
          cmptr Array.length (-);
          cmptr Array.to_list (cmp_lists [cmptr (fun x -> x) compare_values]);
        ] a1 a2
    | Vundefined, _ | _, Vundefined -> assert false
end
and Mv : Extmap.S with type key = Value.value =
  Extmap.Make (struct
    type t = Value.value
    let compare = Value.compare_values
  end)

include Value

let value ty desc = {v_desc= desc; v_ty= ty}
let field v = Field (ref v)
let v_desc v = v.v_desc
let v_ty v = v.v_ty
let field_get (Field r) = r.contents
let field_set (Field r) v = r := v

let int_value n = value ty_int (Vnum n)

let range_value ity n =
  begin match ity_components ity with
  | { its_def = Range r }, _, _ ->
      begin
        try
          Number.(check_range { il_kind = ILitUnk; il_int = n } r);
        with Number.OutOfRange _ ->
          cannot_compute "%s is out of range" (BigInt.to_string n)
      end
  | _ -> ()
  end;
  value (ty_of_ity ity) (Vnum n)

let string_value s = value ty_str (Vstring s)
let bool_value b = value ty_bool (Vbool b)
let proj_value ity ls v =
  value (ty_of_ity ity) (Vproj (ls, v))
let constr_value ity rs fs vl =
  value (ty_of_ity ity) (Vconstr (rs, fs, List.map field vl))
let purefun_value ~result_ity ~arg_ity mv v =
  value (ty_of_ity result_ity) (Vpurefun (ty_of_ity arg_ity, mv, v))
let unit_value =
  value (ty_tuple []) (Vconstr (Expr.rs_void, [], []))
let undefined_value ity =
  value (ty_of_ity ity) Vundefined

let rec print_value fmt v =
  if Debug.test_flag (Debug.lookup_flag "print_types") then
    fprintf fmt "(%a: %a)" print_value' v print_ty (v_ty v)
  else
    print_value' fmt v

and print_value' fmt v =
  match v.v_desc with
  | Vnum n ->
      if BigInt.ge n BigInt.zero then
        fprintf fmt "%s" (BigInt.to_string n)
      else
        fprintf fmt "(%s)" (BigInt.to_string n)
  | Vbool b -> fprintf fmt "%b" b
  | Vreal r -> Big_real.print_real fmt r
  | Vfloat f ->
      (* Getting "@" is intentional in mlmpfr library for bases higher than 10.
         So, we keep this notation. *)
      let hexadecimal = Mlmpfr_wrapper.get_formatted_str ~base:16 f in
      let decimal = Mlmpfr_wrapper.get_formatted_str ~base:10 f in
      fprintf fmt "%s (%s)" decimal hexadecimal
  | Vfloat_mode m -> fprintf fmt "%s" (mode_to_string m)
  | Vstring s -> Constant.print_string_def fmt s
  | Vfun (mvs, vs, e) ->
      fprintf fmt "@[<h>@[<v3>(fun %a -> %a)@]%a@]"
        print_vs vs print_expr e
        Pp.(let start = constant_formatted "@ with " in
            print_list_delim ~start ~sep:comma ~stop:nothing
              (print_pair_delim nothing equal nothing print_vs print_value))
        (Mvs.bindings mvs)
  | Vproj (ls, v) ->
      fprintf fmt "{%a => %a}" print_ls ls print_value v
  | Vconstr (rs, fs, vs) ->
      if is_rs_tuple rs then
        fprintf fmt "@[<hv1>(%a)@]" (Pp.print_list Pp.comma print_field) vs
      else if Strings.has_suffix "'mk" rs.rs_name.id_string then
        let print_field fmt (rs, v) = fprintf fmt "@[%a=@ %a@]" print_rs rs print_field v in
        fprintf fmt "@[<hv1>{%a}@]" (Pp.print_list Pp.semi print_field)
          (List.combine fs vs)
      else if vs = [] then
        print_rs fmt rs
      else
        fprintf fmt "@[<h>(%a%a)@]" print_rs rs
          Pp.(print_list_pre space print_value) (List.map field_get vs)
  | Varray a ->
      fprintf fmt "@[[%a]@]"
        (Pp.print_list Pp.semi print_value) (Array.to_list a)
  | Vpurefun (_, mv, v) ->
      fprintf fmt "@[[|%a; _ -> %a|]@]" (pp_bindings ~delims:Pp.(nothing,nothing) print_value print_value)
        (Mv.bindings mv) print_value v
  | Vterm t ->
      print_term fmt t
  | Vundefined -> fprintf fmt "UNDEFINED"

and print_field fmt f = print_value fmt (field_get f)

let rec snapshot v =
  let v_desc = match v.v_desc with
    | Vconstr (rs, fs, vs) -> Vconstr (rs, fs, List.map snapshot_field vs)
    | Vfun (cl, vs, e) -> Vfun (Mvs.map snapshot cl, vs, e)
    | Vpurefun (ty, mv, v) ->
        let mv = Mv.(fold (fun k v -> add (snapshot k) (snapshot v)) mv empty) in
        Vpurefun (ty, mv, snapshot v)
    | Vproj (rs, v) -> Vproj (rs, snapshot v)
    | Varray a -> Varray (Array.map snapshot a)
    | Vfloat _ | Vstring _ | Vterm _ | Vbool _ | Vreal _
    | Vfloat_mode _ | Vnum _ | Vundefined as vd -> vd in
  {v with v_desc}

and snapshot_field f =
  field (snapshot (field_get f))

let snapshot_oldies oldies vsenv =
  let aux old_pv pv =
    Mvs.add old_pv.pv_vs (snapshot (Mvs.find pv.pv_vs vsenv)) in
  Mpv.fold aux oldies vsenv

let t_undefined ty =
  t_eps_close (create_vsymbol (id_fresh "undefined") ty) t_true

(** [ty_app_arg ts nth ty] returns the nth argument in the type application [ty]. Fails
   when ty is not a type application of [ts] *)
let ty_app_arg ts ix ty = match ty.ty_node with
  | Tyapp (ts', ty_args) when ts_equal ts' ts ->
      List.nth ty_args ix
  | _ -> kasprintf failwith "@[<h>ty_arg: not a type application of %a: %a@]"
           print_ts ts print_ty ty

(******************************************************************************)
(*                                 RESULT                                     *)
(******************************************************************************)

type result =
  | Normal of value
  | Excep of xsymbol * value
  | Irred of expr

let print_logic_result fmt r =
  match r with
  | Normal v -> fprintf fmt "@[%a@]" print_value v
  | Excep (x, v) ->
      fprintf fmt "@[exception %s(@[%a@])@]" x.xs_name.id_string print_value v
  | Irred e -> fprintf fmt "@[Cannot execute expression@ @[%a@]@]" print_expr e

(******************************************************************************)
(*                                  ENV                                       *)
(******************************************************************************)

type rac_prover = Rac_prover of {
    command: string;
    driver: Driver.driver;
    limit: Call_provers.resource_limit;
  }

let rac_prover ~command driver limit =
  Rac_prover {command; driver; limit}

type rac_reduce_config = {
  rac_trans: Task.task Trans.tlist option;
  rac_prover: rac_prover option;
  rac_try_negate: bool;
}

let rac_reduce_config ?trans:rac_trans ?prover:rac_prover ?try_negate:(rac_try_negate=false) () =
  {rac_trans; rac_prover; rac_try_negate}

let rac_reduce_config_lit config env ?trans ?prover ?try_negate () =
  let trans =
    let aux s = Trans.lookup_transform_l s env in
    Opt.map aux trans in
  let prover =
    let aux prover_string =
      let name, limit_time, limit_mem =
        match Strings.split ',' prover_string with
        | [name; limit_time; limit_mem] ->
            name, int_of_string limit_time, int_of_string limit_mem
        | [name; limit_time] ->
            name, int_of_string limit_time, 1000
        | [name] -> name, 1, 1000
        | _ -> failwith "RAC reduce prover config must have format <prover shortcut>[,<time limit>[,<mem limit>]]" in
      let prover = Whyconf.filter_one_prover config (Whyconf.parse_filter_prover name) in
      let command = String.concat " " (prover.Whyconf.command :: prover.Whyconf.extra_options) in
      let driver = Whyconf.load_driver (Whyconf.get_main config) env prover in
      let limit = Call_provers.{empty_limit with limit_time; limit_mem} in
      rac_prover ~command driver limit in
    Opt.map aux prover in
  rac_reduce_config ?trans ?prover ?try_negate ()

(******************************************************************************)
(*                             Execution log                                  *)
(******************************************************************************)

module type Log = sig
  type exec_kind = ExecAbstract | ExecConcrete

  type log_entry_desc = private
    | Val_assumed of (ident * value)
    | Const_init of ident
    | Exec_call of (rsymbol option * value Mvs.t  * exec_kind)
    | Exec_pure of (lsymbol * exec_kind)
    | Exec_any of (rsymbol option * value Mvs.t)
    | Iter_loop of exec_kind
    | Exec_main of (rsymbol * value Mvs.t * value Mrs.t)
    | Exec_stucked of (string * value Mid.t)
    | Exec_failed of (string * value Mid.t)
    | Exec_ended

  type log_entry = private {
    log_desc : log_entry_desc;
    log_loc  : Loc.position option;
  }

  type exec_log
  type log_uc

  val log_val : log_uc -> ident -> value -> Loc.position option -> unit
  val log_const : log_uc -> ident -> Loc.position option -> unit
  val log_call : log_uc -> rsymbol option -> value Mvs.t ->
                 exec_kind -> Loc.position option -> unit
  val log_pure_call : log_uc -> lsymbol -> exec_kind ->
                      Loc.position option -> unit
  val log_any_call : log_uc -> rsymbol option -> value Mvs.t ->
                     Loc.position option -> unit
  val log_iter_loop : log_uc -> exec_kind -> Loc.position option -> unit
  val log_exec_main : log_uc -> rsymbol -> value Mvs.t -> value Mrs.t ->
                      Loc.position option -> unit
  val log_failed : log_uc -> string -> value Mid.t ->
                   Loc.position option -> unit
  val log_stucked : log_uc -> string -> value Mid.t ->
                    Loc.position option -> unit
  val log_exec_ended : log_uc -> Loc.position option -> unit
  val empty_log_uc : unit -> log_uc
  val empty_log : exec_log
  val close_log : log_uc -> exec_log
  val sort_log_by_loc : exec_log -> log_entry list Mint.t Mstr.t
  val print_log : ?verb_lvl:int -> json:bool -> exec_log Pp.pp
end

module Log : Log = struct
  type exec_kind = ExecAbstract | ExecConcrete

  type log_entry_desc =
    | Val_assumed of (ident * value)
    | Const_init of ident
    | Exec_call of (rsymbol option * value Mvs.t  * exec_kind)
    | Exec_pure of (lsymbol * exec_kind)
    | Exec_any of (rsymbol option * value Mvs.t)
    | Iter_loop of exec_kind
    | Exec_main of (rsymbol * value Mvs.t * value Mrs.t)
    | Exec_stucked of (string * value Mid.t)
    | Exec_failed of (string * value Mid.t)
    | Exec_ended

  type log_entry = {
    log_desc : log_entry_desc;
    log_loc  : Loc.position option;
  }

  type log_uc = (log_entry list) ref
  (* new log elements are added to the head of the list *)

  type exec_log = log_entry list
  (* supposed to contain the reverse log_uc contents after close_log *)

  let empty_log_uc () = ref []

  let empty_log = []

  let log_entry log_uc log_desc log_loc =
    log_uc := {log_desc; log_loc} :: !log_uc

  let log_val log_uc id v loc =
    log_entry log_uc (Val_assumed (id,v)) loc

  let log_const log_uc id loc =
    log_entry log_uc (Const_init id) loc

  let log_call log_uc rs mvs kind loc =
    log_entry log_uc (Exec_call (rs,mvs,kind)) loc

  let log_pure_call log_uc ls kind loc =
    log_entry log_uc (Exec_pure (ls,kind)) loc

  let log_any_call log_uc rs mvs loc =
    log_entry log_uc (Exec_any (rs,mvs)) loc

  let log_iter_loop log_uc kind loc =
    log_entry log_uc (Iter_loop kind) loc

  let log_exec_main log_uc rs mvs mrs loc =
    log_entry log_uc (Exec_main (rs,mvs,mrs)) loc

  let log_failed log_uc s mvs loc =
    log_entry log_uc (Exec_failed (s,mvs)) loc

  let log_stucked log_uc s mvs loc =
    log_entry log_uc (Exec_stucked (s,mvs)) loc

  let log_exec_ended log_uc loc =
    log_entry log_uc Exec_ended loc

  let close_log log_uc = List.rev !log_uc

  let exec_kind_to_string ?(cap=true) = function
    | ExecAbstract -> if cap then "Abstract" else "abstract"
    | ExecConcrete -> if cap then "Concrete" else "concrete"

  (** Partition a list of elements into lists of pairs, of consecutive
      elements with the same value for f *)
  let rec consecutives key ?(sofar=[]) ?current xs =
    let to_list = function Some (k, xs) -> [Some k, List.rev xs] | None -> [] in
    match xs with
    | [] -> List.rev (to_list current @ sofar)
    | x :: xs -> match key x with
      | None -> consecutives key ~sofar:((None, [x]) :: to_list current @ sofar) xs
      | Some k -> match current with
        | None ->
            consecutives key ~sofar ~current:(k, [x]) xs
        | Some (k', xs') when k' = k ->
            consecutives key ~sofar ~current:(k, x::xs') xs
        | Some _ ->
            consecutives key ~sofar:(to_list current @ sofar) ~current:(k, [x]) xs

  let print_log_entry_desc fmt e =
    let print_assoc key2string fmt (k,v) =
      fprintf fmt "@[%a = %a@]"
        print_decoded (key2string k) print_value v in
    let print_list key2string =
      Pp.print_list_pre Pp.newline (print_assoc key2string) in
    let vs2string vs = vs.vs_name.id_string in
    let rs2string rs = rs.rs_name.id_string in
    let id2string id = id.id_string in
    match e.log_desc with
    | Val_assumed (id, v) ->
        fprintf fmt "@[<h2>%a = %a@]" print_decoded id.id_string print_value v;
    | Const_init id ->
        fprintf fmt "@[<h2>Constant %a initialization@]" print_decoded id.id_string;
    | Exec_call (None, mvs, k) ->
        fprintf fmt "@[<h2>%s execution of anonymous function with args:%a@]"
          (exec_kind_to_string k)
          (print_list vs2string) (Mvs.bindings mvs)
    | Exec_call (Some rs, mvs, k) ->
        fprintf fmt "@[<h2>%s execution of function `%a` with args:%a@]"
          (exec_kind_to_string k)
          print_decoded rs.rs_name.id_string
          (print_list vs2string) (Mvs.bindings mvs)
    | Exec_pure (ls,k) ->
        fprintf fmt "@[<h2>%s execution of function `%a`@]" (exec_kind_to_string k)
          print_decoded ls.ls_name.id_string
    | Exec_any (rs,mvs) ->
         fprintf fmt
           "@[<h2>(abstract) execution of unimplemented function%s`%a`%s%a@]"
           (if rs = None then "" else " ")
           (Pp.print_option Ident.print_decoded)
           (Opt.map (fun rs -> rs.rs_name.id_string) rs)
           (if Mvs.is_empty mvs then "" else " with args:")
           (print_list vs2string) (Mvs.bindings mvs)
    | Iter_loop k ->
        fprintf fmt "@[<h2>%s iteration of loop@]" (exec_kind_to_string k)
    | Exec_main (rs, mvs, mrs) ->
        fprintf fmt "@[<h2>Execution of main function `%a` with env:%a%a@]"
          print_decoded rs.rs_name.id_string
          (print_list vs2string) (Mvs.bindings mvs)
          (print_list rs2string) (Mrs.bindings mrs)
    | Exec_failed (msg,mid) ->
       fprintf fmt "@[<h2>Property failure, %s with:%a@]"
         msg (print_list id2string) (Mid.bindings mid)
    | Exec_stucked (msg,mid) ->
       fprintf fmt "@[<h2>Execution got stuck, %s with:%a@]"
         msg (print_list id2string) (Mid.bindings mid)
    | Exec_ended ->
        fprintf fmt "@[<h2>Execution of main function terminated normally@]"

  (** verbosity level:
     1 : just imported values
     2 : + execution of function calls
     3 : + execution of loops
     4 : + termination of execution
     5 : + log information about initialization of global vars
   *)
  let print_log ?(verb_lvl=4) ~json fmt entry_log =
    if json then
      let open Json_base in
      let string f = kasprintf (fun s -> String s) f in
      let print_json_kind fmt = function
        | ExecAbstract -> print_json fmt (string "ABSTRACT")
        | ExecConcrete -> print_json fmt (string "CONCRETE") in
      let print_key_value key2string fmt (k,v) =
        fprintf fmt "@[@[<hv1>{%a;@ %a@]}@]"
          (print_json_field "name" print_json) (String (key2string k))
          (print_json_field "value" print_value) v in
      let vs2string vs = vs.vs_name.id_string in
      let id2string id = id.id_string in
      let print_log_entry fmt = function
        | Val_assumed (id, v) ->
            fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "VAL_ASSUMED")
              (print_json_field "vs" print_json)
              (string "%a" print_decoded id.id_string)
              (print_json_field "value" print_value) v
        | Const_init id ->
            fprintf fmt "@[@[<hv1>{%a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "CONST_INIT")
              (print_json_field "id" print_json)
              (string "%a" print_decoded id.id_string)
        | Exec_call (ors, mvs, kind) ->
            fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "EXEC_CALL")
              (print_json_field "rs" print_json) (match ors with
                  | Some rs -> string "%a" print_decoded rs.rs_name.id_string
                  | None -> Null)
              (print_json_field "exec" print_json_kind) kind
              (print_json_field "args" (list (print_key_value vs2string)))
              (Mvs.bindings mvs)
        | Exec_pure (ls, kind) ->
            fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "EXEC_PURE")
              (print_json_field "ls" print_json) (string "%a" print_ls ls)
              (print_json_field "exec" print_json_kind) kind
        | Exec_any (ors,mvs) ->
            fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "EXEC_ANY")
              (print_json_field "rs" print_json) (match ors with
                  | Some rs -> string "%a" print_decoded rs.rs_name.id_string
                  | None -> Null)
              (print_json_field "args" (list (print_key_value vs2string)))
              (Mvs.bindings mvs)
        | Iter_loop kind ->
            fprintf fmt "@[@[<hv1>{%a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "ITER_LOOP")
              (print_json_field "exec" print_json_kind) kind
        | Exec_main (rs,mvs,mrs) ->
           let mid = Mvs.fold (fun vs v mid -> Mid.add vs.vs_name v mid) mvs Mid.empty in
           let mid = Mrs.fold (fun rs v mid -> Mid.add rs.rs_name v mid) mrs mid in
           fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a@]}@]"
             (print_json_field "kind" print_json) (string "EXEC_MAIN")
             (print_json_field "rs" print_json)
             (string "%a" print_decoded rs.rs_name.id_string)
             (print_json_field "env" (list (print_key_value id2string)))
             (Mid.bindings mid)
        | Exec_failed (reason,mid) ->
            fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "FAILED")
              (print_json_field "reason" print_json) (String reason)
              (print_json_field "state" (list (print_key_value id2string)))
              (Mid.bindings mid)
        | Exec_stucked (reason,mid) ->
            fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a@]}@]"
              (print_json_field "kind" print_json) (string "STUCKED")
              (print_json_field "reason" print_json) (String reason)
              (print_json_field "state" (list (print_key_value id2string)))
              (Mid.bindings mid)
        | Exec_ended ->
            fprintf fmt "@[@[<hv1>{%a@]}@]"
              (print_json_field "kind" print_json) (string "ENDED") in
      let print_json_entry fmt e =
        fprintf fmt "@[@[<hv1>{@[<hv2>%a@];@ @[<hv2>%a@]@]}@]"
          (Pp.print_option_or_default "NOLOC"
             (print_json_field "loc" print_json_loc)) e.log_loc
          (print_json_field "entry" print_log_entry) e.log_desc in
      fprintf fmt "@[@[<hv1>[%a@]@]"
        Pp.(print_list comma print_json_entry) entry_log
    else
      let entry_log = List.filter (fun le ->
            match le.log_desc with
            | Val_assumed _ | Const_init _ | Exec_main _ -> true
            | Exec_call _ | Exec_pure _ | Exec_any _
                 when verb_lvl > 1 -> true
            | Iter_loop _ when verb_lvl > 2 -> true
            | Exec_failed _ | Exec_stucked _ | Exec_ended
                 when verb_lvl > 3 -> true
            | _ -> false) entry_log in
      (* if verb_lvl < 5 remove log about initialization of global vars *)
      let entry_log =
        if verb_lvl < 5 then
          Lists.drop_while (fun le ->
              match le.log_desc with
                Exec_main _ -> false | _ -> true) entry_log
        else entry_log in
      let entry_log =
        let on_file e = Opt.map (fun (f,_,_,_) -> f) (Opt.map Loc.get e.log_loc) in
        let on_line e = Opt.map (fun (_,l,_,_) -> l) (Opt.map Loc.get e.log_loc) in
        List.map (fun (f, es) -> f, consecutives on_line es)
          (consecutives on_file entry_log) in
      let pp_entries = Pp.(print_list newline print_log_entry_desc) in
      let pp_lines fmt (opt_line, entries) = match opt_line with
        | Some line -> fprintf fmt "@[<v2>Line %d:@\n%a@]" line pp_entries entries
        | None -> pp_entries fmt entries in
      let pp_files fmt (opt_file, l) = match opt_file with
        | Some file -> fprintf fmt "@[<v2>File %s:@\n%a@]" (Filename.basename file) Pp.(print_list newline pp_lines) l
        | None -> fprintf fmt "@[<v4>Unknown location:@\n%a@]" Pp.(print_list newline pp_lines) l in
      Pp.(print_list newline pp_files) fmt entry_log

  let sort_log_by_loc log =
    let insert f l e sofar =
      let insert_line opt_l =
        let l = Opt.get_def [] opt_l in
        Some (e :: l) in
      let insert_file opt_mf =
        let mf = Opt.get_def Mint.empty opt_mf in
        let res = Mint.change insert_line l mf in
        Some res in
      Mstr.change insert_file f sofar in
    let aux entry sofar = match entry.log_loc with
      | Some loc when not (Loc.equal loc Loc.dummy_position) ->
          let f, l, _, _ = Loc.get loc in
          insert f l entry sofar
      | _ -> sofar in
    Mstr.map (Mint.map List.rev)
      (List.fold_right aux log Mstr.empty)

end

(******************************************************************************)
(*                              RAC configuration                             *)
(******************************************************************************)

type get_value = ?loc:Loc.position -> ident -> ity -> value option

type rac_config = {
  do_rac              : bool;
  rac_abstract        : bool;
  skip_cannot_compute : bool; (* skip if it cannot compute, when possible *)
  rac_reduce          : rac_reduce_config;
  get_value           : get_value;
  log_uc              : Log.log_uc;
  timelimit           : float option; (* seconds *)
}

let default_get_value ?loc:_ _ _ = None

let rac_config ~do_rac ~abstract:rac_abstract
      ?(skip_cannot_compute=true)
      ?reduce:rac_reduce
      ?(get_value=default_get_value) ?timelimit () =
  let rac_reduce = match rac_reduce with
    | Some r -> r
    | None -> rac_reduce_config () in
  {do_rac; rac_abstract; rac_reduce; log_uc= Log.empty_log_uc ();
   get_value; skip_cannot_compute; timelimit }

type bunch = term list list ref
type premises = bunch list ref

let with_push_premises (premises: premises) f =
  premises := (ref []) :: !premises;
  let res = f () in
  premises := List.tl !premises;
  res

let add_premises ts premises =
  let head = List.hd !premises in
  head := ts :: !head

let fold_premises f premises init =
  let fold_terms f ts sofar = List.fold_left f sofar ts in
  let fold_bunch f bunch init = List.fold_right (fold_terms f) !bunch init in
  List.fold_right (fold_bunch f) !premises init

type env = {
  pmodule : Pmodule.pmodule;
  funenv  : cexp Mrs.t;
  vsenv   : value Mvs.t;
  rsenv   : value Mrs.t; (* global constants *)
  premises: premises;
  env     : Env.env;
  rac     : rac_config;
}

let default_env env rac pmodule =
  { pmodule; rac; env; funenv= Mrs.empty; vsenv= Mvs.empty; rsenv= Mrs.empty;
    premises= ref [ref []] }

let register_used_value env loc id value =
  Log.log_val env.rac.log_uc id (snapshot value) loc

let register_const_init env loc id =
  Log.log_const env.rac.log_uc id loc

let register_call env loc rs mvs kind =
  Log.log_call env.rac.log_uc rs (Mvs.map snapshot mvs) kind loc

let register_pure_call env loc ls kind =
  Log.log_pure_call env.rac.log_uc ls kind loc

let register_any_call env loc rs mvs =
  Log.log_any_call env.rac.log_uc rs (Mvs.map snapshot mvs) loc

let register_iter_loop env loc kind =
  Log.log_iter_loop env.rac.log_uc kind loc

let register_exec_main env rs =
  Log.log_exec_main env.rac.log_uc rs (Mvs.map snapshot env.vsenv)
    env.rsenv rs.rs_name.id_loc

let register_failure env loc reason mvs =
  Log.log_failed env.rac.log_uc reason (Mid.map snapshot mvs) loc

let register_stucked env loc reason mvs =
  Log.log_stucked env.rac.log_uc reason (Mid.map snapshot mvs) loc

let register_ended env loc =
  Log.log_exec_ended env.rac.log_uc loc

let snapshot_vsenv = Mvs.map snapshot

let add_local_funs locals env =
  let add acc (rs, ce) = Mrs.add rs ce acc in
  let funenv = List.fold_left add env.funenv locals in
  {env with funenv}

let bind_vs vs v env = {env with vsenv= Mvs.add vs v env.vsenv}
let bind_rs rs v env = {env with rsenv= Mrs.add rs v env.rsenv}
let bind_pvs ?register pv v_t env =
  let env = bind_vs pv.pv_vs v_t env in
  Opt.iter (fun r -> r pv.pv_vs.vs_name v_t) register;
  env
let multibind_pvs ?register l tl env =
  List.fold_left2 (fun env pv v -> bind_pvs ?register pv v env) env l tl

(******************************************************************************)
(*                                BUILTINS                                    *)
(******************************************************************************)

let big_int_of_const i = i.Number.il_int
let big_int_of_value v = match v.v_desc with Vnum i -> i | _ -> raise NotNum

let eval_int_op op ls l =
  match List.map v_desc l with
  | [Vnum i1; Vnum i2] -> (
      match op i1 i2 with
      | exception Division_by_zero -> None
      | v -> Some (range_value ls.rs_cty.cty_result v) )
  | _ -> assert false

let eval_int_uop op ls l =
  let v_desc = match List.map v_desc l with
    | [Vnum i1] -> Vnum (op i1)
    | _ -> assert false in
  Some {v_desc; v_ty=ty_of_ity ls.rs_cty.cty_result}

let eval_int_rel op _ l =
  let v_desc = match List.map v_desc l with
    | [Vnum i1; Vnum i2] -> Vbool (op i1 i2)
    | _ -> assert false in
  Some {v_desc; v_ty= ty_bool}

(* This initialize Mpfr for float32 behavior *)
let initialize_float32 () =
  let open Mlmpfr_wrapper in
  set_default_prec 24 ; set_emin (-148) ; set_emax 128

(* This initialize Mpfr for float64 behavior *)
let initialize_float64 () =
  let open Mlmpfr_wrapper in
  set_default_prec 53 ; set_emin (-1073) ; set_emax 1024

type 'a float_arity =
  | Mode1 : (float_mode -> big_float -> big_float) float_arity (* Unary op *)
  | Mode2 : (float_mode -> big_float -> big_float -> big_float) float_arity (* binary op *)
  | Mode3
      : (float_mode -> big_float -> big_float -> big_float -> big_float)
        float_arity (* ternary op *)
  | Mode_rel : (big_float -> big_float -> bool) float_arity (* binary predicates *)
  | Mode_rel1 : (big_float -> bool) float_arity

let use_float_format (float_format : int) =
  match float_format with
  | 32 -> initialize_float32 ()
  | 64 -> initialize_float64 ()
  | _ -> cannot_compute "float format is unknown: %d" float_format

let eval_float :
  type a. tysymbol -> int -> a float_arity -> a -> rsymbol -> value list -> value option =
  fun tys_result float_format arity op _ vs ->
  (* Set the exponent depending on Float type that are used: 32 or 64 *)
  let ty_result = ty_app tys_result [] in
  use_float_format float_format ;
  try
    let v_desc =
      let open Mlmpfr_wrapper in
      match arity, List.map v_desc vs with
      | Mode1, [Vfloat_mode mode; Vfloat f] ->
          (* Subnormalize used to simulate IEEE behavior *)
          Vfloat (subnormalize ~rnd:mode (op mode f))
      | Mode2, [Vfloat_mode mode; Vfloat f1; Vfloat f2] ->
          Vfloat (subnormalize ~rnd:mode (op mode f1 f2))
      | Mode3, [Vfloat_mode mode; Vfloat f1; Vfloat f2; Vfloat f3] ->
          Vfloat (subnormalize ~rnd:mode (op mode f1 f2 f3))
      | Mode_rel, [Vfloat f1; Vfloat f2] -> Vbool (op f1 f2)
      | Mode_rel1, [Vfloat f] -> Vbool (op f)
      | _ -> cannot_compute "arity error in float operation" in
    Some {v_desc; v_ty= ty_result}
  with Mlmpfr_wrapper.Not_Implemented ->
    cannot_compute "mlmpfr wrapper is not implemented"

type 'a real_arity =
  | Modeconst : Big_real.real real_arity
  | Mode1r : (Big_real.real -> Big_real.real) real_arity
  | Mode2r : (Big_real.real -> Big_real.real -> Big_real.real) real_arity
  | Mode_relr : (Big_real.real -> Big_real.real -> bool) real_arity

let eval_real : type a. a real_arity -> a -> rsymbol -> value list -> value option =
  fun ty op _ l ->
  try
    let v_desc = match ty, List.map v_desc l with
      | Mode1r, [Vreal r] -> Vreal (op r)
      | Mode2r, [Vreal r1; Vreal r2] -> Vreal (op r1 r2)
      | Mode_relr, [Vreal r1; Vreal r2] -> Vbool (op r1 r2)
      | Modeconst, [] -> Vreal op
      | _ -> cannot_compute "arity error in real operation" in
    Some {v_desc; v_ty= ty_real}
  with
  | Big_real.Undetermined ->
      (* Cannot decide interval comparison *)
      cannot_compute "computation on reals is undetermined"
  | Mlmpfr_wrapper.Not_Implemented ->
      cannot_compute "mlmpfr wrapper is not implemented"

let builtin_progs = Hrs.create 17

type builtin = Builtin_module of {
  path: string list;
  name: string;
  types: (string * (Pdecl.known_map -> itysymbol -> unit)) list;
  values: Pmodule.pmodule -> (string * (rsymbol -> value list -> value option)) list;
}

let dummy_type (_:Pdecl.known_map) (_:itysymbol) = ()

let builtin path name values =
  Builtin_module {path; name; types=[]; values= fun _ -> values}

let builtin1t path name (type_name, type_def) values =
  let values = fun pm ->
    let its = Pmodule.(ns_find_its pm.mod_export [type_name]) in
    values its.its_ts in
  Builtin_module {path; name; types= [type_name, type_def]; values}

(* Described as a function so that this code is not executed outside of
   why3execute. *)

(** Description of modules *)
let built_in_modules () =
  let int_ops = [
    op_infix "+",      eval_int_op BigInt.add;
    (* defined as x+(-y)
       op_infix "-",   eval_int_op BigInt.sub; *)
    op_infix "*",      eval_int_op BigInt.mul;
    op_prefix "-",     eval_int_uop BigInt.minus;
    op_infix "=",      eval_int_rel BigInt.eq;
    op_infix "<",      eval_int_rel BigInt.lt;
    op_infix "<=",     eval_int_rel BigInt.le;
    op_infix ">",      eval_int_rel BigInt.gt;
    op_infix ">=",     eval_int_rel BigInt.ge;
  ] in
  let bounded_int_ops = int_ops @ [
    "of_int",          eval_int_uop (fun x -> x);
    "to_int",          eval_int_uop (fun x -> x);
    op_infix "-",      eval_int_op BigInt.sub;
    op_infix "/",      eval_int_op BigInt.computer_div;
    op_infix "%",      eval_int_op BigInt.computer_mod;
  ] in
  let open Mlmpfr_wrapper in
  let float_module tyb ~prec m = builtin1t ["ieee_float"] m ("t", dummy_type) (fun ts -> [
    "zeroF",           (fun _ _ -> Some (value (ty_app ts []) (Vfloat (make_zero ~prec Positive))));
    "add",             eval_float ts tyb Mode2 (fun rnd -> add ~rnd ~prec);
    "sub",             eval_float ts tyb Mode2 (fun rnd -> sub ~rnd ~prec);
    "mul",             eval_float ts tyb Mode2 (fun rnd -> mul ~rnd ~prec);
    "div",             eval_float ts tyb Mode2 (fun rnd -> div ~rnd ~prec);
    "abs",             eval_float ts tyb Mode1 (fun rnd -> abs ~rnd ~prec);
    "neg",             eval_float ts tyb Mode1 (fun rnd -> neg ~rnd ~prec);
    "fma",             eval_float ts tyb Mode3 (fun rnd -> fma ~rnd ~prec);
    "sqrt",            eval_float ts tyb Mode1 (fun rnd -> sqrt ~rnd ~prec);
    "roundToIntegral", eval_float ts tyb Mode1 (fun rnd -> rint ~rnd ~prec);
    (* Intentionnally removed from programs
       "min",          eval_float_minmax min;
       "max",          eval_float_minmax max; *)
    "le",              eval_float ts_bool tyb Mode_rel lessequal_p;
    "lt",              eval_float ts_bool tyb Mode_rel less_p;
    "eq",              eval_float ts_bool tyb Mode_rel equal_p;
    "is_zero",         eval_float ts_bool tyb Mode_rel1 zero_p;
    "is_infinite",     eval_float ts_bool tyb Mode_rel1 inf_p;
    "is_nan",          eval_float ts_bool tyb Mode_rel1 nan_p;
    "is_positive",     eval_float ts_bool tyb Mode_rel1 (fun s -> signbit s = Positive);
    "is_negative",     eval_float ts_bool tyb Mode_rel1 (fun s -> signbit s = Negative);
  ]) in
  [
    builtin ["bool"] "Bool" [
      "True",          (fun _ _ -> Some (value ty_bool (Vbool true)));
      "False",         (fun _ _ -> Some (value ty_bool (Vbool false)));
    ];
    builtin ["int"] "Int" int_ops;
    builtin ["int"] "MinMax" [
      "min",           eval_int_op BigInt.min;
      "max",           eval_int_op BigInt.max
    ];
    builtin ["int"] "ComputerDivision" [
      "div",           eval_int_op BigInt.computer_div;
      "mod",           eval_int_op BigInt.computer_mod
    ];
    builtin ["int"] "EuclideanDivision" [
      "div",           eval_int_op BigInt.euclidean_div;
      "mod",           eval_int_op BigInt.euclidean_mod
    ];
    builtin1t ["ieee_float"] "RoundingMode" ("mode", dummy_type) (fun ts -> [
      "RNE",           (fun _ _ -> Some (value (ty_app ts []) (Vfloat_mode To_Nearest)));
      "RNA",           (fun _ _ -> Some (value (ty_app ts []) (Vfloat_mode Away_From_Zero)));
      "RTP",           (fun _ _ -> Some (value (ty_app ts []) (Vfloat_mode Toward_Plus_Infinity)));
      "RTN",           (fun _ _ -> Some (value (ty_app ts []) (Vfloat_mode Toward_Minus_Infinity)));
      "RTZ",           (fun _ _ -> Some (value (ty_app ts []) (Vfloat_mode Toward_Zero)));
    ]);
    builtin ["real"] "Real" [
      op_infix "=",    eval_real Mode_relr Big_real.eq;
      op_infix "<",    eval_real Mode_relr Big_real.lt;
      op_infix "<=",   eval_real Mode_relr Big_real.le;
      op_prefix "-",   eval_real Mode1r Big_real.neg;
      op_infix "+",    eval_real Mode2r Big_real.add;
      op_infix "*",    eval_real Mode2r Big_real.mul;
      op_infix "/",    eval_real Mode2r Big_real.div
    ];
    builtin ["real"] "Square" [
      "sqrt",          eval_real Mode1r Big_real.sqrt
    ];
    builtin ["real"] "Trigonometry" [
      "pi",            eval_real Modeconst (Big_real.pi ())
    ];
    builtin ["real"] "ExpLog" [
      "exp",           eval_real Mode1r Big_real.exp;
      "log",           eval_real Mode1r Big_real.log;
    ];
    builtin1t ["array"] "Array" ("array", dummy_type) (fun ts -> [
      "make", (fun _ args -> match args with
          | [{v_desc= Vnum n}; def] -> (
              try
                let n = BigInt.to_int n in
                let ty = ty_app ts [def.v_ty] in
                Some (value ty (Varray (Array.make n def)))
              with e -> cannot_compute "array could not be made: %a" Exn_printer.exn_printer e )
          | _ -> assert false);
      "empty", (fun _ args -> match args with
          | [{v_desc= Vconstr(_, _, [])}] ->
              (* we know by typing that the constructor
                  will be the Tuple0 constructor *)
              let ty = ty_app ts [ty_var (tv_of_string "a")] in
              Some (value ty (Varray [||]))
          | _ -> assert false);
      "length", (fun _ args -> match args with
          | [{v_desc= Varray a}] ->
              Some (value ty_int (Vnum (BigInt.of_int (Array.length a))))
          | _ -> assert false) ;
      op_get "", (fun _ args -> match args with
          | [{v_desc= Varray a}; {v_desc= Vnum i}] -> (
              try Some a.(BigInt.to_int i) with e ->
                cannot_compute "array element could not be retrieved: %a" Exn_printer.exn_printer e )
          | _ -> assert false);
      op_set "", (fun _ args -> match args with
          | [{v_desc= Varray a}; {v_desc= Vnum i}; v] -> (
              try
                a.(BigInt.to_int i) <- v;
                Some unit_value
              with e ->
                cannot_compute "array element could not be set: %a" Exn_printer.exn_printer e )
          | _ -> assert false) ;
        ]);
    float_module 32 ~prec:24 "Float32";
    float_module 64 ~prec:53 "Float64";
  ] @ if Debug.test_flag debug_disable_builtin_mach then [] else [
    builtin ["mach"; "int"] "Byte" bounded_int_ops;
    builtin ["mach"; "int"] "Int31" bounded_int_ops;
    builtin ["mach"; "int"] "Int63" bounded_int_ops;
  ]

let add_builtin_mo env (Builtin_module {path; name; types; values}) =
  let open Pmodule in
  let pm = read_module env path name in
  List.iter
    (fun (id, r) ->
      let its =
        try Pmodule.ns_find_its pm.mod_export [id]
        with Not_found -> raise (CannotFind (path, name, id)) in
      r pm.mod_known its)
    types ;
  List.iter
    (fun (id, f) ->
      let ps =
        try Pmodule.ns_find_rs pm.mod_export [id]
        with Not_found -> raise (CannotFind (path, name, id)) in
      Hrs.add builtin_progs ps f)
    (values pm)

let get_builtin_progs env =
  List.iter (add_builtin_mo env) (built_in_modules ())

let get_vs env vs =
  try Mvs.find vs env.vsenv
  with Not_found ->
    ksprintf failwith "program variable %s not found in env"
      vs.vs_name.id_string

let get_pvs env pvs =
  get_vs env pvs.pv_vs

(******************************************************************************)
(*                           TYPE DEFAULTS                                    *)
(******************************************************************************)

let is_array_its env its =
  let pm = Pmodule.read_module env ["array"] "Array" in
  let array_its = Pmodule.ns_find_its pm.Pmodule.mod_export ["array"] in
  its_equal its array_its

(* TODO Remove argument [env] after replacing Varray by model substitution *)
let rec default_value_of_type env known ity : value =
  let ty = ty_of_ity ity in
  match ity.ity_node with
  | Ityvar _ -> failwith "default_value_of_type: type variable"
  | Ityapp (ts, _, _) when its_equal ts its_int -> value ty (Vnum BigInt.zero)
  | Ityapp (ts, _, _) when its_equal ts its_real -> assert false (* TODO *)
  | Ityapp (ts, _, _) when its_equal ts its_bool -> value ty (Vbool false)
  | Ityapp (ts, _, _) when its_equal ts its_str -> value ty (Vstring "")
  | Ityapp (ts,ityl1,_) when is_ts_tuple ts.its_ts ->
      let vs = List.map (default_value_of_type env known) ityl1 in
      constr_value ity (rs_tuple (List.length ityl1)) [] vs
  | Ityapp (its, l1, l2)
  | Ityreg {reg_its= its; reg_args= l1; reg_regs= l2} ->
      if is_array_its env its then
        value ty (Varray (Array.init 0 (fun _ -> assert false)))
      else match Pdecl.find_its_defn known its with
        | {Pdecl.itd_its= {its_def= Range r}} ->
            let zero_in_range = BigInt.(le r.Number.ir_lower zero && le zero r.Number.ir_upper) in
            let n = if zero_in_range then BigInt.zero else r.Number.ir_lower in
            range_value ity n
        | {Pdecl.itd_constructors= rs :: _; itd_fields= fs} ->
            let subst = its_match_regs its l1 l2 in
            let ityl = List.map (fun pv -> pv.pv_ity) rs.rs_cty.cty_args in
            let tyl = List.map (ity_full_inst subst) ityl in
            let vs = List.map (default_value_of_type env known) tyl in
            constr_value ity rs fs vs
        | {Pdecl.itd_constructors= []} ->
            value ty Vundefined

(******************************************************************************)
(*                           ROUTINE DEFINITIONS                              *)
(******************************************************************************)

type routine_defn =
  | Builtin of (rsymbol -> value list -> value option)
  | LocalFunction of (rsymbol * cexp) list * cexp
  | Constructor of Pdecl.its_defn
  | Projection of Pdecl.its_defn

let rec find_def rs = function
  | d :: _ when rs_equal rs d.rec_sym ->
      d.rec_fun (* TODO : put rec_rsym in local env *)
  | _ :: l -> find_def rs l
  | [] -> raise Not_found

let rec find_constr_or_proj dl rs =
  match dl with
  | [] -> raise Not_found
  | d :: rem ->
      if List.mem rs d.Pdecl.itd_constructors then
        Constructor d
      else if List.mem rs d.Pdecl.itd_fields then
        Projection d
      else
        find_constr_or_proj rem rs

let find_global_definition kn rs =
  match (Mid.find rs.rs_name kn).Pdecl.pd_node with
  | Pdecl.PDtype dl -> find_constr_or_proj dl rs
  | Pdecl.PDlet (LDvar _) -> raise Not_found
  | Pdecl.PDlet (LDsym (_, ce)) -> LocalFunction ([], ce)
  | Pdecl.PDlet (LDrec dl) ->
      let locs = List.map (fun d -> d.rec_rsym, d.rec_fun) dl in
      LocalFunction (locs, find_def rs dl)
  | Pdecl.PDexn _ -> raise Not_found
  | Pdecl.PDpure -> raise Not_found

let find_definition env (rs: rsymbol) =
  (* then try if it is a built-in symbol *)
  try Builtin (Hrs.find builtin_progs rs) with Not_found ->
  (* then try if it is a local function *)
  try LocalFunction ([], Mrs.find rs env.funenv) with Not_found ->
  (* else look for a global function *)
  find_global_definition env.pmodule.Pmodule.mod_known rs

(******************************************************************************)
(*                            VALUES TO TERMS                                 *)
(******************************************************************************)

(** Convert a value into a term. The first component of the result are additional bindings
   from closures. *)
let rec term_of_value ?(ty_mt=Mtv.empty) env vsenv v : (vsymbol * term) list * term =
  let v_ty = ty_inst ty_mt v.v_ty in
  match v.v_desc with
  | Vundefined ->
      vsenv, t_undefined v_ty
  | Vnum i ->
      if ty_equal v_ty ty_int || is_range_ty v_ty then
        vsenv, t_const (Constant.int_const i) v_ty
      else
        kasprintf failwith "term_of_value: value type not int or range but %a"
          print_ty v_ty
  | Vstring s ->
      ty_equal_check v_ty ty_str;
      vsenv, t_const (Constant.ConstStr s) ty_str
  | Vbool b ->
      ty_equal_check v_ty ty_bool;
      vsenv, if b then t_bool_true else t_bool_false
  | Vterm t ->
      Opt.iter (ty_equal_check v_ty) t.t_ty;
      vsenv, t
  | Vreal _ | Vfloat _ | Vfloat_mode _ -> (* TODO *)
      Format.kasprintf failwith "term_of_value: %a" print_value v
  | Vproj (ls, x) ->
      (* TERM: epsilon v. rs v = x *)
      let vs = create_vsymbol (id_fresh "v") v_ty in
      let vsenv, t_x = term_of_value ~ty_mt env vsenv x in
      let ty_x = ty_inst ty_mt x.v_ty in
      let t = t_equ (fs_app ls [t_var vs] ty_x) t_x in
      vsenv, t_eps (t_close_bound vs t)
  | Vconstr (rs, field_rss, fs) -> (
      let term_of_field vsenv f = term_of_value ~ty_mt env vsenv (field_get f) in
      let vsenv, fs = Lists.map_fold_left term_of_field vsenv fs in
      match rs_kind rs with
      | RKfunc -> vsenv, fs_app (ls_of_rs rs) fs v_ty
      | RKnone when Strings.has_suffix "'mk" rs.rs_name.id_string ->
          let vs = create_vsymbol (id_fresh "v") v_ty in
          let for_field rs = t_equ (t_app_infer (ls_of_rs rs) [t_var vs]) in
          let t = t_and_l (List.map2 for_field field_rss fs) in
          vsenv, t_eps (t_close_bound vs t)
      | _ -> kasprintf failwith "Cannot construct term for constructor \
                                 %a that is not a function" print_rs rs )
  | Vfun (cl, arg, e) ->
      (* TERM: fun arg -> t *)
      let t = Opt.get_exn (Failure "Cannot convert function body to term")
          (term_of_expr ~prop:false e) in
      (* Rebind values from closure *)
      let bind_cl vs v (mt, mv, vsenv) =
        let vs' = create_vsymbol (id_clone vs.vs_name) v.v_ty in
        let mt = ty_match mt vs.vs_ty v.v_ty in
        let mv = Mvs.add vs (t_var vs') mv in
        let vsenv, t = term_of_value ~ty_mt env vsenv v in
        let vsenv = (vs', t) :: vsenv in
        mt, mv, vsenv in
      let mt, mv, vsenv = Mvs.fold bind_cl cl (Mtv.empty, Mvs.empty, vsenv) in
      (* Substitute argument type *)
      let ty_arg = ty_app_arg ts_func 0 v_ty in
      let vs_arg = create_vsymbol (id_clone arg.vs_name) ty_arg in
      let mv = Mvs.add arg (t_var vs_arg) mv in
      let mt = ty_match mt arg.vs_ty ty_arg in
      let t = t_ty_subst mt mv t in
      vsenv, t_lambda [vs_arg] [] t
  | Varray arr ->
      let open Pmodule in
      let {mod_theory= {Theory.th_export= ns}} =
        read_module env.env ["array"] "Array" in
      let ts_array = Theory.ns_find_ts ns ["array"] in
      if Debug.test_flag debug_array_as_update_chains_not_epsilon then
        (* TERM: (make <length arr> undefined)[<i> <- <arr[i]>] *)
        let ls_make = Theory.ns_find_ls ns ["make"] in
        let ls_update = Theory.ns_find_ls ns [Ident.op_update ""] in
        let t_length = t_nat_const (Array.length arr) in
        let ty_elt = ty_app_arg ts_array 0 v_ty in
        let t0 = fs_app ls_make [t_length; t_undefined ty_elt] v_ty in
        let rec loop vsenv sofar ix =
          if ix = Array.length arr then vsenv, sofar
          else
            let t_ix = t_nat_const ix in
            let vsenv, t_v = term_of_value ~ty_mt env vsenv arr.(ix) in
            let sofar = fs_app ls_update [sofar; t_ix; t_v] v_ty in
            loop vsenv sofar (succ ix) in
        loop vsenv t0 0
      else
        (* TERM: epsilon v. v.length = length arr /\ v[0] = arr.(ix) /\ ... *)
        let ls_length = Theory.ns_find_ls ns ["length"] in
        let ls_get = Theory.ns_find_ls ns [op_get ""] in
        let v = create_vsymbol (id_fresh "a") v_ty in
        let t_eq_length = (* v.length = length arr *)
          t_equ (fs_app ls_length [t_var v] ty_int)
            (t_nat_const (Array.length arr)) in
        let elt_ty = ty_app_arg ts_array 0 v_ty in
        let rec loop vsenv sofar ix = (* v[ix] = arr.(ix) *)
          if ix = Array.length arr then vsenv, List.rev sofar else
            let vsenv, t_a_ix = term_of_value ~ty_mt env vsenv arr.(ix) in
            let t_eq_ix =
              t_equ (fs_app ls_get [t_var v; t_nat_const ix] elt_ty) t_a_ix in
            loop vsenv (t_eq_ix :: sofar) (succ ix) in
        let vsenv, t_eq_ixs = loop vsenv [] 0 in
        let t = t_and_l (t_eq_length :: t_eq_ixs) in
        vsenv, t_eps (t_close_bound v t)
  | Vpurefun (ty, m, def) ->
      (* TERM: fun x -> if x = k0 then v0 else ... else def *)
      let vs_arg = create_vsymbol (id_fresh "x") ty in
      let mk_case key value (vsenv, t) =
        let vsenv, key = term_of_value ~ty_mt env vsenv key in      (* k_i *)
        let vsenv, value = term_of_value ~ty_mt env vsenv value in  (* v_i *)
        let t = t_if (t_equ (t_var vs_arg) key) value t in (* if arg = k_i then v_i else ... *)
        vsenv, t in
      let vsenv, t = Mv.fold mk_case m (term_of_value ~ty_mt env vsenv def) in
      vsenv, t_lambda [vs_arg] [] t

let add_premises ?post_res ?(vsenv=[]) ts env =
  let match_free_var env vs _ (vsenv, mt, mv) =
    let v = get_vs env vs in
    let vsenv, t = term_of_value env vsenv v in
    let vs' = create_vsymbol (id_clone vs.vs_name) (v_ty v) in
    let mt = ty_match mt vs.vs_ty (v_ty v) in
    let mv = Mvs.add vs (vs', t) mv in
    vsenv, mt, mv in
  let bind_vs (vs, t1) t2 =
    t_let_close vs t1 t2 in
  let bind_fun env mt mv vs _ sofar =
    let matching_vs rs _ = id_equal rs.rs_name vs.vs_name in
    match Mrs.choose (Mrs.filter matching_vs env.funenv) with
    | rs, { c_node= Cfun e } ->
        let t = Opt.get (term_of_expr ~prop:false e) in
        let t = t_ty_subst mt mv t in
        let vs_args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
        t_let_close vs (t_lambda vs_args [] t) sofar
    | _ -> cannot_compute "anonymous function not cfun"
    | exception Not_found ->
        kasprintf failwith "add_premises: function %a not found" print_vs vs in
  let close_term t =
    let mt, mv = Mtv.empty, Mvs.empty in
    let free = t_freevars Mvs.empty t in
    let free_vars, free_funs =
      Mvs.partition (fun vs _ -> Mvs.mem vs env.vsenv) free in
    let t, mt, mv =
      match post_res with
      | Some t_res ->
          let vs, t = open_post t in
          let mt = ty_match mt vs.vs_ty (t_type t_res) in
          let vs' = create_vsymbol (id_clone vs.vs_name) (t_type t_res) in
          let mv = Mvs.add vs (vs', t_res) mv in
          t, mt, mv
      | None -> t, mt, mv in
    let vsenv, mt, mv =
      Mvs.fold (match_free_var env) free_vars (vsenv, mt, mv) in
    (* mv : old (polymorphic) vsymbol -> new (monomorphic) vsymbol * value term *)
    let mv_vs = Mvs.map fst mv in
    let mv_t = Mvs.map (fun (vs', _) -> t_var vs') mv in
    let vsenv = List.map (fun (vs, t) -> Mvs.find_def vs vs mv_vs, t_ty_subst mt mv_t t) vsenv in
    let t = t_ty_subst mt mv_t t in
    let t = Mvs.fold (fun _ -> bind_vs) mv t in
    let t = List.fold_left (fun t vs_t -> bind_vs vs_t t) t vsenv in
    let t = Mvs.fold (bind_fun env mt mv_t) free_funs t in
    t in
  add_premises (List.map close_term ts) env.premises

let add_post_premises cty res env =
  let post_res = match res with
    | Normal v -> Some (cty.cty_post, v)
    | Excep (xs, v) -> Some (Mxs.find xs cty.cty_xpost, v)
    | Irred _ -> None in
  Opt.iter (fun (post, res) ->
      let vsenv, t = term_of_value env [] res in
      add_premises ~post_res:t ~vsenv post env) post_res

(******************************************************************************)
(*                           CONTRADICTION CONTEXT                            *)
(******************************************************************************)

type cntr_ctx = {
  c_attr   : attribute; (* From module [Vc] *)
  c_desc   : string option;
  c_loc    : Loc.position option;
  c_vsenv  : value Mvs.t;
  c_log_uc : Log.log_uc;
}

type pre_cntr_ctx = env -> cntr_ctx

exception Contr of cntr_ctx * term

let describe_cntr_ctx ctx =
  asprintf "%s%a"
    (Strings.remove_prefix "expl:" ctx.c_attr.attr_string)
    (Pp.print_option (fun fmt -> fprintf fmt " %s")) ctx.c_desc

let report_cntr_title fmt (ctx, msg) =
  fprintf fmt "%s %s" (String.capitalize_ascii (describe_cntr_ctx ctx)) msg

let report_cntr_head fmt (ctx, msg, term) =
  fprintf fmt "@[<v>%a%t@]" report_cntr_title (ctx, msg)
    (fun fmt ->
       match ctx.c_loc, term.t_loc with
       | Some t1, Some t2 ->
           fprintf fmt " at %a@,- Defined at %a" print_loc' t1 print_loc' t2
       | Some t, None | None, Some t ->
           fprintf fmt " at %a" print_loc' t
       | None, None -> () )

let env_sep = Pp.comma

let pp_env pp_key pp_value fmt =
  let delims = Pp.nothing, Pp.nothing in
  fprintf fmt "%a" (pp_bindings ~delims ~sep:env_sep pp_key pp_value)

let report_cntr_body fmt (ctx, term) =
  let cmp_vs (vs1, _) (vs2, _) =
    String.compare vs1.vs_name.id_string vs2.vs_name.id_string in
  let mvs = t_freevars Mvs.empty term in
  fprintf fmt "@[<hv2>- Term: %a@]@," print_term term ;
  fprintf fmt "@[<hv2>- Variables: %a@]" (pp_env print_vs print_value)
    (List.sort cmp_vs
       (Mvs.bindings
          (Mvs.filter (fun vs _ -> Mvs.contains mvs vs) ctx.c_vsenv)))

let report_cntr fmt (ctx, msg, term) =
  fprintf fmt "@[<v>%a@,%a@]"
    report_cntr_head (ctx, msg, term)
    report_cntr_body (ctx, term)

let cntr_ctx ?loc attr ?desc () : pre_cntr_ctx =
  fun env -> {
      c_attr= attr;
      c_desc= desc;
      c_loc= loc;
      c_vsenv= snapshot_vsenv env.vsenv;
      c_log_uc= env.rac.log_uc;
    }

(******************************************************************************)
(*                                TERM TO TASK                                *)
(******************************************************************************)

(* Add declarations for additional term bindings in [vsenv] *)
let bind_term (vs, t) (task, ls_mt, ls_mv) =
  let ty = Opt.get t.t_ty in
  let ls = create_fsymbol (id_clone vs.vs_name) [] ty in
  let ls_mt = ty_match ls_mt vs.vs_ty ty in
  let ls_mv = Mvs.add vs (fs_app ls [] ty) ls_mv in
  let t = t_ty_subst ls_mt ls_mv t in
  let defn = Decl.make_ls_defn ls [] t in
  let task = Task.add_logic_decl task [defn] in
  task, ls_mt, ls_mv

(* Add declarations for value bindings in [env.vsenv] *)
let bind_value env vs v (task, ls_mt, ls_mv) =
  let ty, ty_mt, ls_mt =
    (* [ty_mt] is a type substitution for [v],
       [ls_mt] is a type substitution for the remaining task *)
    if ty_closed v.v_ty then
      v.v_ty, Mtv.empty, ty_match ls_mt vs.vs_ty v.v_ty
    else
      vs.vs_ty, ty_match Mtv.empty v.v_ty vs.vs_ty, ls_mt in
  let ls = create_fsymbol (id_clone vs.vs_name) [] ty in
  let ls_mv = Mvs.add vs (fs_app ls [] ty) ls_mv in
  let vsenv, t = term_of_value ~ty_mt env [] v in
  let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
  let t = t_ty_subst ls_mt ls_mv t in
  let defn = Decl.make_ls_defn ls [] t in
  let task = Task.add_logic_decl task [defn] in
  task, ls_mt, ls_mv

(* Create and open a formula `p t` where `p` refers to a predicate without definition, to
   use the reduction engine to evaluate `t` *)
let undef_pred_decl, undef_pred_app, undef_pred_app_arg =
  let ls = let tv = create_tvsymbol (id_fresh "a") in
    create_psymbol (id_fresh "p") [ty_var tv] in
  let decl = Decl.create_param_decl ls in
  let app t = t_app ls [t] None in
  let app_arg t = match t with
    | {t_node= Tapp (ls, [t])} when ls_equal ls ls -> t
    | _ -> failwith "open_app" in
  decl, app, app_arg

(* Add declarations from local functions in [env.funenv] *)
let bind_fun rs cexp (task, ls_mv) =
  try
    let t = match cexp.c_node with
      | Cfun e -> Opt.get_exn Exit (term_of_expr ~prop:false e)
      | _ -> raise Exit in
    let ty_args = List.map (fun pv -> ty_of_ity pv.pv_ity) rs.rs_cty.cty_args in
    let ty_res = ty_of_ity rs.rs_cty.cty_result in
    let ls, ls_mv = match rs.rs_logic with
      | RLlemma | RLnone -> raise Exit
      | RLls ls -> ls, ls_mv
      | RLpv {pv_vs= vs} ->
          let ls = create_fsymbol (id_clone rs.rs_name) ty_args ty_res in
          let vss = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
          let ts = List.map t_var vss in
          let t0 = fs_app ls ts ty_res in
          let t = t_lambda vss [] t0 in
          let ls_mv = Mvs.add vs t ls_mv in
          ls, ls_mv in
    let vs_args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
    let decl = Decl.make_ls_defn ls vs_args t in
    let task = Task.add_logic_decl task [decl] in
    task, ls_mv
  with Exit -> task, ls_mv

let task_of_term ?(vsenv=[]) env t =
  let open Task in let open Decl in
  let th = env.pmodule.Pmodule.mod_theory in
  let lsenv =
    let aux1 rs v mls =
      match rs.rs_logic with
      | RLls ls -> Mls.add ls v mls
      | _ -> mls in
    Mrs.fold aux1 env.rsenv Mls.empty in
  let add_used task td =
    let open Theory in
    match td.td_node with
    | Use th ->
        Task.use_export task th
    | Clone (th, sm) ->
        let inst_df = Decl.Paxiom in
        let inst_pr = Decl.Mpr.map (fun _ -> Decl.Paxiom) sm.sm_pr in
        let inst =
          {inst_df; inst_pr; inst_ty= sm.sm_ty; inst_ts= sm.sm_ts; inst_ls= sm.sm_ls } in
        Task.clone_export task th inst
    | _ -> task in
  let add_known _ decl (task, ls_mt, ls_mv) =
    match decl.d_node with
    | Dparam ls when Mls.contains lsenv ls ->
        (* Take value from lsenv (i.e. env.rsenv) for declaration *)
        let vsenv, t = term_of_value env [] (Mls.find ls lsenv) in
        let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
        let t = t_ty_subst ls_mt ls_mv t in
        let ldecl = Decl.make_ls_defn ls [] t in
        let decl = create_logic_decl [ldecl] in
        let task = add_decl task decl in
        task, ls_mt, ls_mv
    | Dprop (Plemma, prs, t) ->
        add_decl task (create_prop_decl Paxiom prs t), ls_mt, ls_mv
    | Dprop (Pgoal, _, _) -> task, ls_mt, ls_mv
    | _ -> add_decl task decl, ls_mt, ls_mv in
  let add_prog_const rs v (task, ls_mt, ls_mv) =
    let is_undefined_constant ls =
      let th_known = env.pmodule.Pmodule.mod_theory.Theory.th_known in
      match Mid.find ls.ls_name th_known with
      | Decl.{d_node = Dparam _} -> true
      | _ -> false in
    match rs.rs_logic with
    | Expr.RLls ls when is_undefined_constant ls ->
        let pr = create_prsymbol (id_fresh (asprintf "def_%a" print_rs rs)) in
        let vsenv, t = term_of_value env [] v in
        let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
        let t = t_equ (t_app ls [] ls.ls_value) t in
        let task = add_prop_decl task Paxiom pr t in
        task, ls_mt, ls_mv
    | _ -> task, ls_mt, ls_mv in
  let add_premise task t =
    let pr = create_prsymbol (id_fresh "premise") in
    Task.add_prop_decl task Decl.Paxiom pr t in
  let task, ls_mt, ls_mv = None, Mtv.empty, Mvs.empty in
  let task = List.fold_left add_used task th.Theory.th_decls in
  let used = Task.used_symbols (Task.used_theories task) in
  let known_local = Mid.filter (fun id _ -> not (Mid.mem id used)) th.Theory.th_known in
  let task, ls_mt, ls_mv = Mid.fold add_known known_local (task, ls_mt, ls_mv) in
  let task, ls_mt, ls_mv = Mrs.fold add_prog_const env.rsenv (task, ls_mt, ls_mv) in
  let task, ls_mv = Mrs.fold bind_fun env.funenv (task, ls_mv) in
  let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
  let task, ls_mt, ls_mv = Mvs.fold (bind_value env) env.vsenv (task, ls_mt, ls_mv) in
  let task = fold_premises add_premise env.premises task in
  let t = t_ty_subst ls_mt ls_mv t in
  let task =
    if t.t_ty = None then (* Add a formula as goal directly ... *)
      let prs = create_prsymbol (id_fresh "goal") in
      add_prop_decl task Pgoal prs t
    else (* ... and wrap a non-formula in a call to a predicate with no definition *)
      let task = add_decl task undef_pred_decl in
      let prs = create_prsymbol (id_fresh "goal") in
      add_prop_decl task Pgoal prs (undef_pred_app t) in
  task, ls_mv

(******************************************************************************)
(*                                CHECK TERM                                  *)
(******************************************************************************)

(* Parameters for binding universally quantified variables to a value
   obtained with rac_config.get_value or the default value *)
let bind_univ_quant_vars = false
let bind_univ_quant_vars_default = false

(* Get the value of a vsymbol with env.rac.get_value or a default value *)
let get_value_for_quant_var env vs =
  match vs.vs_name.id_loc with
  | None -> None
  | Some loc ->
      let value =
        if bind_univ_quant_vars then
          let v = env.rac.get_value ~loc vs.vs_name (ity_of_ty vs.vs_ty) in
          (Opt.iter (fun v ->
               Debug.dprintf debug_rac_values
                 "Bind all-quantified variable %a to %a@."
                 print_vs vs print_value v) v; v)
        else None in
      let value =
        if value <> None then value else
          if bind_univ_quant_vars_default then (
            let v = default_value_of_type env.env env.pmodule.Pmodule.mod_known (ity_of_ty vs.vs_ty) in
            Debug.dprintf debug_rac_values
              "Use default value for all-quantified variable %a: %a@."
              print_vs vs print_value v;
            Some v
          ) else None in
      Opt.iter (fun v ->
          register_used_value env (Some loc) vs.vs_name v) value;
      value

(** When the task goal is [forall vs* . t], add declarations to the
   task that bind the variables [vs*] to concrete values (with
   env.rac.get_value or default values), and make [t] the new goal. *)
let bind_univ_quant_vars env task =
  try match (Task.task_goal_fmla task).t_node with
    | Tquant (Tforall, tq) ->
        let vs, _, t = t_open_quant tq in
        let values = List.map (fun vs -> Opt.get_exn Exit (get_value_for_quant_var env vs)) vs in
        let _, task = Task.task_separate_goal task in
        let task, ls_mt, ls_mv = List.fold_right2 (bind_value env) vs values (task, Mtv.empty, Mvs.empty) in
        let prs = Decl.create_prsymbol (id_fresh "goal") in
        let t = t_ty_subst ls_mt ls_mv t in
        Task.add_prop_decl task Decl.Pgoal prs t
    | _ -> raise Exit
  with Exit -> task

let task_hd_equal t1 t2 = let open Task in let open Theory in let open Decl in
  (* Task.task_hd_equal is too strict: it requires physical equality between
     {t1,t2}.task_prev *)
  match t1.task_decl.td_node, t2.task_decl.td_node with
  | Decl {d_node = Dprop (Pgoal,p1,g1)}, Decl {d_node = Dprop (Pgoal,p2,g2)} ->
      pr_equal p1 p2 && t_equal_strict g1 g2
  | _ -> t1 == t2

(** Apply the (reduction) transformation and fill universally quantified variables
    in the head of the task by values obtained with env.rac.get_value, recursively. *)
let rec trans_and_bind_quants env trans task =
  let task = bind_univ_quant_vars env task in
  let tasks = Trans.apply trans task in
  let task_unchanged = match tasks with
    | [task'] -> Opt.equal task_hd_equal task' task
    | _ -> false in
  if task_unchanged then
    tasks
  else
    List.flatten (List.map (trans_and_bind_quants env trans) tasks)

(** Compute the value of a term by using the (reduction) transformation *)
let compute_term ?vsenv env t =
  match env.rac.rac_reduce.rac_trans with
  | None -> t
  | Some trans ->
      let task, ls_mv = task_of_term ?vsenv env t in
      if t.t_ty = None then (* [t] is a formula *)
        let tasks = trans_and_bind_quants env trans task in
        match List.map Task.task_goal_fmla tasks with
        | [] -> t_true
        | t :: ts -> List.fold_left t_and t ts
      else (* [t] is not a formula *)
        let t = match Trans.apply trans task with
          | [task] -> undef_pred_app_arg (Task.task_goal_fmla task)
          | _ -> failwith "compute_term" in
        (* Free vsymbols in the original [t] have been substituted in by fresh
           lsymbols (actually: ls @ []) to bind them to declarations in the
           task. Now we have to reverse these substitution to ensures that the
           reduced term is valid in the original environment of [t]. *)
        let reverse vs t' t =
          if t_occurs t' t then t_replace t' (t_var vs) t else t in
        Mvs.fold reverse ls_mv t

(** Check the validiy of a term that has been encoded in a task by the (reduction) transformation *)
let check_term_compute env trans task =
  let is_false = function
    | Some {Task.task_decl= Theory.{
        td_node= Decl Decl.{
            d_node= Dprop (Pgoal, _, {t_node= Tfalse})}}} ->
        true
    | _ -> false in
  match trans_and_bind_quants env trans task with
  | [] -> Some true
  | tasks ->
      Debug.dprintf debug_rac_check_sat "Transformation produced %d tasks@." (List.length tasks);
      if List.exists is_false tasks then
        Some false
      else (
        List.iter (Debug.dprintf debug_rac_check_sat "- %a@." print_tdecl)
          (Lists.map_filter (Opt.map (fun t -> t.Task.task_decl)) tasks);
        None )

(** Check the validiy of a term that has been encoded in a task by dispatching it to a prover *)
let check_term_dispatch (Rac_prover {command; driver; limit}) task =
  let open Call_provers in
  let call = Driver.prove_task ~command ~limit driver task in
  let res = wait_on_call call in
  Debug.dprintf debug_rac_check_sat "@[<h>Check term dispatch answer: %a@]@."
    print_prover_answer res.pr_answer;
  match res.pr_answer with
  | Valid -> Some true
  | Invalid -> Some false
  | _ -> None

let negate_goal task =
  let open Task in
  let tdecl, task = task_separate_goal task in
  match tdecl.Theory.td_node with
  | Theory.Decl Decl.{d_node= Dprop (Pgoal,p,t)} ->
      add_prop_decl task Decl.Pgoal p (t_not t)
  | _ -> failwith "negate_goal"

let check_term_dispatch ~try_negate rp task =
  match check_term_dispatch rp task with
  | None when try_negate ->
      Debug.dprintf debug_rac_check_sat "Try negation.@.";
      let task = negate_goal task in
      let res = check_term_dispatch rp task in
      Opt.map (fun b -> not b) res
  | r -> r

(* The callee must ensure that RAC is enabled. *)
let check_term ?vsenv env (ctx: pre_cntr_ctx) t =
  let ctx = ctx env in
  if not env.rac.do_rac then failwith "check_term with RAC disabled";
  Debug.dprintf debug_rac_check_sat "@[<hv2>Check term: %a %a@]@." print_term t
    Pp.(print_list space (fun fmt vs -> fprintf fmt "@[%a=%a@]" print_vs vs print_value (get_vs env vs)))
    (Mvs.keys (t_freevars Mvs.empty t)) ;
  let task, _ = task_of_term ?vsenv env t in
  let res = (* Try checking the term using computation first ... *)
    Opt.map (fun b -> Debug.dprintf debug_rac_check_sat "Computed %b.@." b; b)
      (Opt.bind env.rac.rac_reduce.rac_trans
         (fun trans -> check_term_compute env trans task)) in
  let res =
    if res = None then (* ... then try solving using a prover *)
      let try_negate = env.rac.rac_reduce.rac_try_negate in
      Opt.map (fun b -> Debug.dprintf debug_rac_check_sat "Dispatched: %b.@." b; b)
        (Opt.bind env.rac.rac_reduce.rac_prover
           (fun rp -> check_term_dispatch ~try_negate rp task))
    else res in
  match res with
  | Some true ->
      Debug.dprintf debug_rac_check_term_result "%a@."
        report_cntr_head (ctx, "is ok", t)
  | Some false ->
      Debug.dprintf debug_rac_check_term_result "%a@."
        report_cntr_head (ctx, "has failed", t);
      raise (Contr (ctx, t))
  | None ->
      let msg = "cannot be evaluated" in
      Debug.dprintf debug_rac_check_term_result "%a@."
        report_cntr_head (ctx, msg, t);
      if env.rac.skip_cannot_compute then
        Warning.emit "%a@." report_cntr_head (ctx, msg, t)
      else
        cannot_compute "%a" report_cntr_title (ctx, msg)

let check_terms env ctx = List.iter (check_term env ctx)

(* Check a post-condition [t] by binding the result variable to
   the term [vt] representing the result value.

   TODO Use Expr.term_of_post? *)
let check_post env ctx v post =
  let vs, t = open_post post in
  let env = {env with vsenv= Mvs.add vs v env.vsenv} in
  check_term env ctx t

let check_posts env attr ?desc loc v posts =
  let ctx = cntr_ctx attr ?desc ?loc () in
  List.iter (check_post env ctx v) posts

let check_type_invs ?loc env ity v =
  let ts = match ity.ity_node with
  | Ityapp (ts, _, _) | Ityreg {reg_its= ts} -> ts
  | Ityvar _ -> failwith "check_type_invs: type variable" in
  let def = Pdecl.find_its_defn env.pmodule.Pmodule.mod_known ts in
  if def.Pdecl.itd_invariant <> [] then
    let fs_vs = match v.v_desc with
      | Vconstr (_, fs, vs) ->
          List.fold_right2 Mrs.add fs (List.map field_get vs) Mrs.empty
      | _ -> failwith "check_type_invs: value is not record" in
    let bind_field env rs =
      bind_pvs (Opt.get rs.rs_field) (Mrs.find rs fs_vs) env in
    let env = List.fold_left bind_field env def.Pdecl.itd_fields in
    let ctx = cntr_ctx Vc.expl_type_inv ?loc:loc () in
    check_terms env ctx def.Pdecl.itd_invariant

exception RACStuck of env * Loc.position option
(* The execution goes into RACStuck when a property that should be
   assumed is not satisfied. E.g. when executing a function, if the
   environment does not satisfy the precondition, the execution ends
   with RACStuck. *)

let value_of_free_vars env ctx t =
  let get_value get_value get_ty env x =
    let def = undefined_value (ity_of_ty (get_ty x)) in
    snapshot (Opt.get_def def (get_value x env))  in
  let mid = t_v_fold (fun mvs vs ->
    let get_ty vs = vs.vs_ty in
    let value = get_value Mvs.find_opt get_ty ctx.c_vsenv vs in
    Mid.add vs.vs_name value mvs) Mid.empty t in
  t_app_fold (fun mrs ls tyl ty ->
      let get_ty rs = ty_of_ity rs.rs_cty.cty_result in
      if tyl = [] && ty <> None then
        try let rs = restore_rs ls in
            let value = get_value Mrs.find_opt get_ty env.rsenv rs in
            Mid.add rs.rs_name value mrs
        with Not_found -> mrs
      else mrs
    ) mid t

let check_assume_term env ctx t =
  try check_term env ctx t with Contr (ctx,t) ->
    let mid = value_of_free_vars env ctx t in
    register_stucked env t.t_loc (describe_cntr_ctx ctx) mid;
    raise (RACStuck (env, t.t_loc))

let check_assume_terms env ctx tl =
  try check_terms env ctx tl with Contr (ctx,t) ->
    let mid = value_of_free_vars env ctx t in
    register_stucked env t.t_loc (describe_cntr_ctx ctx) mid;
    raise (RACStuck (env, t.t_loc))

let check_assume_posts env ctx v posts =
  let ctx = ctx env in
  try check_posts env ctx.c_attr ?desc:ctx.c_desc ctx.c_loc v posts
  with Contr (ctx,t) ->
    let mid = value_of_free_vars env ctx t in
    register_stucked env t.t_loc (describe_cntr_ctx ctx) mid;
    raise (RACStuck (env,t.t_loc))

let check_term ?vsenv env ctx t =
  try check_term ?vsenv env ctx t with (Contr (ctx,t)) as e ->
    let mid = value_of_free_vars env ctx t in
    register_failure env t.t_loc (describe_cntr_ctx ctx) mid;
    raise e

let check_terms env ctx tl =
  try check_terms env ctx tl with (Contr (ctx,t)) as e ->
    let mid = value_of_free_vars env ctx t in
    register_failure env t.t_loc (describe_cntr_ctx ctx) mid;
    raise e

let check_posts env attr ?desc loc v posts =
  try check_posts env attr ?desc loc v posts with (Contr (ctx,t)) as e ->
    let mid = value_of_free_vars env ctx t in
    register_failure env t.t_loc (describe_cntr_ctx ctx) mid;
    raise e

let check_assume_type_invs ?loc env ity v =
  try check_type_invs ?loc env ity v with Contr (ctx, t) ->
    let mid = value_of_free_vars env ctx t in
    register_stucked env t.t_loc (describe_cntr_ctx ctx) mid;
    raise (RACStuck (env, t.t_loc))

(* Currently, type invariants are only check when creating values or getting
   values from the model. TODO Check type invariants also during execution *)
let check_type_invs ?loc env ity v =
  try check_type_invs ?loc env ity v with Contr (ctx, t) as e ->
    let mid = value_of_free_vars env ctx t in
    register_failure env t.t_loc (describe_cntr_ctx ctx) mid;
    raise e

(** [oldify_variant env var] returns a pair [old_ts, oldies] where [old_ts] are
    the variant terms where all free variables have been replaced by fresh
    variables, and [oldies] is a mapping from the fresh variables in [old_ts] to
    snapshots of the current values of the original variables in [env]. *)
let oldify_variant env var =
  let ts = List.map fst var in
  let free_vs = Mvs.keys (List.fold_left t_freevars Mvs.empty ts) in
  let aux vs (subst, oldies) =
    let vs' = create_vsymbol (id_clone vs.vs_name) vs.vs_ty in
    let v = snapshot (Mvs.find vs env.vsenv) in
    Mvs.add vs (t_var vs') subst, Mvs.add vs' v oldies in
  let subst, oldies =
    List.fold_right aux free_vs (Mvs.empty, Mvs.empty) in
  let old_ts = List.map (t_subst subst) ts in
  old_ts, oldies

(** [mk_variant_term env loc old_ts var] creates a term that represents the
    validity of variant [var] of a loop at location [loc], where [old_ts] are
    the oldified variant terms.

    TODO use Vc.decrease? *)
let mk_variant_term env loc attr old_ts var =
  let {Pmodule.mod_theory= {Theory.th_crcmap= crc}} = env.pmodule in
  let {Pmodule.mod_theory= {Theory.th_export= ns}} =
    Pmodule.read_module env.env ["int"] "Int" in
  let ls_int_le = Theory.ns_find_ls ns [Ident.op_infix "<="] in
  let ls_int_lt = Theory.ns_find_ls ns [Ident.op_infix "<"] in
  let rec loop old_ts var =
    match old_ts, var with
    | [], [] -> t_false
    | old_t :: old_ts, (t, opt_op) :: var ->
        let t_here =
          match opt_op with
          | Some op -> ps_app op [t; old_t]
          | None ->
              if ty_equal (t_type t) ty_int then
                t_and (ps_app ls_int_le [t_nat_const 0; old_t])
                  (ps_app ls_int_lt [t; old_t])
              else
                let crc = try ignore (Coercion.find crc (t_type t) ty_int); true
                  with Not_found -> false in
                if crc then failwith "coercions not supported in variants"
                else cannot_compute "loop variant implemented only for int" in
        t_attr_set ?loc:t.t_loc Sattr.empty
          (t_or t_here (t_and (t_equ old_t t) (loop old_ts var)))
    | _ -> assert false in
  let loc = match var with
    | (var_t, _) :: _  when var_t.t_loc <> None -> var_t.t_loc
    | _ -> loc in
  let rec relocate g =
    t_attr_set ?loc g.t_attrs (TermTF.t_map (fun t -> t) relocate g) in
  t_attr_set ?loc (Sattr.singleton attr)
    (relocate (loop old_ts var))

(******************************************************************************)
(*                           EXPRESSION EVALUATION                            *)
(******************************************************************************)

(* Assuming the real is given in pow2 and pow5 *)
let compute_fraction {Number.rv_sig= i; Number.rv_pow2= p2; Number.rv_pow5= p5}
  =
  let p2_val = BigInt.pow_int_pos_bigint 2 (BigInt.abs p2) in
  let p5_val = BigInt.pow_int_pos_bigint 5 (BigInt.abs p5) in
  let num = ref BigInt.one in
  let den = ref BigInt.one in
  num := BigInt.mul i !num ;
  if BigInt.ge p2 BigInt.zero then
    num := BigInt.mul p2_val !num
  else
    den := BigInt.mul p2_val !den ;
  if BigInt.ge p5 BigInt.zero then
    num := BigInt.mul p5_val !num
  else
    den := BigInt.mul p5_val !den ;
  !num, !den

let rec matching env (v : value) p =
  match p.pat_node with
  | Pwild -> env
  | Pvar vs -> bind_vs vs v env
  | Por (p1, p2) -> (
      try matching env v p1 with NoMatch -> matching env v p2 )
  | Pas (p, vs) -> matching (bind_vs vs v env) v p
  | Papp (ls, pl) -> (
      match v.v_desc with
      | Vconstr ({rs_logic= RLls ls2}, _, tl) ->
          if ls_equal ls ls2 then
            List.fold_left2 matching env (List.map field_get tl) pl
          else if ls2.ls_constr > 0 then
            raise NoMatch
          else
            raise Undetermined
      | Vbool b ->
          let ls2 = if b then fs_bool_true else fs_bool_false in
          if ls_equal ls ls2 then env else raise NoMatch
      | _ -> raise Undetermined )

(* Many ways to say yes... *)
let is_true v = match v.v_desc with
  | Vbool true | Vterm {t_node= Ttrue} -> true
  | Vterm t when t_equal t t_bool_true -> true
  | Vconstr (rs, [], []) when rs_equal rs rs_true -> true
  | _ -> false

(* ...and no *)
let is_false v = match v.v_desc with
  | Vbool false | Vterm {t_node= Tfalse} -> true
  | Vterm t when t_equal t t_bool_false -> true
  | Vconstr (rs, [], []) when rs_equal rs rs_false -> true
  | _ -> false

let fix_boolean_term t =
  if t_equal t t_true then t_bool_true else
  if t_equal t t_false then t_bool_false else t

let exec_pure ~loc env ls pvs =
  register_pure_call env loc ls Log.ExecConcrete;
  if ls_equal ls ps_equ then
    (* TODO (?) Add more builtin logical symbols *)
    let pv1, pv2 = match pvs with [pv1; pv2] -> pv1, pv2 | _ -> assert false in
    let v1 = Mvs.find pv1.pv_vs env.vsenv and v2 = Mvs.find pv2.pv_vs env.vsenv in
    Normal (value ty_bool (Vbool (compare_values v1 v2 = 0)))
  else if ls_equal ls fs_func_app then
    failwith "Pure function application not yet implemented"
  else
    match Decl.find_logic_definition env.pmodule.Pmodule.mod_theory.Theory.th_known ls with
    | Some defn ->
        let vs, t = Decl.open_ls_defn defn in
        let args = List.map (get_pvs env) pvs in
        let vsenv = List.fold_right2 Mvs.add vs args env.vsenv in
        let t = compute_term {env with vsenv} t in
        (* TODO A variable x binding the result of exec pure are used as (x = True) in
           subsequent terms, so we map true/false to True/False here. Is this reasonable? *)
        let t = fix_boolean_term t in
        Normal (value (Opt.get_def ty_bool t.t_ty) (Vterm t))
    | None ->
        kasprintf failwith "No logic definition for %a" print_ls ls

let pp_limited ?(n=100) pp fmt x =
  let s = asprintf "%a" pp x in
  let s = String.map (function '\n' -> ' ' | c -> c) s in
  let s = String.(if length s > n then sub s 0 (Pervasives.min n (length s)) ^ "..." else s) in
  pp_print_string fmt s

let print_result fmt = function
  | Normal v -> print_value fmt v
  | Excep (xs, v) -> fprintf fmt "EXC %a: %a" print_xs xs print_value v
  | Irred e -> fprintf fmt "IRRED: %a" (pp_limited print_expr) e

(******************************************************************************)
(*                                VALUE OF TERM                               *)
(******************************************************************************)

let value_of_constant ty c =
  let open Constant in
  match c with
  | ConstInt i -> value ty (Vnum i.Number.il_int)
  | ConstStr s -> string_value s
  | ConstReal _ -> failwith "not implemented: value_of_term real"

let value_of_term env t =
  let rec aux t =
    let ty = Opt.get_exn Exit t.t_ty in
    match t.t_node with
    | Ttrue -> bool_value true
    | Tfalse -> bool_value false
    | Tconst c -> value_of_constant ty c
    | Tapp (ls, ts) when ls.ls_constr > 0 ->
        let rs = try restore_rs ls with Not_found -> raise Exit in
        let fs = match (ity_of_ty ty).ity_node with
          | Ityapp (its, _, _) | Ityreg {reg_its= its} ->
              let defn = Pdecl.find_its_defn env.pmodule.Pmodule.mod_known its in
              defn.Pdecl.itd_fields
          | _ -> raise Exit in
        let vs = List.map aux ts in
        let res = value ty (Vconstr (rs, fs, List.map field vs)) in
        if env.rac.do_rac then check_type_invs env (ity_of_ty ty) res;
        res
    | _ -> raise Exit in
  try Some (aux t) with Exit -> None

(* Find a postcondition of the form [ensures { result = t (/\ ...) }],
   compute_fraction [t], and return it as a value. *)
let try_eval_ensures env posts =
  let rec loop vs = function
    | {t_node= Tapp (ls, [{t_node= Tvar vs'}; t])}
      when ls_equal ls ps_equ && vs_equal vs vs' ->
        let t = compute_term env t in
        value_of_term env t
    | {t_node= Tbinop (Tand, t1, t2)} ->
        let res = loop vs t1 in
        if res <> None then res else loop vs t2
    | _ -> None in
  let is_ensures_result = function
    | {t_node= Teps tb} -> let vs, t = t_open_bound tb in loop vs t
    | _ -> None in
  try Some (Lists.first is_ensures_result posts) with Not_found -> None

(******************************************************************************)
(*            GET AND REGISTER VALUES FOR VARIABLES AND CALL RESULTS          *)
(******************************************************************************)

(** A partial value generator with a string as a description. *)
type value_gen = string * (unit -> value option)

(** [get_value gens] takes a list of generators [gen] and returns the
    description and value for the first generator whose result is not [None]. *)
let get_value : value_gen list -> string * value =
  let aux (s, gen) = match gen () with Some v -> Some (s, v) | None -> None in
  Lists.first aux

(** Generate a value by querying the model for a variable *)
let gen_model_variable env ?loc id ity : value_gen =
  "value from model", fun () ->
    let res = env.rac.get_value ?loc id ity in
    Opt.iter (check_assume_type_invs ?loc env ity) res; res

(** Generator for a default value *)
let gen_default def : value_gen =
  "default value", fun () -> def

(** Generate a value by computing the postcondition *)
let gen_from_post env posts : value_gen =
  "value computed from postcondition", fun () ->
    Opt.bind posts (try_eval_ensures env)

(** Generator for the type default value, when [posts] are not none or [really]
    is true. *)
let gen_type_default ~really ?posts env ity : value_gen =
  "type default value", fun () ->
    if posts = None && not really then None else
    let v = default_value_of_type env.env env.pmodule.Pmodule.mod_known ity in
    try
      Opt.iter (check_posts env Vc.expl_post ~desc:"type default value" None v) posts;
      Some v
    with Contr _ | CannotCompute _ -> None

(** Generate a value by evaluating an optional expression, if that is not [None]
   *)
let gen_eval_expr env eval_expr id oexp =
  "RHS evaluated", fun () ->
    match oexp with
    | None -> None
    | Some e ->
        let env' = {env with rac= {env.rac with rac_abstract= false}} in
        register_const_init env id.id_loc id;
        match eval_expr env' e with
        | Normal v -> Some v
        | Excep _ ->
            cannot_compute "initialization of global variable `%a` raised an \
                            exception" print_decoded id.id_string
        | Irred _ -> None

(** Get a value from a list of generators and print debugging messages or fail,
    if no value is generated. *)
let get_value' ctx_desc oloc gens =
  let desc, value = try get_value gens with Not_found ->
    cannot_compute "missing value for %s" ctx_desc
      (Pp.print_option_or_default "NO LOC" Pretty.print_loc') oloc in
  Debug.dprintf debug_rac_values "@[<h>%s for %s at %a: %a@]@."
    (String.capitalize_ascii desc) ctx_desc
    (Pp.print_option_or_default "NO LOC" Pretty.print_loc') oloc print_value value;
  value

let is_ignore_id id = id.id_string = "_"

let get_and_register_value env ?def ?loc ?posts id ity =
  let ctx_desc = asprintf "variable `%a`%t" print_decoded id.id_string
      (fun fmt -> match loc with
         | Some loc -> fprintf fmt " at %a" Pretty.print_loc' loc
         | None -> ()) in
  let oloc = if loc <> None then loc else id.id_loc in
  let gens = [
    gen_model_variable env ?loc id ity;
    gen_from_post env posts;
    gen_default def;
    gen_type_default ~really:(is_ignore_id id) ?posts env ity;
  ] in
  let value = get_value' ctx_desc oloc gens in
  register_used_value env oloc id value;
  value

let get_and_register_param env id ity =
  let ctx_desc = asprintf "parameter `%a`" print_decoded id.id_string in
  let gens = [
    gen_model_variable env id ity;
    gen_type_default ~really:(is_ignore_id id) env ity;
  ] in
  let value = get_value' ctx_desc id.id_loc gens in
  register_used_value env id.id_loc id value;
  value

let get_and_register_global env eval_expr id oexp ity =
  let ctx_desc = asprintf "global `%a`" print_decoded id.id_string in
  let gens = [
    gen_model_variable env id ity;
    gen_eval_expr env eval_expr id oexp;
  ] in
  let value = get_value' ctx_desc id.id_loc gens in
  register_used_value env id.id_loc id value;
  value

(******************************************************************************)
(*                              SIDE EFFECTS                                  *)
(******************************************************************************)

let rec set_fields fs1 fs2 =
  let set_field f1 f2 =
    match (field_get f1).v_desc, (field_get f2).v_desc with
    | Vconstr (rs1, _, fs1), Vconstr (rs2, _, fs2) ->
        assert (rs_equal rs1 rs2);
        set_fields fs1 fs2
    | _ -> field_set f1 (field_get f2) in
  List.iter2 set_field fs1 fs2

let set_constr v1 v2 =
  match v1.v_desc, v2.v_desc with
   | Vconstr (rs1, _, fs1), Vconstr (rs2, _, fs2) ->
       assert (rs_equal rs1 rs2);
       set_fields fs1 fs2;
   | _ -> failwith "set_constr"

let assign_written_vars ?(vars_map=Mpv.empty) wrt loc env vs =
  let pv = restore_pv vs in
  if pv_affected wrt pv then (
    Debug.dprintf debug_trace_exec "@[<h>%tVAR %a is written in loop/function call %a@]@."
      pp_indent print_pv pv
      (Pp.print_option print_loc') pv.pv_vs.vs_name.id_loc;
    let pv = Mpv.find_def pv pv vars_map in
    let value = get_and_register_value env ~loc pv.pv_vs.vs_name pv.pv_ity in
    set_constr (get_vs env vs) value )

(******************************************************************************)
(*                               TIME LIMITS                                  *)
(******************************************************************************)

(* Internal start time *)
let time0 = ref None

let with_timelimit f =
  if !time0 <> None then failwith "with_timelimit: called twice";
  time0 := Some (Sys.time ());
  try
    let res = f () in
    time0 := None; res
  with e ->
    time0 := None;
    Printexc.raise_with_backtrace e (Printexc.get_raw_backtrace ())

let check_timelimit = function
  | None -> ()
  | Some timelimit ->
      match !time0 with
      | None -> failwith "check_timelimit: called outside with_timelimit"
      | Some time0 ->
          if Sys.time () -. time0 >= timelimit then
            cannot_compute "RAC timelimit reached"

(******************************************************************************)
(*                          EXPRESSION EVALUATION                             *)
(******************************************************************************)

let rec eval_expr env e =
  check_timelimit env.rac.timelimit;
  let _,l,bc,ec = Loc.get (Opt.get_def Loc.dummy_position e.e_loc) in
  Debug.dprintf debug_trace_exec "@[<h>%t%sEVAL EXPR %d %d-%d: %a@]@." pp_indent
    (if env.rac.rac_abstract then "Abs. " else "") l bc ec
    (pp_limited print_expr) e;
  let res = eval_expr' env e in
  Debug.dprintf debug_trace_exec "@[<h>%t -> %a@]@." pp_indent (print_result) res;
  res

(* abs = abstractly - do not execute loops and function calls - use
   instead invariants and function contracts to guide execution. *)
and eval_expr' env e =
  let loc_or_dummy = Opt.get_def Loc.dummy_position e.e_loc in
  match e.e_node with
  | Evar pvs ->
      let v = get_pvs env pvs in
      Debug.dprintf debug_trace_exec "[interp] reading var %s from env -> %a@\n"
        pvs.pv_vs.vs_name.id_string print_value v ;
      Normal v
  | Econst (Constant.ConstInt c) ->
      Normal (value (ty_of_ity e.e_ity) (Vnum (big_int_of_const c)))
  | Econst (Constant.ConstReal r) ->
      (* ConstReal can be float or real *)
      if ity_equal e.e_ity ity_real then
        let p, q = compute_fraction r.Number.rl_real in
        let sp, sq = BigInt.to_string p, BigInt.to_string q in
        try Normal (value ty_real (Vreal (Big_real.real_from_fraction sp sq)))
        with Mlmpfr_wrapper.Not_Implemented ->
          cannot_compute "mlmpfr wrapper is not implemented"
      else
        let c = Constant.ConstReal r in
        let s = Format.asprintf "%a" Constant.print_def c in
        Normal (value ty_real (Vfloat (Mlmpfr_wrapper.make_from_str s)))
  | Econst (Constant.ConstStr s) -> Normal (value ty_str (Vstring s))
  | Eexec (ce, cty) -> begin
      (* TODO (When) do we have to check the contracts in cty? When ce <> Capp? *)
      match ce.c_node with
      | Cpur (ls, pvs) ->
          Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR: EXEC PURE %a %a@]@." pp_indent print_ls ls
            (Pp.print_list Pp.comma print_value) (List.map (get_pvs env) pvs);
          let desc = asprintf "of `%a`" print_ls ls in
          if env.rac.do_rac then
            check_terms env (cntr_ctx ?loc:e.e_loc Vc.expl_pre ~desc ()) cty.cty_pre;
          with_push_premises env.premises @@ fun () -> (
          add_premises cty.cty_pre env;
          exec_pure ~loc:e.e_loc env ls pvs )
      | Cfun e' ->
        Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR EXEC FUN: %a@]@." pp_indent print_expr e';
        let add_free pv = Mvs.add pv.pv_vs (Mvs.find pv.pv_vs env.vsenv) in
        let cl = Spv.fold add_free ce.c_cty.cty_effect.eff_reads Mvs.empty in
        let mvs = snapshot_vsenv cl in
        ( match ce.c_cty.cty_args with
          | [] ->
             if env.rac.rac_abstract then begin
                 register_call env e.e_loc None mvs Log.ExecAbstract;
                 exec_call_abstract ~snapshot:cty.cty_oldies ?loc:e.e_loc env ce.c_cty [] e.e_ity
               end
             else begin
                 register_call env e.e_loc None mvs Log.ExecConcrete;
                 if env.rac.do_rac then
                   check_terms env (cntr_ctx ?loc:e.e_loc Vc.expl_pre ()) cty.cty_pre;
                 with_push_premises env.premises @@ fun () -> (
                 add_premises cty.cty_pre env;
                 eval_expr env e' )
               end
          | [arg] ->
              let match_free pv mt =
                let v = Mvs.find pv.pv_vs env.vsenv in
                ty_match mt pv.pv_vs.vs_ty v.v_ty in
              let mt = Spv.fold match_free cty.cty_effect.eff_reads Mtv.empty in
              let ty = ty_inst mt (ty_of_ity e.e_ity) in
              if cty.cty_pre <> [] then
                cannot_compute "anonymous function with precondition not supported (%a)"
                  Pp.(print_option_or_default "unknown location" Pretty.print_loc') e.e_loc;
              Normal (value ty (Vfun (cl, arg.pv_vs, e')))
          | _ -> cannot_compute "many args for exec fun" (* TODO *) )
      | Cany ->
         register_any_call env e.e_loc None Mvs.empty;
         if env.rac.do_rac then
           exec_call_abstract ~snapshot:cty.cty_oldies ?loc:e.e_loc env cty [] e.e_ity
         else (* We must check postconditions for abstract exec *)
           cannot_compute "cannot evaluate any-value with RAC disabled"
      | Capp (rs, pvsl) when
          Opt.map is_prog_constant (Mid.find_opt rs.rs_name env.pmodule.Pmodule.mod_known)
          = Some true ->
          if env.rac.do_rac then (
            let desc = asprintf "of `%a`" print_rs rs in
            let ctx = cntr_ctx ?loc:e.e_loc Vc.expl_pre ~desc () in
            check_terms env ctx cty.cty_pre );
          assert (cty.cty_args = [] && pvsl = []);
          let v = Mrs.find rs env.rsenv in
          if env.rac.do_rac then
            check_posts env Vc.expl_post None v rs.rs_cty.cty_post;
          Normal v
      | Capp (rs, pvsl) ->
          if ce.c_cty.cty_args <> [] then
            cannot_compute "no support for partial function applications (%a)"
              (Pp.print_option_or_default "unknown location" Pretty.print_loc')
              e.e_loc;
          exec_call ?loc:e.e_loc env rs pvsl e.e_ity
    end
  | Eassign l ->
      let search_and_assign (pvs, rs, v) =
        let rss, fs =
          match (get_pvs env pvs).v_desc with
          | Vconstr (_, rs, args) -> rs, args
          | _ -> assert false in
        let maybe_assign rs' f =
          if rs_equal rs' rs then (
            field_set f (get_pvs env v);
            raise Exit) in
        try List.iter2 maybe_assign rss fs
        with Exit -> () in
      List.iter search_and_assign l;
      Normal unit_value
  | Elet (ld, e2) -> (
    match ld with
    | LDvar (pvs, e1) -> (
      match eval_expr env e1 with
      | Normal v ->
        let env = bind_pvs pvs v env in
        eval_expr env e2
      | r -> r )
    | LDsym (rs, ce) ->
        let env = {env with funenv= Mrs.add rs ce env.funenv} in
        eval_expr env e2
    | LDrec l ->
        let env' =
          { env with
            funenv=
              List.fold_left
                (fun acc d ->
                  Mrs.add d.rec_sym d.rec_fun (Mrs.add d.rec_rsym d.rec_fun acc))
                env.funenv l } in
        eval_expr env' e2 )
  | Eif (e1, e2, e3) -> (
    match eval_expr env e1 with
    | Normal v ->
      if is_true v then
        eval_expr env e2
      else if is_false v then
        eval_expr env e3
      else (
        Debug.dprintf debug_trace_exec "Cannot eval if condition@.";
        Irred e )
    | r -> r )
  | Ewhile (cond, inv, var, e1) when env.rac.rac_abstract -> begin
      (* arbitrary execution of an iteration taken from the counterexample

        while e1 do invariant {I} e2 done
        ~>
        assert1 {I};
        assign_written_vars_with_ce;
        assert2* {I};
        if e1 then (e2;assert3 {I}; abort* ) else ()

        1 - if assert1 fails, then we have a real couterexample
            (invariant init doesn't hold)
        2 - if assert2 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        3 - if assert3 fails, then we have a real counterexample
            (invariant does not hold after iteration)
        * stop the interpretation here - raise RACStuck *)
      (* assert1 *)
      let res = with_push_premises env.premises @@ fun () -> (
      if env.rac.do_rac then
        check_terms env (cntr_ctx Vc.expl_loop_init ()) inv;
      add_premises inv env;
      register_iter_loop env e.e_loc Log.ExecAbstract;
      List.iter (assign_written_vars e.e_effect.eff_writes loc_or_dummy env)
        (Mvs.keys env.vsenv);
      (* assert2 *)
      let opt_old_variant =
        if env.rac.do_rac && e.e_effect.eff_oneway = Total then
          Some (oldify_variant env var) else None in
      check_assume_terms env (cntr_ctx Vc.expl_loop_keep ()) inv;
      add_premises inv env;
      match eval_expr env cond with
      | Normal v ->
         if is_true v then begin
             register_iter_loop env e.e_loc Log.ExecConcrete;
             match eval_expr env e1 with
             | Normal _ ->
                 if env.rac.do_rac then
                   check_terms env (cntr_ctx Vc.expl_loop_keep ()) inv;
                 add_premises inv env;
                 if env.rac.do_rac && e.e_effect.eff_oneway = Total then (
                   let old_ts, oldies = Opt.get opt_old_variant in
                   let vsenv =
                     Mvs.union (fun _ _ _ -> assert false) env.vsenv oldies in
                   let env = {env with vsenv} in
                   check_term env (cntr_ctx Vc.expl_loop_vari ())
                     (mk_variant_term env e.e_loc Vc.expl_loop_vari old_ts var)
                 );
                 (* the execution cannot continue from here *)
                register_stucked env e.e_loc
                  "Cannot continue after arbitrary iteration" Mid.empty;
                raise (RACStuck (env,e.e_loc))
             | r -> r
           end
         else if is_false v then
           Normal unit_value
         else (
           Debug.dprintf debug_trace_exec "Cannot debug while condition@.";
           Irred e )
      | r -> r
      ) in
      add_premises inv env;
      res
    end
  | Ewhile (e1, inv, var, e2) ->
      let res = with_push_premises env.premises @@ fun () -> (
      if env.rac.do_rac then
        check_terms env (cntr_ctx Vc.expl_loop_init ()) inv ;
      add_premises inv env;
      let rec iter () =
        let opt_old_variant =
          if env.rac.do_rac && e.e_effect.eff_oneway = Total then
            Some (oldify_variant env var) else None in
        match eval_expr env e1 with
        | Normal v ->
            if is_true v then ( (* condition true *)
              register_iter_loop env e.e_loc Log.ExecConcrete;
              match eval_expr env e2 with
              | Normal _ -> (* body executed normally *)
                  if env.rac.do_rac then
                    check_terms env (cntr_ctx Vc.expl_loop_keep ()) inv;
                  add_premises inv env;
                  if env.rac.do_rac && e.e_effect.eff_oneway = Total then (
                    let old_ts, oldies = Opt.get opt_old_variant in
                    let vsenv =
                      Mvs.union (fun _ _ _ -> assert false) env.vsenv oldies in
                    let env = {env with vsenv} in
                    check_term env (cntr_ctx Vc.expl_loop_vari ())
                      (mk_variant_term env e.e_loc Vc.expl_loop_vari old_ts var) );
                  iter ()
              | r -> r
            ) else if is_false v then (* condition false *)
              Normal unit_value
            else (
              Debug.dprintf debug_trace_exec "Cannot eval while condition@.";
              Irred e )
        | r -> r in
      iter ()
      ) in
      add_premises inv env;
      res
  | Efor (i, (pvs1, dir, pvs2), _ii, inv, e1) when env.rac.rac_abstract -> begin
      (* TODO what to do with _ii? *)
      (* arbitrary execution of an iteartion taken from the counterexample
        for i = e1 to e2 do invariant {I} e done
        ~>
        let a = eval_expr e1 in
        let b = eval_expr e2 in
        if a <= b + 1 then begin
          bind_vs i a;
          assert1 {I};
          assign_written_vars_with_ce;
          let i = get_and_register_value ~def:(b+1) i in
          if not (a <= i <= b + 1) then abort1;
          if a <= i <= b then begin
            assert2* { I };
            eval_expr e;
            bind_vs i (i + 1) in
            assert3 {I};
            bind_vs i (b + 1);
          end;
          assert4* {I}
        end else ()

        1 - if assert1 fails, then we have a real counterexample
            (invariant init doesn't hold)
        2 - if assert2 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        3 - if assert3 fails, then we have a real counterexample
            (invariant does not hold after iteration)
        4 - if assert4 fails, then we have a false counterexample
            (invariant does not hold for the execution to continue)
        5 - abort1: we have a false counterexample
            (value assigned to i is not compatible with loop range) *)
      let res, v = with_push_premises env.premises @@ fun () -> (
      try
        let a = big_int_of_value (get_pvs env pvs1) in
        let b = big_int_of_value (get_pvs env pvs2) in
        let le, suc = match dir with
          | To -> BigInt.le, BigInt.succ
          | DownTo -> BigInt.ge, BigInt.pred in
        register_iter_loop env e.e_loc Log.ExecAbstract;
        (* assert1 *)
        if le a (suc b) then begin
          let env = bind_vs i.pv_vs (int_value a) env in
          if env.rac.do_rac then begin
            check_terms env (cntr_ctx Vc.expl_loop_init ()) inv end;
          add_premises inv env;
          List.iter (assign_written_vars e.e_effect.eff_writes loc_or_dummy env)
            (Mvs.keys env.vsenv);
          let def = int_value (suc b) in
          let i_val = get_and_register_value env ~def i.pv_vs.vs_name i.pv_ity in
          let env = bind_vs i.pv_vs i_val env in
          let i_bi = big_int_of_value i_val in
          if not (le a i_bi && le i_bi (suc b)) then begin
            let msg = asprintf "Iterating variable not in bounds" in
            let mid = Mid.singleton i.pv_vs.vs_name i_val in
            register_stucked env e.e_loc msg mid;
            raise (RACStuck (env,e.e_loc)) end;
          if le a i_bi && le i_bi b then begin
            register_iter_loop env e.e_loc Log.ExecAbstract;
            (* assert2 *)
            check_assume_terms env (cntr_ctx Vc.expl_loop_keep ()) inv;
            add_premises inv env;
            match eval_expr env e1 with
            | Normal _ ->
                let env = bind_vs i.pv_vs (int_value (suc i_bi)) env in
                (* assert3 *)
                if env.rac.do_rac then
                  check_terms env (cntr_ctx Vc.expl_loop_keep ()) inv;
                add_premises inv env;
                let env = bind_vs i.pv_vs (int_value (suc b)) env in
                (* assert4 *)
                let ctx = cntr_ctx Vc.expl_loop_keep ~desc:"with (b+1)" () in
                check_assume_terms env ctx inv;
                Normal unit_value, Some (suc b)
            | r -> r, None
          end
          else begin
            (* assert4 *)
            (* i is already equal to b + 1 *)
            let ctx = cntr_ctx Vc.expl_loop_keep ~desc:"after last iteration" () in
            check_assume_terms env ctx inv;
            Normal unit_value, match i_val.v_desc with Vnum n -> Some n | _ -> None
          end
        end
        else
          Normal unit_value, None
      with NotNum -> failwith "Something's not a number@."
      ) in
      Opt.iter (fun v -> add_premises inv (bind_vs i.pv_vs (int_value v) env)) v;
      res
    end
  | Efor (pvs, (pvs1, dir, pvs2), _i, inv, e1) ->
    let res, i = with_push_premises env.premises @@ fun () -> (
    let le, suc =
      match dir with
      | To -> BigInt.le, BigInt.succ
      | DownTo -> BigInt.ge, BigInt.pred in
    try
      let a = big_int_of_value (get_pvs env pvs1) in
      let b = big_int_of_value (get_pvs env pvs2) in
      let env = bind_vs pvs.pv_vs (value ty_int (Vnum a)) env in
      ( if env.rac.do_rac then
          check_terms env (cntr_ctx Vc.expl_loop_init ()) inv ) ;
      add_premises inv env;
      let rec iter i =
        Debug.dprintf debug_trace_exec "[interp] for loop with index = %s@."
          (BigInt.to_string i) ;
        if le i b then (
          register_iter_loop env e.e_loc Log.ExecConcrete;
          let env = bind_vs pvs.pv_vs (int_value i) env in
          match eval_expr env e1 with
          | Normal _ ->
              if env.rac.do_rac then
                check_terms env (cntr_ctx Vc.expl_loop_keep ()) inv ;
              iter (suc i)
          | r -> r, None
        ) else
          Normal unit_value, Some i
        in
      iter a
    with NotNum -> failwith "Something's not a number@."
    ) in
    Opt.iter (fun i -> add_premises inv (bind_vs pvs.pv_vs (int_value i) env)) i;
    res
  | Ematch (e0, ebl, el) -> (
      let r = eval_expr env e0 in
      match r with
      | Normal t -> (
          if ebl = [] then
            r
          else
            try exec_match env t ebl with Undetermined -> (
                Debug.dprintf debug_trace_exec "Match is undetermined@.";
                Irred e ) )
      | Excep (ex, t) -> (
        match Mxs.find ex el with
        | [], e2 ->
            (* assert (t = Vvoid); *)
            eval_expr env e2
        | [v], e2 ->
            let env' = bind_vs v.pv_vs t env in
            eval_expr env' e2
        | _ -> assert false (* TODO ? *)
        | exception Not_found -> r )
      | _ -> r )
  | Eraise (xs, e1) -> (
      let r = eval_expr env e1 in
      match r with Normal t -> Excep (xs, t) | _ -> r )
  | Eexn (_, e1) -> eval_expr env e1
  | Eassert (kind, t) ->
      if env.rac.do_rac then begin
          match kind with
            | Assert ->
                check_term env (cntr_ctx Vc.expl_assert ()) t;
                add_premises [t] env
            | Assume ->
                check_assume_term env (cntr_ctx Vc.expl_assume ()) t;
                add_premises [t] env
            | Check ->
                check_term env (cntr_ctx Vc.expl_check ()) t
        end;
      Normal unit_value
  | Eghost e1 ->
      Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR: GHOST %a@]@." pp_indent print_expr e1;
      (* TODO: do not eval ghost if no assertion check *)
      eval_expr env e1
  | Epure t ->
      Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR: PURE %a@]@." pp_indent print_term t;
      let t = compute_term env t in
      Normal (value (Opt.get t.t_ty) (Vterm t))
  | Eabsurd ->
      let ctx = cntr_ctx Vc.expl_absurd ?loc:e.e_loc () in
      raise (Contr (ctx env, t_false))

and exec_match env t ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
        Warning.emit "[Exec] Pattern matching not exhaustive in evaluation@." ;
        assert false
    | (p, e) :: rem -> (
      try
        let env' = matching env t p.pp_pat in
        eval_expr env' e
      with NoMatch -> iter rem ) in
  iter ebl

and exec_call ?(main_function=false) ?loc env rs arg_pvs ity_result =
  let arg_vs = List.map (get_pvs env) arg_pvs in
  Debug.dprintf debug_trace_exec "@[<h>%tExec call %a %a@]@."
    pp_indent print_rs rs Pp.(print_list space print_value) arg_vs;
  let env = multibind_pvs rs.rs_cty.cty_args arg_vs env in
  let env = {env with vsenv= snapshot_oldies rs.rs_cty.cty_oldies env.vsenv} in
  let res = with_push_premises env.premises @@ fun () -> (
  let exec_kind =
    let can_interpret_abstractly =
      if rs_equal rs rs_func_app then false else
        match find_definition env rs with
        | LocalFunction _ -> true | _ -> false in
    if env.rac.rac_abstract && can_interpret_abstractly && not main_function
    then Log.ExecAbstract
    else Log.ExecConcrete in
  let mvs = let aux pv v = pv.pv_vs, snapshot v in
    Mvs.of_list (List.map2 aux rs.rs_cty.cty_args arg_vs) in
  let check_pre_and_register_call ?(any_function=false) exec_kind =
    if not main_function then
      if any_function then
        register_any_call env loc (Some rs) mvs
      else
        register_call env loc (Some rs) mvs exec_kind;
    if env.rac.do_rac then (
      let desc = asprintf "of `%a`" print_rs rs in
      let ctx = cntr_ctx ?loc:loc Vc.expl_pre ~desc () in
      (if main_function then check_assume_terms else check_terms)
        env ctx rs.rs_cty.cty_pre );
    (* Module [Expr] adds a precondition "DECR f" to each recursive function
       "f", which is not defined in the context of Pinterp. TODO? *)
    let not_DECR = function
      | {t_node= Tapp (f, _)} ->
          not (Strings.has_prefix "DECR " f.ls_name.id_string)
      | _ -> true in
    add_premises (List.filter not_DECR rs.rs_cty.cty_pre) env in
  match exec_kind with
  | Log.ExecAbstract ->
      check_pre_and_register_call Log.ExecAbstract;
      exec_call_abstract ?loc ~rs env rs.rs_cty arg_pvs ity_result
  | Log.ExecConcrete ->
      let res =
        if rs_equal rs rs_func_app then begin
          check_pre_and_register_call Log.ExecConcrete;
          match arg_vs with
          | [{v_desc= Vfun (cl, arg, e)}; value] ->
              let env =
                let vsenv = Mvs.union (fun _ _ v -> Some v) env.vsenv cl in
                {env with vsenv} in
              let env = bind_vs arg value env in
              eval_expr env e
          | [{v_desc= Vpurefun (_, bindings, default)}; value] ->
              let v = try Mv.find value bindings with Not_found -> default in
              Normal v
          | _ -> assert false
          end
        else
          match rs, arg_vs with
          | {rs_logic= RLls ls}, [{v_desc= Vproj (ls', v)}]
            when ls_equal ls ls' -> (* Projection of a projection value *)
              check_pre_and_register_call Log.ExecConcrete;
              Normal v
          | _ -> match find_definition env rs with
            | LocalFunction (locals, ce) -> (
                let env = add_local_funs locals env in
                match ce.c_node with
                | Capp (rs', pvl) ->
                    Debug.dprintf debug_trace_exec "@[<h>%tEXEC CALL %a: Capp %a]@."
                      pp_indent print_rs rs print_rs rs';
                    check_pre_and_register_call Log.ExecConcrete;
                    exec_call ?loc env rs' (pvl @ arg_pvs) ity_result
                | Cfun body ->
                    Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: FUN/%d %a@]@."
                      pp_indent print_rs rs (List.length ce.c_cty.cty_args) (pp_limited print_expr) body;
                    let env = multibind_pvs ce.c_cty.cty_args arg_vs env in
                    check_pre_and_register_call Log.ExecConcrete;
                    eval_expr env body
                | Cany ->
                    if env.rac.do_rac then (
                      check_pre_and_register_call ~any_function:true Log.ExecAbstract;
                      exec_call_abstract ?loc ~rs env rs.rs_cty arg_pvs ity_result )
                    else (* We can't check the postcondition *)
                      cannot_compute "cannot apply an any-function %a with RAC disabled"
                        print_rs rs
                | Cpur _ -> assert false (* TODO ? *) )
            | Builtin f ->
                Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: BUILTIN@]@." pp_indent print_rs rs;
                check_pre_and_register_call Log.ExecConcrete;
                ( match f rs arg_vs with
                  | Some v -> Normal v
                  | None -> cannot_compute "cannot compute result of builtin `%a`"
                              Ident.print_decoded rs.rs_name.id_string )
            | Constructor its_def ->
                Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: CONSTRUCTOR@]@." pp_indent print_rs rs;
                check_pre_and_register_call Log.ExecConcrete;
                let mt = List.fold_left2 ty_match Mtv.empty
                    (List.map (fun pv -> pv.pv_vs.vs_ty) rs.rs_cty.cty_args) (List.map v_ty arg_vs) in
                let ty = ty_inst mt (ty_of_ity ity_result) in
                let vs = List.map field arg_vs in
                let v = value ty (Vconstr (rs, its_def.Pdecl.itd_fields, vs)) in
                if env.rac.do_rac then check_type_invs ?loc env ity_result v;
                Normal v
            | Projection _d -> (
                Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: PROJECTION@]@." pp_indent print_rs rs;
                check_pre_and_register_call Log.ExecConcrete;
                match rs.rs_field, arg_vs with
                | Some pv, [{v_desc= Vconstr (cstr, _, args)} as v] ->
                    let rec search constr_args args =
                      match constr_args, args with
                      | pv2 :: pvl, v :: vl ->
                          if pv_equal pv pv2 then
                            Normal (field_get v)
                          else search pvl vl
                      | _ -> kasprintf failwith "Cannot project %a by %a"
                               print_value v print_rs rs
                    in
                    search cstr.rs_cty.cty_args args
                | _ -> kasprintf failwith "Cannot project values %a by %a"
                         Pp.(print_list comma print_value) arg_vs
                         print_rs rs )
            | exception Not_found ->
                cannot_compute "definition of routine %s could not be found"
                  rs.rs_name.id_string in
      if env.rac.do_rac then (
        let desc = asprintf "of `%a`" print_rs rs in
        let loc = if main_function then None else loc in
        match res with
        | Normal v ->
            check_posts env Vc.expl_post ~desc loc v rs.rs_cty.cty_post
        | Excep (xs, v) ->
            let posts = Mxs.find xs rs.rs_cty.cty_xpost in
            check_posts env Vc.expl_xpost ~desc loc v posts
        | Irred _ -> () );
      res
  ) in
  add_post_premises rs.rs_cty res env;
  res

and exec_call_abstract ?snapshot ?loc ?rs env cty arg_pvs ity_result =
  (* let f (x1: ...) ... (xn: ...) = e
     ~>
     assert1 {f_pre};
     assign_written_vars_with_ce;
     assert2* {f_post};

     1 - if assert1 fails, then we have a real counterexample
     (precondition doesn't hold)
     2 - if assert2 fails, then we have a false counterexample
     (postcondition does not hold with the values obtained
     from the counterexample)
   *)
  let res = with_push_premises env.premises @@ fun () -> (
  let exn = CannotCompute {reason= "Abstract call without location"} in
  let loc = Opt.get_exn exn loc in
  let env = match snapshot with
    | Some oldies -> {env with vsenv= snapshot_oldies oldies env.vsenv}
    | None -> env in
  (* assert1 is already done above *)
  let res = match cty.cty_post with
    | p :: _ -> let (vs,_) = open_post p in vs.vs_name
    | _ -> id_register (id_fresh "result") in
  let vars_map = Mpv.of_list (List.combine cty.cty_args arg_pvs) in
  let asgn_wrt =
    assign_written_vars ~vars_map cty.cty_effect.eff_writes loc env in
  List.iter asgn_wrt (Mvs.keys env.vsenv);
  let res_v =
    get_and_register_value env ~loc ~posts:cty.cty_post res ity_result in
  (* assert2 *)
  let desc = match rs with
    | None -> "of anonymous function"
    | Some rs -> asprintf "of `%a`" print_rs rs in
  let ctx = cntr_ctx Vc.expl_post ~desc () in
  check_assume_posts env ctx res_v cty.cty_post;
  Normal res_v
  ) in
  add_post_premises cty res env;
  res

(******************************************************************************)
(*                             GLOBAL EVALUATION                              *)
(******************************************************************************)

let init_real (emin, emax, prec) = Big_real.init emin emax prec

let bind_globals ?rs_main mod_known env =
  let open Pdecl in
  let eval_global id d env =
    match d.pd_node with
    | PDlet (LDvar (pv, e)) ->
        Debug.dprintf debug_trace_exec "EVAL GLOBAL VAR %a at %a@."
          print_decoded id.id_string
          Pp.(print_option_or_default "NO LOC" print_loc') id.id_loc;
        let v = get_and_register_global env eval_expr id (Some e) e.e_ity in
        bind_vs pv.pv_vs v env
    | PDlet (LDsym (rs, ce)) when is_prog_constant d -> (
        Debug.dprintf debug_trace_exec "EVAL GLOBAL SYM CONST %a at %a@."
          print_decoded id.id_string
          Pp.(print_option_or_default "NO LOC" Pretty.print_loc') id.id_loc;
        assert (ce.c_cty.cty_args = []);
        let oexp = match ce.c_node with
          | Cany -> None | Cfun e -> Some e
          | _ -> failwith "eval_globals: program constant cexp" in
        let v =
          get_and_register_global env eval_expr id oexp ce.c_cty.cty_result in
        if env.rac.do_rac then (
          let desc = asprintf "of global variable `%a`" print_rs rs in
          let ctx = cntr_ctx Vc.expl_post ~desc () in
          check_assume_posts env ctx v ce.c_cty.cty_post );
        bind_rs rs v env )
    | _ -> env in
  let is_before id d (env, found_rs) =
    let found_rs_here = match d.pd_node with
      | PDlet (LDsym (rs, _)) -> Opt.equal rs_equal (Some rs) rs_main
      | PDlet (LDrec ds) ->
          List.exists (fun d -> Opt.equal rs_equal (Some d.rec_sym) rs_main) ds
      | _ -> false in
    let found_rs = found_rs || found_rs_here in
    let env = if found_rs then env else Mid.add id d env in
    env, found_rs in
  let mod_known, _ = Mid.fold is_before mod_known (Mid.empty, false) in
  Mid.fold eval_global mod_known env

let eval_global_fundef rac env pmodule locals e =
  with_timelimit @@ fun () ->
  get_builtin_progs env ;
  let env = default_env env rac pmodule in
  let env = bind_globals pmodule.Pmodule.mod_known env in
  let env = add_local_funs locals env in
  let res = eval_expr env e in
  res, env.vsenv, env.rsenv

let eval_rs rac env pm rs =
  let open Pmodule in
  with_timelimit @@ fun () ->
  let get_value env pv = get_and_register_param env pv.pv_vs.vs_name pv.pv_ity in
  get_builtin_progs env ;
  let env = default_env env rac pm in
  let env = bind_globals ~rs_main:rs pm.mod_known env in
  let env = multibind_pvs ~register:(register_used_value env rs.rs_name.id_loc)
      rs.rs_cty.cty_args (List.map (get_value env) rs.rs_cty.cty_args) env in
  register_exec_main env rs;
  let loc = Opt.get_def Loc.dummy_position rs.rs_name.id_loc in
  let res = exec_call ~main_function:true ~loc env rs rs.rs_cty.cty_args
      rs.rs_cty.cty_result in
  register_ended env rs.rs_name.id_loc;
  res, env

let report_eval_result body fmt (res, vsenv, rsenv) =
  let print_envs fmt =
    pp_env print_vs print_value fmt (Mvs.bindings vsenv);
    (* if not (Mvs.is_empty vsenv) && not (Mrs.is_empty rsenv) then
     *   fprintf fmt "%a" env_sep ();
     * pp_env print_rs print_value fmt (Mrs.bindings rsenv) *)
    ignore rsenv
  in
  match res with
  | Normal _ ->
      fprintf fmt "@[<hov2>result:@ %a@ =@ %a@]@,"
        print_ity body.e_ity print_logic_result res;
      fprintf fmt "@[<hov2>globals:@ %t@]" print_envs
  | Excep _ ->
      fprintf fmt "@[<hov2>exceptional result:@ %a@]@,"
        print_logic_result res;
      fprintf fmt "@[<hov2>globals:@ %t@]" print_envs
  | Irred _ ->
      fprintf fmt "@[<hov2>Execution error: %a@]@," print_logic_result res ;
      fprintf fmt "@[globals:@ %t@]" print_envs

let report_cntr fmt (ctx, term) =
  report_cntr fmt (ctx, "has failed", term)
