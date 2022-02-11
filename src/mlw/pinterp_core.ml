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
open Ident
open Expr
open Term
open Ity
open Ty
open Pretty

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

let pp_env pp_key pp_value fmt l =
  let delims = Pp.nothing, Pp.nothing in
  pp_bindings ~delims ~sep:Pp.comma pp_key pp_value fmt l

exception Incomplete of string

let incomplete f =
  kasprintf (fun reason ->
      Debug.dprintf (Debug.lookup_flag "trace_exec") "Incomplete: %s@." reason;
      raise (Incomplete reason)) f

let ity_components ity = match ity.ity_node with
  | Ityapp (ts, l1, l2)
  | Ityreg {reg_its= ts; reg_args= l1; reg_regs= l2} ->
      ts, l1, l2
  | _ -> failwith "ity_components"

module rec Value : sig

  type float_mode = Mlmpfr_wrapper.mpfr_rnd_t
  type big_float = Mlmpfr_wrapper.mpfr_float

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
    | Vpurefun of ty (* keys *) * value Mv.t * value
    | Vfun of value Mvs.t (* closure *) * vsymbol * expr
    | Vterm of term
    (** Result of a pure expression *)
    | Vundefined
    (** An undefined value; unreducible *)
  and field = Field of value ref
  val compare_values : value -> value -> int
end = struct

  type float_mode = Mlmpfr_wrapper.mpfr_rnd_t
  type big_float = Mlmpfr_wrapper.mpfr_float

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
    | Vpurefun of ty (* keys *) * value Mv.t * value
    | Vfun of value Mvs.t (* closure *) * vsymbol * expr
    | Vterm of term
    | Vundefined
  and field = Field of value ref

  open Util

  let rec compare_values v1 v2 =
    if v1.v_desc = Vundefined then
      incomplete "undefined value of type %a cannot be compared" print_ty v1.v_ty;
    if v2.v_desc = Vundefined then
      incomplete "undefined value of type %a cannot be compared" print_ty v2.v_ty;
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

let num_value ity n = value (ty_of_ity ity) (Vnum n)

let float_value ity f = value (ty_of_ity ity) (Vfloat f)

let real_value r = value ty_real (Vreal r)

let string_value s = value ty_str (Vstring s)

let bool_value b = value ty_bool (Vbool b)

let constr_value ity rs fs vl =
  value (ty_of_ity ity) (Vconstr (rs, fs, List.map field vl))

let purefun_value ~result_ity ~arg_ity mv v =
  value (ty_of_ity result_ity) (Vpurefun (ty_of_ity arg_ity, mv, v))

let unit_value =
  value (ty_tuple []) (Vconstr (Expr.rs_void, [], []))

(**********************************************************************)

let range_value ity n =
  let valid_range =
    match ity_components ity with
    | { its_def = Range r }, _, _ -> (
        try
          Number.(check_range { il_kind = ILitUnk; il_int = n } r);
          true
        with Number.OutOfRange _ -> false )
    | _ -> true in
  if valid_range then
    Some (value (ty_of_ity ity) (Vnum n))
  else
    None

let proj_value ity ls v =
  let valid_range =
    match ity_components ity, v with
      | ({ its_def = Range r; its_ts= ts }, _, _), {v_desc= Vnum n}
        when ls.ls_name.id_string = ts.ts_name.id_string ^ "'int"
          && Opt.equal ty_equal ls.ls_value (Some ty_int) -> (
          try
            Number.(check_range { il_kind = ILitUnk; il_int = n } r);
            true
          with Number.OutOfRange _ ->
            false )
      | _ -> true in
  if valid_range then
    Some (value (ty_of_ity ity) (Vproj (ls, v)))
  else
    None

let mode_to_string m =
  let open Mlmpfr_wrapper in
  match m with
  | To_Nearest -> "RNE"
  | Away_From_Zero -> "RNA"
  | Toward_Plus_Infinity -> "RTP"
  | Toward_Minus_Infinity -> "RTN"
  | Toward_Zero -> "RTZ"
  | Faithful -> assert false

let rec print_value fmt v =
  if Debug.test_flag (Debug.lookup_flag "print_types") then
    fprintf fmt "(%a: %a)" print_value' v print_ty (v_ty v)
  else
    print_value' fmt v

and print_value' fmt v =
  match v.v_desc with
  | Vnum n ->
      if BigInt.ge n BigInt.zero then
        pp_print_string fmt (BigInt.to_string n)
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
  | Vfloat_mode m -> pp_print_string fmt (mode_to_string m)
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

let snapshot_vsenv = Mvs.map snapshot

let snapshot_oldies oldies vsenv =
  let aux old_pv pv =
    Mvs.add old_pv.pv_vs (snapshot (Mvs.find pv.pv_vs vsenv)) in
  Mpv.fold aux oldies vsenv

module Log = struct

  type exec_mode = Exec_giant_steps | Exec_normal

  type value_or_invalid = Value of value | Invalid

  type log_entry_desc =
    | Val_assumed of (ident * value)
    | Res_assumed of (rsymbol option * value)
    | Const_init of ident
    | Exec_call of (rsymbol option * value Mvs.t  * exec_mode)
    | Exec_pure of (lsymbol * exec_mode)
    | Exec_any of (rsymbol option * value Mvs.t)
    | Iter_loop of exec_mode
    | Exec_main of (rsymbol * value Mvs.t * value_or_invalid Mrs.t)
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

  let log_res log_uc ors v loc =
    log_entry log_uc (Res_assumed (ors,v)) (Some loc)

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
    let mrs = Mrs.map (fun v -> try Value (Lazy.force v) with _ -> Invalid) mrs in
    log_entry log_uc (Exec_main (rs,mvs,mrs)) loc

  let log_failed log_uc s mvs loc =
    log_entry log_uc (Exec_failed (s,mvs)) loc

  let log_stucked log_uc s mvs loc =
    log_entry log_uc (Exec_stucked (s,mvs)) loc

  let log_exec_ended log_uc loc =
    log_entry log_uc Exec_ended loc

  let get_log log_uc =
    !log_uc

  let flush_log log_uc =
    let res = List.rev !log_uc in
    log_uc := [];
    res

  let exec_kind_to_string ?(cap=true) = function
    | Exec_giant_steps -> if cap then "Giant-step" else "giant-step"
    | Exec_normal -> if cap then "Normal" else "normal"

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
    let vs2string vs = vs.vs_name.id_string in
    let rs2string rs = rs.rs_name.id_string in
    let id2string id = id.id_string in
    let print_value_or_invalid fmt = function
      | Value v -> print_value fmt v
      | Invalid -> Pp.string fmt "invalid value" in
    let print_assoc key2string print_value fmt (k,v) =
      fprintf fmt "@[%a = %a@]"
        print_decoded (key2string k) print_value v in
    let print_list key2string =
      Pp.print_list_pre Pp.newline (print_assoc key2string print_value) in
    let print_list_or_invalid =
      Pp.print_list_pre Pp.newline (print_assoc rs2string print_value_or_invalid) in
    match e.log_desc with
    | Val_assumed (id, v) ->
        fprintf fmt "@[<h2>%a = %a@]" print_decoded id.id_string print_value v;
    | Res_assumed (None,v) ->
        fprintf fmt "@[<h2>result = %a@]" print_value v
    | Res_assumed (Some rs,v) ->
        fprintf fmt "@[<h2>result of `%a` = %a@]" print_rs rs print_value v
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
           "@[<h2>(giant-step) execution of unimplemented function%t%t%a@]"
           (fun fmt -> Opt.iter (fprintf fmt " `%a`" print_rs) rs)
           (fun fmt -> if Mvs.is_empty mvs then fprintf fmt " with args:")
           (print_list vs2string) (Mvs.bindings mvs)
    | Iter_loop k ->
        fprintf fmt "@[<h2>%s iteration of loop@]" (exec_kind_to_string k)
    | Exec_main (rs, mvs, mrs) ->
        fprintf fmt "@[<h2>Execution of main function `%a` with env:%a%a@]"
          print_decoded rs.rs_name.id_string
          (print_list vs2string) (Mvs.bindings mvs)
          print_list_or_invalid (Mrs.bindings mrs)
    | Exec_failed (msg,mid) ->
       fprintf fmt "@[<h2>Property failure at %s with:%a@]"
         msg (print_list id2string) (Mid.bindings mid)
    | Exec_stucked (msg,mid) ->
       fprintf fmt "@[<h2>Execution got stuck at %s with:%a@]"
         msg (print_list id2string) (Mid.bindings mid)
    | Exec_ended ->
        fprintf fmt "@[<h2>Execution of main function terminated normally@]"

  let json_log entry_log =
    let open Json_base in
    let string f x = String (Format.asprintf "%a" f x) in
    let vs2string vs = vs.vs_name.id_string in
    let id2string id = id.id_string in
    let rs2string rs = rs.rs_name.id_string in
    let json_kind = function
      | Exec_giant_steps -> String "GIANT-STEPS"
      | Exec_normal -> String "NORMAL" in
    let value_or_undefined = function
        | Value v -> string print_value v
        | Invalid -> Null in
    let key_value key2string (k,v) =
      Record [
          "name", String (key2string k);
          "value", string print_value v
        ] in
    let key_value_or_undefined (k,v) =
      Record [
          "name", String (rs2string k);
          "value", value_or_undefined v
        ] in
    let log_entry = function
      | Val_assumed (id, v) ->
          Record [
              "kind", String "VAL_ASSUMED";
              "vs", string print_decoded id.id_string;
              "value", string print_value v
            ]
        | Res_assumed (None, v) ->
            Record [
                "kind", String "RES_ASSUMED";
                "value", string print_value v
              ]
        | Res_assumed (Some rs, v) ->
            Record [
                "kind", String "RES_ASSUMED";
                "rs", string print_rs rs;
                "value", string print_value v
              ]
        | Const_init id ->
            Record [
                "kind", String "CONST_INIT";
                "id", string print_decoded id.id_string
              ]
        | Exec_call (ors, mvs, kind) ->
            Record [
                "kind", String "EXEC_CALL";
                "rs", (match ors with
                       | Some rs -> string print_decoded rs.rs_name.id_string
                       | None -> Null);
                "exec", json_kind kind;
                "args", List (List.map (key_value vs2string) (Mvs.bindings mvs))
              ]
        | Exec_pure (ls, kind) ->
            Record [
                "kind", String "EXEC_PURE";
                "ls", string print_ls ls;
                "exec", json_kind kind
              ]
        | Exec_any (ors,mvs) ->
            Record [
                "kind", String "EXEC_ANY";
                "rs", (match ors with
                       | Some rs -> string print_decoded rs.rs_name.id_string
                       | None -> Null);
                "args", List (List.map (key_value vs2string) (Mvs.bindings mvs))
              ]
        | Iter_loop kind ->
            Record [
                "kind", String "ITER_LOOP";
                "exec", json_kind kind;
              ]
        | Exec_main (rs,mvs,mrs) ->
            Record [
                "kind", String "EXEC_MAIN";
                "rs", string print_decoded rs.rs_name.id_string;
                "env", List (List.map (key_value vs2string) (Mvs.bindings mvs));
                "globals", List (List.map key_value_or_undefined (Mrs.bindings mrs))
              ]
        | Exec_failed (reason,mid) ->
            Record [
                "kind", String "FAILED";
                "reason", String reason;
                "state", List (List.map (key_value id2string) (Mid.bindings mid))
              ]
        | Exec_stucked (reason,mid) ->
            Record [
                "kind", String "STUCKED";
                "reason", String reason;
                "state", List (List.map (key_value id2string) (Mid.bindings mid))
              ]
        | Exec_ended ->
            Record [ "kind", String "ENDED" ] in
    let entry e =
      let loc =
        match e.log_loc with
        | None -> String "NOLOC"
        | Some loc ->
            let f, l, b, e = Loc.get loc in
            Record [
                "filename", String f;
                "line", Int l;
                "start-char", Int b;
                "end-char", Int e
              ] in
      Record [
          "loc", loc;
          "entry", log_entry e.log_desc
        ] in
    List (List.map entry entry_log)

  (** verbosity level:
     1 : just imported values
     2 : + execution of function calls
     3 : + execution of loops
     4 : + termination of execution
     5 : + log information about initialization of global vars
   *)
  let print_log ?(verb_lvl=4) ~json fmt entry_log =
    if json then
      Json_base.print_json fmt (json_log entry_log)
    else
      let entry_log = List.filter (fun le ->
            match le.log_desc with
            | Val_assumed _ | Res_assumed _ | Const_init _ | Exec_main _ -> true
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

type bunch = term list list ref
type premises = bunch list ref

let mk_empty_premises () = ref [ref []]

let with_push_premises (premises: premises) f =
  premises := (ref []) :: !premises;
  let res = f () in
  premises := List.tl !premises;
  res

let add_premises ts (premises: premises) =
  let head = List.hd !premises in
  head := ts :: !head

let fold_premises f (premises: premises) init =
  let fold_terms f ts sofar = List.fold_left f sofar ts in
  let fold_bunch f bunch init = List.fold_right (fold_terms f) !bunch init in
  List.fold_right (fold_bunch f) !premises init

type env = {
  why_env  : Env.env;
  pmodule  : Pmodule.pmodule;
  funenv   : (cexp * rec_defn list option) Mrs.t;
  vsenv    : value Mvs.t;
  rsenv    : value Lazy.t Mrs.t; (* global constants *)
  premises : premises;
  log_uc   : Log.log_uc;
}

let mk_empty_env env pmodule =
  {pmodule; funenv= Mrs.empty; vsenv= Mvs.empty; rsenv= Mrs.empty;
   premises= mk_empty_premises (); why_env= env; log_uc= Log.empty_log_uc ()}

let snapshot_env env =
  let snapshot_rs l =
    if Lazy.is_val l then Lazy.from_val (snapshot (Lazy.force l)) else l in
  { env with
    vsenv= snapshot_vsenv env.vsenv;
    rsenv= Mrs.map snapshot_rs env.rsenv }

let get_vs env vs =
  try Mvs.find vs env.vsenv
  with Not_found ->
    ksprintf failwith "program variable %s not found in env"
      vs.vs_name.id_string

let get_pvs env pvs =
  get_vs env pvs.pv_vs

let bind_vs vs v ctx = {ctx with vsenv= Mvs.add vs v ctx.vsenv}

let bind_rs rs v ctx = {ctx with rsenv= Mrs.add rs v ctx.rsenv}

let bind_pvs ?register pv v_t ctx =
  let ctx = bind_vs pv.pv_vs v_t ctx in
  Opt.iter (fun r -> r pv.pv_vs.vs_name v_t) register;
  ctx

let multibind_pvs ?register l tl ctx =
  List.fold_left2 (fun ctx pv v -> bind_pvs ?register pv v ctx) ctx l tl

type check_value = ity -> value -> unit

type oracle = {
  for_variable:
    env -> ?check:check_value -> loc:Loc.position option -> Ident.ident -> Ity.ity -> value option;
  for_result:
    env -> ?check:check_value -> loc:Loc.position -> call_id:int option -> Ity.ity -> value option;
}

let oracle_dummy = {
  for_variable= (fun _ ?check:_ ~loc:_ _ _ -> None);
  for_result= (fun _ ?check:_ ~loc:_ ~call_id:_ _ -> None);
}

(******************************************************************************)
(*                              Log registration                              *)
(******************************************************************************)

let register_used_value env loc id value =
  Log.log_val env.log_uc id (snapshot value) loc

let register_res_value env loc ors value =
  Log.log_res env.log_uc ors (snapshot value) loc

let register_const_init env loc id =
  Log.log_const env.log_uc id loc

let register_call env loc rs mvs kind =
  Log.log_call env.log_uc rs (Mvs.map snapshot mvs) kind loc

let register_pure_call env loc ls kind =
  Log.log_pure_call env.log_uc ls kind loc

let register_any_call env loc rs mvs =
  Log.log_any_call env.log_uc rs (Mvs.map snapshot mvs) loc

let register_iter_loop env loc kind =
  Log.log_iter_loop env.log_uc kind loc

let register_exec_main env rs =
  Log.log_exec_main env.log_uc rs (Mvs.map snapshot env.vsenv)
    env.rsenv rs.rs_name.id_loc

let register_failure env loc reason mvs =
  Log.log_failed env.log_uc reason (Mid.map snapshot mvs) loc

let register_stucked env loc reason mvs =
  Log.log_stucked env.log_uc reason (Mid.map snapshot mvs) loc

let register_ended env loc =
  Log.log_exec_ended env.log_uc loc


(******************************************************************************)
(*                           CONTRADICTION CONTEXT                            *)
(******************************************************************************)

type cntr_ctx = {
  attr        : attribute;
  desc        : string option;
  loc         : Loc.position option;
  attrs       : Sattr.t;
  cntr_env    : env;
  giant_steps : bool option;
}

let describe_cntr_ctx ctx =
  asprintf "%s%a"
    (Strings.remove_prefix "expl:" ctx.attr.attr_string)
    (Pp.print_option (fun fmt -> fprintf fmt " %s")) ctx.desc

let report_cntr_title fmt (ctx, msg) =
  fprintf fmt "%s %s" (String.capitalize_ascii (describe_cntr_ctx ctx)) msg

let report_cntr_head fmt (ctx, msg, term) =
  fprintf fmt "@[<v>%a%t@]" report_cntr_title (ctx, msg)
    (fun fmt ->
       match ctx.loc, term.t_loc with
       | Some t1, Some t2 ->
           fprintf fmt " at %a@,- Defined at %a" print_loc' t1 print_loc' t2
       | Some t, None | None, Some t ->
           fprintf fmt " at %a" print_loc' t
       | None, None -> () )

let report_cntr_body fmt (ctx, term) =
  let cmp_vs (vs1, _) (vs2, _) =
    String.compare vs1.vs_name.id_string vs2.vs_name.id_string in
  let mvs = t_freevars Mvs.empty term in
  fprintf fmt "@[<hv2>- Term: %a@]@," print_term term ;
  fprintf fmt "@[<hv2>- Variables: %a@]" (pp_env print_vs print_value)
    (List.sort cmp_vs
       (Mvs.bindings
          (Mvs.filter (fun vs _ -> Mvs.contains mvs vs) ctx.cntr_env.vsenv)))

let report_cntr fmt (ctx, msg, term) =
  fprintf fmt "@[<v>%a@,%a@]"
    report_cntr_head (ctx, msg, term)
    report_cntr_body (ctx, term)

let mk_cntr_ctx env ~giant_steps ?loc ?(attrs=Sattr.empty) ?desc attr : cntr_ctx =
  { attr; desc; loc; attrs; cntr_env= snapshot_env env; giant_steps }

(**********************************************************************)

exception Fail of cntr_ctx * Term.term

exception Stuck of cntr_ctx * Loc.position option * string

let stuck ?loc ctx f =
  kasprintf (fun reason ->
      Debug.dprintf (Debug.lookup_flag "trace_exec") "Stuck: %s@." reason;
      raise (Stuck (ctx, loc, reason))) f

type check_term =
  ?vsenv:(Term.vsymbol * Term.term) list -> cntr_ctx -> Term.term -> unit

let check_term_dummy ?vsenv:_ _ _ =
  incomplete "check_term_dummy"

type rac = {
  check_term        : check_term;
  ignore_incomplete : bool;
}

let mk_rac ?(ignore_incomplete=false) check_term =
  { ignore_incomplete; check_term }

let rac_dummy =
  mk_rac check_term_dummy

(*************************************************************************)

let check_term rac ?vsenv cntr_ctx t =
  try rac.check_term ?vsenv cntr_ctx t
  with Incomplete reason when rac.ignore_incomplete ->
    Warning.emit "%s.@." reason

let check_terms rac ctx ts =
  try List.iter (rac.check_term ctx) ts
  with Incomplete reason when rac.ignore_incomplete ->
    Warning.emit "%s.@." reason

(* Check a post-condition [t] by binding the result variable to
   the term [vt] representing the result value.

   TODO Use Expr.term_of_post? *)
let check_post rac ctx v post =
  let vs, t = open_post post in
  let vsenv = Mvs.add vs v ctx.cntr_env.vsenv in
  let ctx = {ctx with cntr_env= {ctx.cntr_env with vsenv}} in
  try rac.check_term ctx t
  with Incomplete reason when rac.ignore_incomplete ->
    Warning.emit "%s.@." reason

let check_posts rac ctx v posts =
  try List.iter (check_post rac ctx v) posts
  with Incomplete reason when rac.ignore_incomplete ->
    Warning.emit "%s.@." reason

let check_type_invs rac ?loc ~giant_steps env ity v =
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
    let desc = asprintf "of type %a" print_ity ity in
    let ctx = mk_cntr_ctx env ?loc:loc ~desc ~giant_steps:(Some giant_steps) Vc.expl_type_inv in
    check_terms rac ctx def.Pdecl.itd_invariant

let opt_or o1 o2 = if o1 <> None then o1 else o2

let value_of_free_vars ctx t =
  let get_value get get_ty env x =
    let def = value (get_ty x) Vundefined in
    snapshot (Opt.get_def def (get x env))  in
  let mid = t_v_fold (fun mvs vs ->
    let get_ty vs = vs.vs_ty in
    let value = get_value Mvs.find_opt get_ty ctx.cntr_env.vsenv vs in
    Mid.add vs.vs_name value mvs) Mid.empty t in
  t_app_fold (fun mrs ls tyl ty ->
      let get_ty rs = ty_of_ity rs.rs_cty.cty_result in
      if tyl = [] && ty <> None then
        try let rs = restore_rs ls in
            let get x m = Opt.map Lazy.force (Mrs.find_opt x m) in
            let value = get_value get get_ty ctx.cntr_env.rsenv rs in
            Mid.add rs.rs_name value mrs
        with Not_found -> mrs
      else mrs
    ) mid t

let stuck_for_fail ?loc ctx t =
  let loc = opt_or loc (opt_or ctx.loc t.t_loc) in
  let mid = value_of_free_vars ctx t in
  register_stucked ctx.cntr_env loc (describe_cntr_ctx ctx) mid;
  stuck ?loc ctx "failure in %s" (describe_cntr_ctx ctx)

let check_assume_term rac ctx t =
  try check_term rac ctx t with Fail (ctx,t) ->
    stuck_for_fail ctx t

let check_assume_terms rac ctx tl =
  try check_terms rac ctx tl with Fail (ctx,t) ->
    stuck_for_fail ctx t

let check_assume_posts rac ctx v posts =
  try
    check_posts rac ctx v posts
  with Fail (ctx,t) ->
    stuck_for_fail ctx t

let check_term rac ?vsenv ctx t =
  try check_term rac ?vsenv ctx t with (Fail (ctx,t)) as e ->
    let mid = value_of_free_vars ctx t in
    register_failure ctx.cntr_env
      (opt_or ctx.loc t.t_loc) (describe_cntr_ctx ctx) mid;
    raise e

let check_terms rac ctx tl =
  try check_terms rac ctx tl with (Fail (ctx,t)) as e ->
    let mid = value_of_free_vars ctx t in
    register_failure ctx.cntr_env
      (opt_or ctx.loc t.t_loc) (describe_cntr_ctx ctx) mid;
    raise e

let check_posts rac ctx v posts =
  try
    check_posts rac ctx v posts
  with (Fail (ctx,t)) as e ->
    let mid = value_of_free_vars ctx t in
    register_failure ctx.cntr_env
      (opt_or ctx.loc t.t_loc) (describe_cntr_ctx ctx) mid;
    raise e

let check_assume_type_invs rac ?loc ~giant_steps env ity v =
  try check_type_invs rac ?loc ~giant_steps env ity v with Fail (ctx, t) ->
    stuck_for_fail ctx t

(* Currently, type invariants are only check when creating values or getting
   values from the model. TODO Check type invariants also during execution *)
let check_type_invs rac ?loc ~giant_steps env ity v =
  try check_type_invs rac ?loc ~giant_steps env ity v with Fail (ctx, t) as e ->
    let mid = value_of_free_vars ctx t in
    register_failure ctx.cntr_env
      (opt_or ctx.loc t.t_loc) (describe_cntr_ctx ctx) mid;
    raise e

(** [oldify_varl env vars] returns a pair [vars', oldies] where [vars'] are the
   variants, where all free variables have been replaced by fresh variables, and
   [oldies] is a mapping from the fresh variables in [vars'] to snapshots of the
   current values of the original variables in [env]. *)
let oldify_varl env varl =
  let free_vs = Mvs.keys (List.fold_left t_freevars Mvs.empty (List.map fst varl)) in
  let aux vs (subst, oldies) =
    let vs' = create_vsymbol (id_clone vs.vs_name) vs.vs_ty in
    let v = snapshot (Mvs.find vs env.vsenv) in
    Mvs.add vs (t_var vs') subst, Mvs.add vs' v oldies in
  let subst, oldies = List.fold_right aux free_vs (Mvs.empty, Mvs.empty) in
  List.map (fun (t, ols) -> t_subst subst t, ols) varl, oldies

(** [variant_term env loc olds news] creates a term representing the validity of
    variants [news] at location [loc], where [olds] are the oldified variants. *)
let variant_term env olds news =
  let {Pmodule.mod_theory= {Theory.th_export= ns}} =
    Pmodule.read_module env.why_env ["int"] "Int" in
  let ls_int_le = Theory.ns_find_ls ns [Ident.op_infix "<="] in
  let ls_int_lt = Theory.ns_find_ls ns [Ident.op_infix "<"] in
  let decrease_alg old_t t =
    Format.eprintf "RAC not implemented for %a@." Pretty.print_ty (t_type t);
    ignore (old_t, t); t_true in
  let decrease_def old_t t =
    let ty = t_type t in
    if ty_equal (t_type old_t) ty then
      match ty.ty_node with
        | Tyapp (ts, _) when ts_equal ts ts_int ->
            t_and
              (ps_app ls_int_le [t_nat_const 0; old_t])
              (ps_app ls_int_lt [t; old_t])
        | Tyapp (ts, _) when is_range_type_def ts.ts_def ->
            let ls = (* int_of_range env ts *)
              let rs = env.pmodule.Pmodule.mod_theory.Theory.th_ranges in
              match (Mts.find ts rs).Theory.td_node with
              | Theory.(Meta (_, [_; MAls ls])) -> ls | _ -> assert false in
            let proj t = fs_app ls [t] ty_int in
            ps_app ls_int_lt [proj t; proj old_t]
        | _ -> decrease_alg old_t t
    else
      decrease_alg old_t t in
  let rec decr = function
    | (old_t, Some old_r) :: olds, (t, Some r) :: varl when ls_equal old_r r ->
        t_or (ps_app r [t; old_t]) (* Checking well-foundedness omitted *)
          (t_and (t_equ old_t t) (decr (olds, varl)))
    | (old_t, None) :: olds, (t, None) :: news ->
        if oty_equal old_t.t_ty t.t_ty then
          t_or (decrease_def old_t t)
            (t_and (t_equ old_t t) (decr (olds, news)))
        else
          decrease_def old_t t
    | _::_, [] -> t_true
    | _ -> t_false in
  decr (olds, news)

let rec relocate loc t =
  t_attr_set ?loc t.t_attrs (TermTF.t_map (fun t -> t) (relocate loc) t)

let check_variant rac expl loc ~giant_steps env (old_varl, oldies) varl =
  let env = {env with vsenv=Mvs.union (fun _ _ v -> Some v) env.vsenv oldies} in
  let loc = match varl with (t,_)::_ when t.t_loc<>None -> t.t_loc | _ -> loc in
  let t = relocate loc (variant_term env old_varl varl) in
  let ctx = mk_cntr_ctx env ~giant_steps:(Some giant_steps) expl in
  check_term rac ctx (t_attr_set ?loc (Sattr.singleton expl) t)

(******************************************************************************)
(*                                 Auxiliaries                                *)
(******************************************************************************)

let is_range_ty ty =
  let its, _, _ = ity_components (ity_of_ty ty) in
  Ty.is_range_type_def its.its_def

(** [ty_app_arg ts nth ty] returns the nth argument in the type application [ty]. Fails
   when ty is not a type application of [ts] *)
let ty_app_arg ts ix ty = match ty.ty_node with
  | Tyapp (ts', ty_args) when ts_equal ts' ts ->
      List.nth ty_args ix
  | _ -> kasprintf failwith "@[<h>ty_arg: not a type application of %a: %a@]"
           print_ts ts print_ty ty

let t_undefined ty =
  t_eps_close (create_vsymbol (id_fresh "undefined") ty) t_true

let rec term_of_value ?(ty_mt=Mtv.empty) (env: env) vsenv v : (vsymbol * term) list * term =
  let ty = ty_inst ty_mt (v_ty v) in
  match v_desc v with
  | Vundefined ->
      vsenv, t_undefined ty
  | Vnum i ->
      if ty_equal ty ty_int || is_range_ty ty then
        vsenv, t_const (Constant.int_const i) ty
      else
        kasprintf failwith "term_of_value: value type not int or range but %a"
          print_ty ty
  | Vstring s ->
      ty_equal_check ty ty_str;
      vsenv, t_const (Constant.ConstStr s) ty_str
  | Vbool b ->
      ty_equal_check ty ty_bool;
      vsenv, if b then t_bool_true else t_bool_false
  | Vterm t ->
      Opt.iter (ty_equal_check ty) t.t_ty;
      vsenv, t
  | Vreal _ | Vfloat _ | Vfloat_mode _ -> (* TODO *)
      Format.kasprintf failwith "term_of_value: %a" print_value v
  | Vproj (ls, x) ->
      (* TERM: epsilon v. rs v = x *)
      let vs = create_vsymbol (id_fresh "v") ty in
      let vsenv, t_x = term_of_value ~ty_mt env vsenv x in
      let ty_x = ty_inst ty_mt (v_ty x) in
      let t = t_equ (fs_app ls [t_var vs] ty_x) t_x in
      vsenv, t_eps (t_close_bound vs t)
  | Vconstr (rs, field_rss, fs) -> (
      let match_field mt pv f =
        ty_match mt pv.pv_vs.vs_ty (ty_inst mt (v_ty (field_get f))) in
      let ty_mt = List.fold_left2 match_field ty_mt rs.rs_cty.cty_args fs in
      let term_of_field vsenv f = term_of_value ~ty_mt env vsenv (field_get f) in
      let vsenv, fs = Lists.map_fold_left term_of_field vsenv fs in
      match rs_kind rs with
      | RKfunc ->
          vsenv, fs_app (ls_of_rs rs) fs ty
      | RKnone when Strings.has_suffix "'mk" rs.rs_name.id_string ->
          let vs = create_vsymbol (id_fresh "v") ty in
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
        let vs' = create_vsymbol (id_clone vs.vs_name) (v_ty v) in
        let mt = ty_match mt vs.vs_ty (v_ty v) in
        let mv = Mvs.add vs (t_var vs') mv in
        let vsenv, t = term_of_value ~ty_mt env vsenv v in
        let vsenv = (vs', t) :: vsenv in
        mt, mv, vsenv in
      let mt, mv, vsenv = Mvs.fold bind_cl cl (Mtv.empty, Mvs.empty, vsenv) in
      (* Substitute argument type *)
      let ty_arg = ty_app_arg ts_func 0 ty in
      let vs_arg = create_vsymbol (id_clone arg.vs_name) ty_arg in
      let mv = Mvs.add arg (t_var vs_arg) mv in
      let mt = ty_match mt arg.vs_ty ty_arg in
      let t = t_ty_subst mt mv t in
      vsenv, t_lambda [vs_arg] [] t
  | Varray arr ->
      let open Pmodule in
      let {mod_theory= {Theory.th_export= ns}} =
        read_module env.why_env ["array"] "Array" in
      let ts_array = Theory.ns_find_ts ns ["array"] in
      if Debug.test_flag debug_array_as_update_chains_not_epsilon then
        (* TERM: (make <length arr> undefined)[<i> <- <arr[i]>] *)
        let ls_make = Theory.ns_find_ls ns ["make"] in
        let ls_update = Theory.ns_find_ls ns [Ident.op_update ""] in
        let t_length = t_nat_const (Array.length arr) in
        let ty_elt = ty_app_arg ts_array 0 ty in
        let t0 = fs_app ls_make [t_length; t_undefined ty_elt] ty in
        let rec loop vsenv sofar ix =
          if ix = Array.length arr then vsenv, sofar
          else
            let t_ix = t_nat_const ix in
            let vsenv, t_v = term_of_value ~ty_mt env vsenv arr.(ix) in
            let sofar = fs_app ls_update [sofar; t_ix; t_v] ty in
            loop vsenv sofar (succ ix) in
        loop vsenv t0 0
      else
        (* TERM: epsilon v. v.length = length arr /\ v[0] = arr.(ix) /\ ... *)
        let ls_length = Theory.ns_find_ls ns ["length"] in
        let ls_get = Theory.ns_find_ls ns [op_get ""] in
        let v = create_vsymbol (id_fresh "a") ty in
        let t_eq_length = (* v.length = length arr *)
          t_equ (fs_app ls_length [t_var v] ty_int)
            (t_nat_const (Array.length arr)) in
        let elt_ty = ty_app_arg ts_array 0 ty in
        let rec loop vsenv sofar ix = (* v[ix] = arr.(ix) *)
          if ix = Array.length arr then vsenv, List.rev sofar else
            let vsenv, t_a_ix = term_of_value ~ty_mt env vsenv arr.(ix) in
            let t_eq_ix =
              t_equ (fs_app ls_get [t_var v; t_nat_const ix] elt_ty) t_a_ix in
            loop vsenv (t_eq_ix :: sofar) (succ ix) in
        let vsenv, t_eq_ixs = loop vsenv [] 0 in
        let t = t_and_l (t_eq_length :: t_eq_ixs) in
        vsenv, t_eps (t_close_bound v t)
  | Vpurefun (ty', m, def) ->
      (* TERM: fun x -> if x = k0 then v0 else ... else def *)
      let vs_arg = create_vsymbol (id_fresh "x") ty' in
      let mk_case key value (vsenv, t) =
        let vsenv, key = term_of_value ~ty_mt env vsenv key in      (* k_i *)
        let vsenv, value = term_of_value ~ty_mt env vsenv value in  (* v_i *)
        let t = t_if (t_equ (t_var vs_arg) key) value t in (* if arg = k_i then v_i else ... *)
        vsenv, t in
      let vsenv, t = Mv.fold mk_case m (term_of_value ~ty_mt env vsenv def) in
      vsenv, t_lambda [vs_arg] [] t

type compute_term = env -> Term.term -> Term.term

let compute_term_dummy : compute_term = fun _ t -> t


(******************************************************************************)
(*                           TYPE DEFAULTS                                    *)
(******************************************************************************)

let is_array_its env its =
  let pm = Pmodule.read_module env ["array"] "Array" in
  let array_its = Pmodule.ns_find_its pm.Pmodule.mod_export ["array"] in
  its_equal its array_its

(* TODO Remove argument [env] after replacing Varray by model substitution *)
let rec default_value_of_type env ity : value =
  let ty = ty_of_ity ity in
  match ity.ity_node with
  | Ityvar _ -> failwith "default_value_of_type: type variable"
  | Ityapp (ts, _, _) when its_equal ts its_int -> value ty (Vnum BigInt.zero)
  | Ityapp (ts, _, _) when its_equal ts its_real -> assert false (* TODO *)
  | Ityapp (ts, _, _) when its_equal ts its_bool -> value ty (Vbool false)
  | Ityapp (ts, _, _) when its_equal ts its_str -> value ty (Vstring "")
  | Ityapp (ts,ityl1,_) when is_ts_tuple ts.its_ts ->
      let vs = List.map (default_value_of_type env) ityl1 in
      constr_value ity (rs_tuple (List.length ityl1)) [] vs
  | Ityapp (its, l1, l2)
  | Ityreg {reg_its= its; reg_args= l1; reg_regs= l2} ->
      if is_array_its env.why_env its then
        value ty (Varray (Array.init 0 (fun _ -> assert false)))
      else match Pdecl.find_its_defn env.pmodule.Pmodule.mod_known its with
        | {Pdecl.itd_its= {its_def= Range r}} ->
            let zero_in_range = BigInt.(le r.Number.ir_lower zero && le zero r.Number.ir_upper) in
            let n = if zero_in_range then BigInt.zero else r.Number.ir_lower in
            Opt.get (range_value ity n)
        | {Pdecl.itd_constructors= rs :: _; itd_fields= fs} ->
            let subst = its_match_regs its l1 l2 in
            let ityl = List.map (fun pv -> pv.pv_ity) rs.rs_cty.cty_args in
            let tyl = List.map (ity_full_inst subst) ityl in
            let vs = List.map (default_value_of_type env) tyl in
            constr_value ity rs fs vs
        | {Pdecl.itd_constructors= []} ->
            value ty Vundefined

let rec undefined_value env ity : value =
  let ty = ty_of_ity ity in
  match ity.ity_node with
  | Ityapp (ts,ityl1,_) when is_ts_tuple ts.its_ts ->
      let vs = List.map (undefined_value env) ityl1 in
      constr_value ity (rs_tuple (List.length ityl1)) [] vs
  | Ityapp (its, l1, l2)
  | Ityreg { reg_its = its; reg_args = l1; reg_regs = l2 } ->
      begin match Pdecl.find_its_defn env.pmodule.Pmodule.mod_known its with
      | { Pdecl.itd_constructors = [rs]; itd_fields = fs } ->
          let subst = its_match_regs its l1 l2 in
          let ityl = List.map (fun pv -> pv.pv_ity) rs.rs_cty.cty_args in
          let tyl = List.map (ity_full_inst subst) ityl in
          let vs = List.map (undefined_value env) tyl in
          constr_value ity rs fs vs
      | _ -> value ty Vundefined
      end
  | _ -> value ty Vundefined
