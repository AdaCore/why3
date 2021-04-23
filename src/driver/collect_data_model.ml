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

open Wstdlib
open Printer
open Smtv2_model_defs

let debug_cntex = Debug.register_flag "cntex_collection"
    ~desc:"Intermediate representation debugging for counterexamples"

let is_true = function Model_parser.(Const (Boolean true)) -> true | _ -> false

type func_def = {
  args: (ident * typ option) list;
  res_type: typ option;
  body: term;
}

type context = {
  (** Bindings for top-level constants and function parameters *)
  values: Model_parser.model_value Mstr.t;

  (** Top-level function definitions *)
  functions: func_def Mstr.t;

  (** Bindings for prover variables, mutable to cache values during evaluation *)
  prover_values: Model_parser.model_value Hstr.t;

  (** Don't interprete prover vars, which is required to make the case analysis
     in projection and field functions *)
  opaque_prover_vars: bool;

  (** Other info fields *)
  fields_projs: Ident.ident Mstr.t;
  table: definition Mstr.t;
  pm: printer_mapping;
  list_records: string list Mstr.t;
}

(* let rec eval ctx oty t =
 *   Format.eprintf "@[<hv2>[EVAL %a %a@ (@[<h>%a@])@ (@[<h>%t@])@]@." Pp.(print_option string) oty print_term t Pp.(print_list space (print_pair string Model_parser.print_model_value_human)) (Mstr.bindings ctx.values)
 *     (fun fmt -> Hstr.iter (fun s -> Format.fprintf fmt "%s: %a, " s Model_parser.print_model_value_human) ctx.prover_values) ;
 *   let res = eval' ctx oty t in
 *   Format.eprintf "] -> %a@." Model_parser.print_model_value_human res;
 *   res *)

let rec eval ctx oty t =
  let open Model_parser in
  match t with
  | Tconst c -> Const c
  | Tunparsed s -> Unparsed s
  | Tprover_var (ty, v) ->
      if ctx.opaque_prover_vars then
        Var v
      else
        Opt.get_def (Var v) (eval_prover_var ctx ty v)
  | Tvar v ->
      if List.mem v ctx.pm.noarg_constructors then
        Apply (v, [])
      else
        Mstr.find_def (Var v) v ctx.values
  | Tite (t1, t2, t3) ->
      if is_true (eval ctx None t1) then eval ctx oty t2 else eval ctx oty t3
  | Tlet (bs, t) ->
      let aux values (s, t) = Mstr.add s (eval ctx None t) values in
      let values = List.fold_left aux ctx.values bs in
      eval {ctx with values} oty t
  | Tapply ("=", [t1; t2]) ->
      Const (Boolean (eval ctx None t1 = eval ctx None t2))
  | Tapply ("or", ts) ->
      Const (Boolean List.(exists is_true (map (eval ctx None) ts)))
  | Tapply ("and", ts) ->
      Const (Boolean List.(for_all is_true (map (eval ctx None) ts)))
  | Tapply ("not", [t]) -> (
      match eval ctx None t with
      | Const (Boolean b) -> Const (Boolean (not b))
      | t -> Apply ("not", [t]) )
  | Tapply (s, ts) -> (
      match Mstr.find_opt s ctx.list_records with
      | Some fs -> (* A record construction *)
          let ctx = {ctx with opaque_prover_vars= false} in
          Record List.(combine fs (map (eval ctx None (* TODO ty *)) ts))
      | None ->
          match Mstr.find_opt s ctx.functions with
          | Some fd -> (* A function call *)
              let bind_arg (v, ot) t = Mstr.add v (eval ctx ot t) in
              let values = List.fold_right2 bind_arg fd.args ts ctx.values in
              eval {ctx with values} fd.res_type fd.body
          | None -> (* Cannot reduce *)
              Apply (s, List.map (eval ctx None) ts) )
  | Tarray a ->
      Array (eval_array {ctx with opaque_prover_vars= false} a)
  | Tto_array t ->
      Array (eval_to_array {ctx with opaque_prover_vars= false} t)

and eval_prover_var ctx ty v =
  assert (not ctx.opaque_prover_vars);
  try Some (Hstr.find ctx.prover_values v) with Not_found ->
    let res =
      (* Format.eprintf "EVAL PROVER VAR' %s %s@." ty v; *)
      let aux name = function
        | Dfunction ([param, Some ty'], oty'', t)
          when Mstr.mem name ctx.fields_projs && ty' = ty -> (
            let values = Mstr.add param (Model_parser.Var v) ctx.values in
            match eval {ctx with values; opaque_prover_vars= true} oty'' t, oty'' with
                | Model_parser.Var v, Some ty'' -> eval_prover_var ctx ty'' v
                | mv, _ -> Some mv )
        | _ -> None in
      let fs = Mstr.bindings (Mstr.mapi_filter aux ctx.table) in
      (* Format.eprintf "EVAL VAR %s %s: %a@." v ty Pp.(print_list space string) (List.map fst fs); *)
      (* Format.eprintf "FIELDS for %s: %a@." v
       *   Pp.(print_list space (print_pair string Model_parser.print_model_value)) fs; *)
      if fs = [] then
        None
      else if List.for_all (fun (f, _) -> Mstr.mem f ctx.pm.list_fields) fs then
        Some (Model_parser.Record fs)
      else (
        match List.find_opt (fun (f, _) -> Mstr.mem f ctx.pm.list_projections) fs with
        | Some (f, t) -> Some (Model_parser.Proj (f, t))
        | None -> None ) in
    Opt.iter (Hstr.add ctx.prover_values v) res;
    res

and eval_array ctx = function
  | Aconst t -> Model_parser.{arr_indices= []; arr_others= eval ctx None t}
  | Avar v -> Format.ksprintf failwith "eval_array var %s" v (*try Aconst (Mstr.find v bindings) with Not_found -> a*)
  | Astore (a, key, value) ->
      let a = eval_array ctx a in
      let key = eval ctx None key and value = eval ctx None value in
      Model_parser.{a with arr_indices= {arr_index_key= key; arr_index_value= value} :: a.arr_indices}

and eval_to_array ctx = function
  | Tvar v -> (
      match Mstr.find_opt v ctx.functions with
      | Some {args= [arg, key_oty]; res_type= val_oty; body= t} ->
          let rec aux = function
            | Tite (Tapply ("=", [Tvar var; t1]), t2, t3) ->
                if var <> arg then Format.ksprintf failwith "eval_to_array %s - %s" arg var;
                let a = aux t3 in
                let ix = Model_parser.{
                    arr_index_key= eval ctx key_oty t1;
                    arr_index_value= eval ctx val_oty t2;
                  } in
                Model_parser.{a with arr_indices= ix :: a.arr_indices}
            | t -> Model_parser.{arr_others= eval ctx val_oty t; arr_indices= []} in
          aux t
      | _ -> Format.ksprintf failwith "eval_to_array %s" v )
  | Tarray a -> eval_array ctx a
  | t -> Format.kasprintf failwith "eval_to_array: %a" print_term t


(************************************************************************)
(*            Import Smtv2_model_defs to model elements                 *)
(************************************************************************)

let create_list pm (table: definition Mstr.t) =

  (* Convert list_records to take replace fields with model_trace when necessary. *)
  let list_records =
    let select fi =
      if fi.field_trace <> "" then fi.field_trace else
        match fi.field_ident with
        | Some id -> id.Ident.id_string
        | None -> fi.field_name in
    Mstr.mapi (fun _ -> List.map select) pm.Printer.list_records in

  let print_def fmt (s, def) =
    Format.fprintf fmt "%s: %a" s print_definition def in
  Debug.dprintf debug_cntex "@[<hv2>Table: %a@]@."
    Pp.(print_list newline print_def) (Mstr.bindings table);

  let consts =
    let aux = function
      | Dfunction ([], oty, t) -> Some (oty, t)
      | _ -> None in
    Mstr.map_filter aux table in

  let print_const fmt (s,(_,t)) = Format.fprintf fmt "%s: %a" s print_term t in
  Debug.dprintf debug_cntex "@[<hv2>Consts: %a@]@."
    Pp.(print_list newline print_const) (Mstr.bindings consts);

  let ctx =
    let fields_projs = fields_projs pm in
    let just_function = function
      | Dfunction (args, res_type, body) -> Some {args; res_type; body}
      | _ -> None in
    let functions = Mstr.map_filter just_function table in
    let ctx = {functions; values= Mstr.empty; prover_values= Hstr.create 5; pm;
               fields_projs; table; list_records; opaque_prover_vars= false} in
    let values = Mstr.map (fun (oty,t) -> eval ctx oty t) consts in
    {ctx with values} in

  let eval_const (oty, t) = eval ctx oty t in
  let res = Mstr.map eval_const consts in

  let print_mv fmt (s, mv) =
    Format.fprintf fmt "%s: %a" s Model_parser.print_model_value_human mv in
  Debug.dprintf debug_cntex "@[<hv2>Result: %a@]@."
    Pp.(print_list newline print_mv) (Mstr.bindings res);

  res
