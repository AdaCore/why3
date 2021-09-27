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

type func_def = {
  args: (ident * typ option) list;
  res_type: typ option;
  body: term;
}

type context = {
  (** Binding for function parameters and let variables *)
  values: Model_parser.model_value Mstr.t;

  (** Lazy bindings for top-level constants, initially all [None] *)
  consts: Model_parser.model_value Hstr.t;

  (** Lazy bindings for prover variables, mutable to cache values during
      evaluation *)
  prover_values: Model_parser.model_value Hstr.t;

  (** Top-level function definitions *)
  function_defs: func_def Mstr.t;

  (** Interprete prover vars, which is disabled when making the case analysis
      in projection and field functions *)
  interprete_prover_vars: bool;

  (** Other info fields *)
  fields_projs: Ident.ident Mstr.t;
  pm: printer_mapping;
  list_records: string list Mstr.t;
}

let is_true = function Model_parser.(Const (Boolean true)) -> true | _ -> false

(** Evaluate a term [t] while caching values for constants and prover variables
    in the context *)
let rec eval ctx oty t =
  let open Model_parser in
  match t with
  | Tconst c -> Const c
  | Tunparsed s -> Unparsed s
  | Tvar v when List.mem v ctx.pm.noarg_constructors ->
      Apply (v, [])
  | Tvar v -> (
      try Mstr.find v ctx.values with Not_found ->
      match Hstr.find ctx.consts v with
      | mv -> mv
      | exception Not_found -> eval_const ctx v )
  | Tprover_var (ty, v) ->
      if ctx.interprete_prover_vars then (
        try Hstr.find ctx.prover_values v with Not_found ->
          let res = eval_prover_var Mstr.empty ctx ty v in
          Debug.dprintf debug_cntex "Eval prover var %s: %a@." v
            Pp.(print_option_or_default "NO VALUE" print_model_value_human) res;
          let res = Opt.get_def (Var v) res in
          Hstr.add ctx.prover_values v res;
          res )
      else
        Var v
  | Tite (t1, t2, t3) ->
      if is_true (eval ctx None t1) then eval ctx oty t2 else eval ctx oty t3
  | Tlet (bs, t) ->
      let aux values (s, t) = Mstr.add s (eval ctx None t) values in
      let values = List.fold_left aux ctx.values bs in
      eval {ctx with values} oty t
  | Tapply ("=", [t1; t2]) ->
      let v1 = eval ctx None t1 in
      let v2 = eval ctx None t2 in
      Const (Boolean (compare_model_value_const v1 v2 = 0))
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
          let ctx = {ctx with interprete_prover_vars= true} in
          Record List.(combine fs (map (eval ctx None (* TODO ty *)) ts))
      | None ->
          match Mstr.find_opt s ctx.function_defs with
          | Some fd -> (* A function call *)
              let bind_arg (v, ot) t = Mstr.add v (eval ctx ot t) in
              let values = List.fold_right2 bind_arg fd.args ts ctx.values in
              eval {ctx with values} fd.res_type fd.body
          | None -> (* Cannot reduce *)
              Apply (s, List.map (eval ctx None) ts) )
  | Tarray a ->
      Array (eval_array {ctx with interprete_prover_vars= true} a)
  | Tto_array t ->
      Array (eval_to_array {ctx with interprete_prover_vars= true} t)

and eval_const ctx v =
  let res = match Mstr.find v ctx.function_defs with
    | exception Not_found ->
        Warning.emit "const %s not defined" v;
        None
    | def ->
        if def.args <> [] then (
          Warning.emit "variable %s defined by non-nullary function" v;
          None )
        else
          Some (eval ctx def.res_type def.body) in
  let res = Opt.get_def (Model_parser.Var v) res in
  Hstr.add ctx.consts v res;
  res

and eval_prover_var seen ctx ty v =
  (* The parameter [seen] records the names of (field and projection) functions
     (as map keys) and argument prover variables (in the map values), to detect
     unbounded recursion in the definitions of prover variables. *)
  Debug.dprintf debug_cntex "@[<hv2>Eval prover var %s:%s@]@." v  ty;
  let update_seen v old = Some (Sstr.add v (Opt.get_def Sstr.empty old)) in
  let already_seen fn v =
    let res = Sstr.mem v (Mstr.find_def Sstr.empty fn seen) in
    if res then Debug.dprintf debug_cntex "Recursion %s %s!@." fn v;
    res in
  (* [field_proj_value] applies functions that define fields or projections with
     with matching return type to the prover variable [v]. If the result is
     again a prover variable, it recurses on that. *)
  let field_proj_value fn def =
    match def.args with
    | [param, Some ty'] when Mstr.mem fn ctx.fields_projs && ty' = ty ->
        if already_seen fn v then (
          Debug.dprintf debug_cntex
            "Recursive definition for prover variable %s in model" v;
          None )
        else (
          Debug.dprintf debug_cntex
            "@[<hv2>Eval function %s for var %s@]@." fn v;
          let ctx' =
            { ctx with
              values= Mstr.add param (Model_parser.Var v) ctx.values;
              interprete_prover_vars= false } in
          match eval ctx' def.res_type def.body, def.res_type with
          | Model_parser.Var v, Some ty'' ->
              let seen = Mstr.change (update_seen v) fn seen in
              eval_prover_var seen ctx ty'' v
          | mv, _ -> Some mv )
    | _ -> None in
  match Mstr.bindings (Mstr.mapi_filter field_proj_value ctx.function_defs) with
  | [] -> None
  | fs ->
      let field_name_in m (f, _) = Mstr.mem f m in
      if List.for_all (field_name_in ctx.pm.list_fields) fs then
        Some (Model_parser.Record fs)
      else match List.find_opt (field_name_in ctx.pm.list_projections) fs with
        | Some (f, t) -> Some (Model_parser.Proj (f, t))
        | None -> None

and eval_array ctx = function
  | Aconst t -> Model_parser.{arr_indices= []; arr_others= eval ctx None t}
  | Avar v ->
      (match eval_const ctx v with
       | Model_parser.Array a -> a
       | _ -> Format.ksprintf failwith "eval array var %s not an array" v)
  | Astore (a, key, value) ->
      let a = eval_array ctx a in
      let arr_indices = Model_parser.({
          arr_index_key= eval ctx None key;
          arr_index_value= eval ctx None value
        } :: a.arr_indices) in
      {a with Model_parser.arr_indices}

and eval_to_array ctx = function
  | Tvar v -> (
      match Mstr.find_opt v ctx.function_defs with
      | Some {args= [arg, key_oty]; res_type= val_oty; body= t} ->
          let rec aux = function
            | Tite (Tapply ("=", [Tvar var; t1]), t2, t3) ->
                if var <> arg then
                  Format.ksprintf failwith "eval_to_array %s - %s" arg var;
                let a = aux t3 in
                let arr_indices = Model_parser.({
                    arr_index_key= eval ctx key_oty t1;
                    arr_index_value= eval ctx val_oty t2;
                  } :: a.arr_indices) in
                {a with Model_parser.arr_indices}
            | t ->
                Model_parser.{
                  arr_indices= [];
                  arr_others= eval ctx val_oty t;
                } in
          aux t
      | _ -> Format.ksprintf failwith "eval_to_array %s" v )
  | Tarray a -> eval_array ctx a
  | t -> Format.kasprintf failwith "eval_to_array: %a" print_term t


(************************************************************************)
(*            Import Smtv2_model_defs to model elements                 *)
(************************************************************************)

(** Create a mapping from the names of constants among the definitions to model
    values, which are obtained by evaluating the SMTv2 expressions by which
    the constants are defined. *)
let create_list pm (defs: definition Mstr.t) =

  (* Convert list_records to take replace fields with model_trace when
     necessary. *)
  let list_records =
    let select fi =
      if fi.field_trace <> "" then fi.field_trace else
        match fi.field_ident with
        | Some id -> id.Ident.id_string
        | None -> fi.field_name in
    Mstr.mapi (fun _ -> List.map select) pm.Printer.list_records in

  let fields_projs = fields_projs pm in

  let print_def fmt (s, def) =
    Format.fprintf fmt "%s: %a" s print_definition def in
  Debug.dprintf debug_cntex "@[<hv2>Definitions:%a@]@."
    Pp.(print_list_pre newline print_def) (Mstr.bindings defs);

  (* Collect the function definitions from the SMT definitions, for use
     during the evaluation of SMT expressions. *)
  let function_defs =
    let only_functions = function
      | Dfunction (args, res_type, body) -> Some {args; res_type; body}
      | _ -> None in
    Mstr.map_filter only_functions defs in

  (* The constant names, i.e. the keys of the resulting mapping *)
  let const_names =
    let is_const nm def =
      def.args = [] &&
      not (Mstr.mem nm fields_projs) &&
      not (List.mem nm pm.noarg_constructors) in
    Mstr.keys (Mstr.filter is_const function_defs) in

  Debug.dprintf debug_cntex "@[<hov2>Const defs:%a@]@."
    Pp.(print_list_pre comma string) const_names;

  (* The evaluation context *)
  let ctx =
    { values= Mstr.empty; consts= Hstr.create 7; prover_values= Hstr.create 7;
      function_defs; fields_projs; pm; list_records;
      interprete_prover_vars= true } in

  (* Evaluate the expressions by which the constants are defined *)
  let res =
    let for_const nm  =
      Debug.dprintf debug_cntex "@[<hv2>EVAL CONST %s@]@." nm;
      nm, eval_const ctx nm in
    Mstr.of_list (List.map for_const const_names) in

  let print_mv fmt (s, mv) =
    Format.fprintf fmt "%s: %a" s Model_parser.print_model_value_human mv in
  Debug.dprintf debug_cntex "@[<hv2>Result:%a@]@."
    Pp.(print_list_pre newline print_mv) (Mstr.bindings res);

  res
