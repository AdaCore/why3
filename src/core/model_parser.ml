(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Format
open Term
open Ident
open Printer


let debug = Debug.register_info_flag "model_parser"
  ~desc:"Print@ debugging@ messages@ about@ parsing@ \
         the@ counter-example@ model."

(*
***************************************************************
**  Model elements
***************************************************************
*)

type model_element_kind =
  | Result
  | Call_result of Loc.position
  | Old
  | At of string
  | Loop_before
  | Loop_previous_iteration
  | Loop_current_iteration
  | Error_message
  | Other

let print_model_kind fmt = function
  | Result -> pp_print_string fmt "Result"
  | Call_result loc -> fprintf fmt "Call_result (file %a)" Loc.pp_position loc
  | Old -> pp_print_string fmt "Old"
  | At l -> fprintf fmt "At %s" l
  | Error_message -> pp_print_string fmt "Error_message"
  | Loop_before -> pp_print_string fmt "Loop_before"
  | Loop_previous_iteration -> pp_print_string fmt "Loop_previous_iteration"
  | Loop_current_iteration -> pp_print_string fmt "Loop_current_iteration"
  | Other -> pp_print_string fmt "Other"

type concrete_syntax_int = {
  int_value: Number.int_constant;
  int_verbatim: string
}

type concrete_syntax_bv = {
  bv_value: BigInt.t;
  bv_length: int;
  bv_verbatim : string
}

type concrete_syntax_real = {
  real_value: Number.real_constant;
  real_verbatim: string
}

type concrete_syntax_frac = {
  frac_num: concrete_syntax_real;
  frac_den: concrete_syntax_real;
  frac_verbatim: string
}

type concrete_syntax_float_value =
  | Plus_infinity | Minus_infinity
  | Plus_zero | Minus_zero
  | NaN
  | Float_number of
    {
      float_sign : concrete_syntax_bv;
      float_exp : concrete_syntax_bv;
      float_mant : concrete_syntax_bv;
      float_hex : string
    }

type concrete_syntax_float = {
    float_exp_size : int;
    float_significand_size : int;
    float_val : concrete_syntax_float_value
  }

type concrete_syntax_constant =
  | Boolean of bool
  | String of string
  | Integer of concrete_syntax_int
  | Real of concrete_syntax_real
  | Float of concrete_syntax_float
  | BitVector of concrete_syntax_bv
  | Fraction of concrete_syntax_frac

type concrete_syntax_quant = Forall | Exists
type concrete_syntax_binop = And | Or | Implies | Iff

type concrete_syntax_funlit_elts =
  {
    elts_index : concrete_syntax_term;
    elts_value : concrete_syntax_term;
  }

(** Function literal value *)
and concrete_syntax_funlit =
  {
    elts : concrete_syntax_funlit_elts list;
    others : concrete_syntax_term;
  }

(** Function arguments and body *)
and concrete_syntax_fun = { args : string list; body : concrete_syntax_term; }

and concrete_syntax_term =
  | Var of string
  | Const of concrete_syntax_constant
  | Apply of string * concrete_syntax_term list
  | If of concrete_syntax_term * concrete_syntax_term * concrete_syntax_term
  | Epsilon of string * concrete_syntax_term
  | Quant of concrete_syntax_quant * string list * concrete_syntax_term
  | Binop of concrete_syntax_binop * concrete_syntax_term * concrete_syntax_term
  | Not of concrete_syntax_term
  | Function of concrete_syntax_fun
  | FunctionLiteral of concrete_syntax_funlit
  | Record of (string * concrete_syntax_term) list
  | Proj of (string * concrete_syntax_term)
  | Let of (string * concrete_syntax_term) list * concrete_syntax_term


(* Pretty printing of concrete terms *)

let print_concrete_bv fmt { bv_value; bv_length; bv_verbatim } =
  ignore bv_value; ignore bv_length;
  fprintf fmt "%s" bv_verbatim

let print_concrete_float_value fmt = function
  | Plus_infinity -> pp_print_string fmt "+infty"
  | Minus_infinity -> pp_print_string fmt "-infty"
  | Plus_zero -> pp_print_string fmt "+0"
  | Minus_zero -> pp_print_string fmt "-0"
  | NaN -> pp_print_string fmt "NaN"
  | Float_number {float_exp;float_sign;float_mant;float_hex} ->
    fprintf fmt "number{exp=%a, sign=%a, mant=%a, hex=%s}"
      print_concrete_bv float_exp
      print_concrete_bv float_sign
      print_concrete_bv float_mant
      float_hex

let rec print_concrete_term fmt ct =
  match ct with
  | Var v -> pp_print_string fmt v
  | Const (Boolean b) -> pp_print_bool fmt b
  | Const (String s) -> Constant.print_string_def fmt s
  | Const (Integer {int_value; int_verbatim}) ->
      ignore int_value; pp_print_string fmt int_verbatim
  | Const (Real {real_value; real_verbatim}) ->
      ignore real_value; pp_print_string fmt real_verbatim
  | Const (Float { float_exp_size; float_significand_size; float_val } ) ->
    fprintf fmt
      "float{ @[<hov>exp_size = %d;@ significand_size = %d;@ value = %a@] }"
      float_exp_size
      float_significand_size
      print_concrete_float_value float_val
  | Const (BitVector bv) -> fprintf fmt "%a" print_concrete_bv bv
  | Const (Fraction {frac_num;frac_den;frac_verbatim}) ->
      ignore frac_num; ignore frac_den; fprintf fmt "%s" frac_verbatim
  | Apply ("=",[t1;t2]) ->
    fprintf fmt "%a = %a"
      print_concrete_term t1
      print_concrete_term t2
  | Apply (f,[]) -> pp_print_string fmt f
  | Apply (f,ctl) ->
    fprintf fmt "@[(%s@ %a)@]" f (Pp.print_list Pp.space print_concrete_term) ctl
  | If (b,t1,t2) ->
    fprintf fmt "@[if %a@ then %a@ else %a@]"
      print_concrete_term b
      print_concrete_term t1
      print_concrete_term t2
  | Epsilon (eps_vs,eps_t) ->
    fprintf fmt "epsilon %s.@ %a" eps_vs print_concrete_term eps_t
  | Quant (quant,quant_vars,quant_t) ->
    let quant_string = match quant with Forall -> "Forall" | Exists -> "Exists" in
    fprintf fmt "@[<hov 1>%s %a.@ %a@]" quant_string
      (Pp.print_list Pp.comma Pp.print_string) quant_vars
      print_concrete_term quant_t
  | Binop (op,t1,t2) ->
    let op_string = match op with
      | And -> "/\\"
      | Or -> "\\/"
      | Implies -> "->"
      | Iff -> "<->"
    in
    fprintf fmt "@[%a %s@ %a@]"
      print_concrete_term t1
      op_string
      print_concrete_term t2
  | Not ct' -> fprintf fmt "not %a" print_concrete_term ct'
  | FunctionLiteral {elts; others} ->
    let print_others fmt others =
      fprintf fmt "@[_ =>@ %a@]"
        print_concrete_term others
    in
    let print_indice_value fmt { elts_index; elts_value } =
      fprintf fmt "@[%a =>@ %a@]"
        print_concrete_term elts_index
        print_concrete_term elts_value
    in
    fprintf fmt "@[[|%a%a|]@]"
      (Pp.print_list_delim ~start:Pp.nothing ~stop:Pp.semi ~sep:Pp.semi print_indice_value) elts
      print_others others
  | Function {args; body} ->
    fprintf fmt "@[<hov 1>fun %a ->@ %a@]"
      (Pp.print_list Pp.space Pp.print_string) args
      print_concrete_term body
  | Record fields_values ->
    let print_field_value fmt (field,value) =
      fprintf fmt "@[%s =@ %a@]" field print_concrete_term value
    in
    fprintf fmt "@[<hv1>%a@]"
      (Pp.print_list_delim ~start:Pp.lbrace ~stop:Pp.rbrace ~sep:Pp.semi print_field_value) fields_values
  | Proj (proj_name,proj_value) ->
    fprintf fmt "@[{%s =>@ %a}@]" proj_name print_concrete_term proj_value
  | Let (ll, t) -> fprintf fmt "@[<hov 1>let %a@ in@ %a@]"
                      (Pp.print_list_delim ~start:Pp.nothing ~stop:Pp.semi ~sep:Pp.semi (Pp.print_pair Pp.print_string print_concrete_term)) ll
                      print_concrete_term t

(* Helper functions for concrete terms *)

let concrete_var_from_vs vs =
  Var (Format.asprintf "@[<h>%a@]" Pretty.print_vs_qualified vs)
let concrete_const_bool b = Const (Boolean b)
let concrete_apply_from_ls ls ts =
  let ls_name = Format.asprintf "@[<h>%a@]" Pretty.print_ls_qualified ls in
  Apply (ls_name, ts)
let concrete_apply_equ t1 t2 = Apply ("=", [t1;t2])
let rec subst_concrete_term subst t =
  match t with
  | Var v -> (try Mstr.find v subst with _ -> t)
  | Const _ -> t
  | Apply (f, ctl) -> Apply (f, List.map (subst_concrete_term subst) ctl)
  | If (cb,ct1,ct2) ->
    If (subst_concrete_term subst cb,
        subst_concrete_term subst ct1,
        subst_concrete_term subst ct2)
  | Epsilon (cx,ct) -> Epsilon (cx, subst_concrete_term subst ct)
  | Quant (cq,ctl,ct) ->
    Quant (cq, ctl, subst_concrete_term subst ct)
  | Binop (op,ct1,ct2) ->
    Binop (op, subst_concrete_term subst ct1, subst_concrete_term subst ct2)
  | Not ct -> Not (subst_concrete_term subst ct)
  | Function {args; body} -> Function {args; body= subst_concrete_term subst body}
  | FunctionLiteral {elts; others} ->
    let elts =
      List.map
        (fun e ->
            { elts_index = subst_concrete_term subst e.elts_index;
              elts_value = subst_concrete_term subst e.elts_value })
        elts
    in
    let others = subst_concrete_term subst others in
    FunctionLiteral {elts; others}
  | Record fields_values ->
    Record (
      List.map
        (fun (field,value) -> (field, subst_concrete_term subst value))
        fields_values
    )
  | Proj (proj_name,proj_value) ->
    Proj (proj_name, subst_concrete_term subst proj_value)
  | Let (ll, t) -> Let (ll, subst_concrete_term subst t) (* Do I need to substitute inside the bound terms as well? *)
let rec t_and_l_concrete = function
  | [] -> concrete_const_bool true
  | [f] -> f
  | f::fl -> Binop (And, f, (t_and_l_concrete fl))

type model_element = {
  me_kind: model_element_kind;
  me_value: term;
  me_concrete_value: concrete_syntax_term;
  me_location: Loc.position option;
  me_attrs: Sattr.t;
  me_lsymbol: lsymbol;
}

let create_model_element ~value ~concrete_value ~oloc ~attrs ~lsymbol = {
  me_kind= Other;
  me_value= value;
  me_concrete_value= concrete_value;
  me_location= oloc;
  me_attrs= attrs;
  me_lsymbol= lsymbol
}

let get_lsymbol_or_model_trace_name me =
  Ident.get_model_trace_string
    ~name:(me.me_lsymbol.ls_name.id_string)
    ~attrs:(me.me_attrs)

(*
***************************************************************
**  Model definitions
***************************************************************
*)

type model_file = model_element list Mint.t
type model_files = model_file Mstr.t

type model = {
  model_files: model_files;
  vc_term_loc: Loc.position option;
  vc_term_attrs: Sattr.t;
}

let empty_model_file = Mint.empty
let empty_model_files = Mstr.empty
let is_model_empty m = Mstr.is_empty m.model_files

let empty_model = {
  vc_term_loc= None;
  vc_term_attrs= Sattr.empty;
  model_files= empty_model_files;
}

let set_model_files model model_files =
  { model with model_files }

let get_model_elements m =
  List.(concat (concat (map Mint.values (Mstr.values m.model_files))))

let get_model_term_loc m = m.vc_term_loc
let get_model_term_attrs m = m.vc_term_attrs

(** [search_model_element ?file ?line m p] searches a model element [me] in
    model [m], whose file is [file] and line is [line], and which fullfils
    [p me]. *)
let search_model_element ?file ?line m p =
  let iter_line f line' mes = if line = None || line = Some line' then
      List.iter f mes in
  let iter_file f file' lines = if file = None || file = Some file' then
      Mint.iter (iter_line f) lines in
  let iter_files f = Mstr.iter (iter_file f) m.model_files in
  try Some (Util.iter_first iter_files p) with Not_found -> None

let trace_by_id id =
  Ident.get_model_trace_string ~name:id.id_string ~attrs:id.id_attrs

let trace_by_name me = get_lsymbol_or_model_trace_name me

let search_model_element_for_id m ?loc id =
  let oloc = if loc <> None then loc else id.id_loc in
  let id_trace = trace_by_id id in
  let p me =
    if trace_by_name me = id_trace &&
       Option.equal Loc.equal me.me_location oloc
    then Some me else None in
  search_model_element m p

let search_model_element_call_result model (call_id : Expr.expr_id option) =
  match call_id with
  | None -> None
  | Some call_id ->
      let matching_eid attrs =
        match Ident.get_eid_attr attrs with
        | Some i -> i = call_id
        | _ -> false
      in
      let p me =
        (* [@model_trace:result] [@eid:<eid>] *)
        let has_model_trace_result attrs =
          get_model_trace_string ~name:"" ~attrs = "result"
        in
        if has_model_trace_result me.me_attrs && matching_eid me.me_attrs then
          Some me
        else
          None
      in
      search_model_element model p

(*
***************************************************************
**  Printing the model (JSON format and pretty printing)
***************************************************************
*)

let cmp_attrs a1 a2 =
  String.compare a1.attr_string a2.attr_string

(*
let model_element_equal n1 n2 =
  let me_kind_equal k1 k2 = match k1,k2 with
  | Result, Result
  | Old, Old
  | Loop_before, Loop_before
  | Loop_previous_iteration, Loop_previous_iteration
  | Loop_current_iteration, Loop_current_iteration
  | Error_message, Error_message
  | Other, Other -> true
  | Call_result l1, Call_result l2 -> Loc.equal l1 l2
  | At s1, At s2 -> String.equal s1 s2
  | _ -> false
  in
  me_kind_equal n1.me_kind n2.me_kind &&
  Term.t_equal n1.me_value n2.me_value &&
  Option.equal Loc.equal n1.me_location n2.me_location &&
  Sattr.equal n1.me_attrs n2.me_attrs &&
  Term.ls_equal n1.me_lsymbol n2.me_lsymbol
*)

(* FIXME: understand why some elements are duplicated *)
(*
let rec filter_duplicated l =
  let is_duplicated a l =
    List.exists (fun x -> model_element_equal a x) l in
  match l with
  | [] | [_] -> l
  | me :: l when is_duplicated me l -> filter_duplicated l
  | me :: l -> me :: filter_duplicated l
*)

let json_attrs attrs =
  let open Json_base in
  List (List.map
  (fun attr -> String attr.attr_string)
  (List.sort cmp_attrs (Sattr.elements attrs)))

let json_loc oloc =
  let open Json_base in
  match oloc with
  | None -> String "NO_LOC"
  | Some loc ->
    let f,sl,sc,el,ec = Loc.get loc in
  Record [
    "end-char", Int ec;
    "end-line", Int el;
    "file-name", String f;
    "start-char", Int sc;
    "start-line", Int sl
  ]

let rec json_type ty =
  let open Json_base in
  let open Ty in
  let open Pretty in
  match ty.ty_node with
  | Tyvar v ->
    Record [ "Tyvar", String (Format.asprintf "@[<h>%a@]" print_tv_qualified v) ]
  | Tyapp (ts, tl) ->
    Record [
      "Tyapp", Record [
        "ty_symbol", String (Format.asprintf "@[<h>%a@]" print_ts_qualified ts);
        "ty_args", List (List.map json_type tl)
      ]
    ]

let json_otype oty =
  let open Json_base in
  match oty with
  | None -> Null
  | Some ty -> json_type ty

let json_lsymbol ls =
  let open Json_base in
  let open Pretty in
  let ls_name = Format.asprintf "@[<h>%a@]" print_ls_qualified ls in
  Record [
    "name", String ls_name;
    "attrs", json_attrs ls.ls_name.id_attrs;
    "loc", json_loc ls.ls_name.id_loc;
  ]

let json_vsymbol ~forget vs =
  let open Pretty in
  let open Json_base in
  let vs_name = Format.asprintf "@[<h>%a@]" print_vs_qualified vs in
  if forget then forget_var vs;
  Record [
    "vs_name", String vs_name;
    "vs_type", json_type vs.vs_ty
  ]

let rec json_of_term t =
  let open Json_base in
  let open Pretty in
  match t.t_node with
  | Tvar vs -> Record [
    "Tvar", json_vsymbol ~forget:false vs
  ]
  | Tconst c ->
    let const_type = match c with
    | Constant.ConstInt _ -> "ConstInt"
    | Constant.ConstReal _ -> "ConstReal"
    | Constant.ConstStr _ -> "ConstStr"
    in
    Record [
      "Tconst", Record [
        "const_type", String const_type;
        "const_value", String (Format.asprintf "@[<h>%a@]" Constant.print_def c) ]
    ]
  | Tapp (ls,ts) ->
    Record [
    "Tapp",
    Record [
      "app_ls", String (Format.asprintf "@[<h>%a@]" print_ls_qualified ls) ;
      "app_args", List (List.map json_of_term ts) ]
  ]
  | Tif (t1,t2,t3) -> Record [
    "Tif",
    Record [
      "if", json_of_term t1;
      "then", json_of_term t2;
      "else", json_of_term t3 ]
  ]
  | Teps tb ->
    let vs,_,t' = t_open_lambda t in
    if vs = [] then
      let vs,t' = t_open_bound tb in
      Record [
      "Teps",
      Record [
        "eps_vs", json_vsymbol ~forget:true vs;
        "eps_t", json_of_term t' ]
      ]
    else
      Record [
      "Tfun",
      Record [
        "fun_args", List (List.map (json_vsymbol ~forget:true) vs);
        "fun_body", json_of_term t' ]
      ]
  | Tquant (q,tq) ->
    let quant = match q with Tforall -> "Tforall" | Texists -> "Texists" in
    let vsl,_,t' = t_open_quant tq in
    Record [
    "Tquant",
    Record [
      "quant", String quant;
      "quant_vs", List (List.map (fun vs -> (json_vsymbol ~forget:true) vs) vsl);
      "quant_t", json_of_term t' ]
    ]
  | Tbinop (op,t1,t2) ->
    let binop = match op with
    | Tand -> "Tand"
    | Tor -> "Tor"
    | Timplies -> "Timplies"
    | Tiff -> "Tiff"
    in
    Record [
    "Tbinop",
    Record [
      "binop", String binop;
      "binop_t1", json_of_term t1;
      "binop_t2", json_of_term t2
    ]
  ]
  | Tnot t' -> Record [
    "Tnot", json_of_term t'
  ]
  | Ttrue -> String "Ttrue"
  | Tfalse -> String "Tfalse"
  | Tlet _ -> Record [ "Tlet", String "UNSUPPORTED" ]
  | Tcase _ -> Record [ "Tcase", String "UNSUPPORTED" ]

let json_of_concrete_bv { bv_value; bv_length; bv_verbatim } =
  let open Json_base in
  Record [
    "bv_value_as_decimal", String (BigInt.to_string bv_value);
    "bv_length", Int bv_length;
    "bv_verbatim", String bv_verbatim
  ]

let json_of_concrete_real { real_value; real_verbatim } =
  let open Json_base in
  let real_value_string =
    Format.asprintf "@[<h>%a@]"
      (Number.(print_real_constant full_support)) real_value
  in
  Record [
    "type", String "Real";
    "val",
      Record [
        "real_value", String real_value_string;
        "real_verbatim", String real_verbatim
      ]
  ]

let json_of_float_value f =
  let open Json_base in
  match f with
  | Plus_infinity -> Record [ "float_type", String "Plus_Infinity" ]
  | Minus_infinity -> Record [ "float_type", String "Minus_infinity" ]
  | Plus_zero -> Record [ "float_type", String "Plus_zero" ]
  | Minus_zero -> Record [ "float_type", String "Minus_zero" ]
  | NaN -> Record [ "float_type", String "NaN" ]
  | Float_number {float_sign;float_exp;float_mant;float_hex} ->
    Record [
      "float_type", String "Float_value";
      "float_sign", json_of_concrete_bv float_sign;
      "float_exp", json_of_concrete_bv float_exp;
      "float_mant", json_of_concrete_bv float_mant;
      "float_hex", String float_hex
    ]

let [@warning "-42"] rec json_of_concrete_term ct =
  let open Json_base in
  match ct with
  | Var v -> Record [ "type", String "Var"; "val", String v ]

  | Const (Boolean b) -> Record [ "type", String "Boolean"; "val", Bool b ]
  | Const (String s) -> Record [ "type", String "String"; "val", String s ]
  | Const (Integer {int_value; int_verbatim}) ->
    let int_value_string =
      Format.asprintf "@[<h>%a@]"
        (Number.(print_int_constant full_support)) int_value
    in
    Record [
      "type", String "Integer";
      "val",
        Record [
          "int_value", String int_value_string;
          "int_verbatim", String int_verbatim
        ]
    ]
  | Const (Real d) -> json_of_concrete_real d
  | Const (BitVector bv) ->
    Record [ "type", String "BitVector"; "val", json_of_concrete_bv bv ]
  | Const (Fraction {frac_num;frac_den;frac_verbatim}) ->
    Record [
      "type", String "Fraction";
      "val",
        Record [
          "frac_num", json_of_concrete_real frac_num;
          "frac_den", json_of_concrete_real frac_den;
          "frac_verbatim", String frac_verbatim
        ]
    ]

  | Const (Float { float_val; _ }) ->
    Record [
      "type", String "Float";
      "val", json_of_float_value float_val
    ]

  | Apply (ls, args) ->
    Record [
      "type", String "Apply";
      "val", Record [
        "app_ls", String ls;
        "app_args", List (List.map json_of_concrete_term args)
      ]
    ]
  | If (b,t1,t2) ->
    Record [
      "type", String "If";
      "val", Record [
        "if", json_of_concrete_term b;
        "then", json_of_concrete_term t1;
        "else", json_of_concrete_term t2
      ]
    ]
  | Epsilon (eps_vs,eps_t) ->
    Record [
      "type", String "Epsilon";
      "val", Record [
        "eps_var", String eps_vs;
        "eps_t", json_of_concrete_term eps_t
      ]
    ]
  | Quant (quant,quant_vars,quant_t) ->
    let quant_string = match quant with Forall -> "Forall" | Exists -> "Exists" in
    Record [
      "type", String "Quant";
      "val", Record [
        "quant", String quant_string;
        "quant_vars", List (List.map (fun var -> String var) quant_vars);
        "quant_t", json_of_concrete_term quant_t
      ]
    ]
  | Let _ -> Record [ "type", String "Let"; "val", String "UNSUPPORTED" ]
  | Binop (op,t1,t2) ->
    let op_string = match op with
      | And -> "And"
      | Or -> "Or"
      | Implies -> "Implies"
      | Iff -> "Iff"
    in
    Record [
      "type", String "Binop";
      "val", Record [
        "binop", String op_string;
        "binop_t1", json_of_concrete_term t1;
        "binop_t2", json_of_concrete_term t2
      ]
    ]
  | Not t' -> Record [ "type", String "Not"; "val", json_of_concrete_term t' ]
  | FunctionLiteral {elts; others} ->
    Record [
      "type", String "FunctionLiteral";
      "val", Record [
        "funliteral_elts",
          List (
            List.map
              (fun { elts_index; elts_value }->
                Record [
                  "indice", json_of_concrete_term elts_index;
                  "value", json_of_concrete_term elts_value
                ])
              elts
          );
        "funliteral_others", json_of_concrete_term others
      ]
    ]
  | Function {args; body} ->
    Record [
      "type", String "Function";
      "val", Record [
        "fun_args", List (List.map (fun s -> String s) args);
        "fun_body", json_of_concrete_term body
      ]
    ]
  | Record fields_values ->
    Record [
      "type", String "Record";
      "val", List (
        List.map
          (fun (field,value) ->
            Record [
              "field", String field;
              "value", json_of_concrete_term value
            ])
          fields_values
      )
    ]
  | Proj (proj_name,proj_value) ->
    Record [
      "type", String "Proj";
      "val", Record [
        "proj_name", String proj_name;
        "proj_value", json_of_concrete_term proj_value
      ]
    ]
      [@@warning "-42"]

let json_model_element me =
  let open Json_base in
  let kind =
    match me.me_kind with
    | Result -> "result"
    | Call_result _ -> "result"
    | At l -> Printf.sprintf "@%s" l
    | Old -> "old"
    | Error_message -> "error_message"
    | Other -> "other"
    | Loop_before -> "before_loop"
    | Loop_previous_iteration ->"before_iteration"
    | Loop_current_iteration -> "current_iteration" in
  Record [
      "location", json_loc me.me_location;
      "attrs", json_attrs me.me_attrs;
      "value",
        Record [
          "value_type", json_otype me.me_value.t_ty;
          "value_term", json_of_term me.me_value;
          "value_concrete_term", json_of_concrete_term me.me_concrete_value ];
      "lsymbol", json_lsymbol me.me_lsymbol;
      "kind", String kind
    ]

let json_model_elements model_elements =
  Json_base.List (List.map json_model_element model_elements)

let json_model_elements_on_lines vc_term_loc (file_name, model_file) =
  let l =
    List.map (fun (i, e) ->
        let is_vc_line =
          match vc_term_loc with
          | None -> false
          | Some pos ->
              let vc_file_name, line, _, _, _ = Loc.get pos in
              file_name = vc_file_name && i = line in
        Json_base.(Record [
          "line", String (string_of_int i);
          "is_vc_line", Bool is_vc_line;
          "model_elements", json_model_elements e
        ]))
      (Mint.bindings model_file) in
  Json_base.List l

let json_model_files vc_term_loc model_files =
  let l =
    List.map (fun (file_name, model_file) ->
        Json_base.(Record [
          "filename", String file_name;
          "model",
          json_model_elements_on_lines vc_term_loc (file_name, model_file)
        ]))
      (Mstr.bindings model_files) in
  Json_base.List l

let json_model model = json_model_files model.vc_term_loc model.model_files

(*
***************************************************************
**  Quering the model
***************************************************************
*)

let pretty_model_element_name me =
  let name = get_lsymbol_or_model_trace_name me in
  let name = List.hd (Strings.bounded_split '@' name 2) in
  match me.me_kind with
  | Result -> "result"
  | Call_result loc ->
     asprintf "result of call at %a" Loc.pp_position_no_file loc
  | Old -> "old "^name
  | At l -> name^" at "^l
  | Loop_previous_iteration -> "[before iteration] "^name
  | Loop_current_iteration -> "[current iteration] "^name
  | Loop_before | Error_message | Other -> name

let print_model_element ?(print_locs=false) ~print_attrs fmt m_element =
  match m_element.me_kind with
  | Error_message ->
    pp_print_string fmt (pretty_model_element_name m_element)
  | _ ->
      fprintf fmt "@[<hv2>@[<hov2>%s%t :@]@ %a = %a@]"
        (pretty_model_element_name m_element)
        (fun fmt ->
           if print_attrs then
             fprintf fmt " %a" Pp.(print_list space Pretty.print_attr)
               (List.sort cmp_attrs (Sattr.elements m_element.me_attrs));
           if print_locs then
             fprintf fmt " (%a)"
               (Pp.print_option_or_default "NO LOC" Pretty.print_loc_as_attribute)
               m_element.me_location)
        (Pp.print_option (Pretty.print_ty)) m_element.me_value.t_ty
        print_concrete_term m_element.me_concrete_value

let print_model_elements ~print_attrs ?(sep = Pp.newline) fmt m_elements =
  fprintf fmt "@[%a@]"
    (Pp.print_list sep
       (print_model_element ?print_locs:None ~print_attrs))
    m_elements

let print_model_file ~print_attrs fmt (filename, model_file) =
  (* Relativize does not work on nighly bench: using basename instead. It
     hides the local paths. *)
  let filename = Filename.basename filename in
  let pp fmt (line, m_elements) =
    let cmp me1 me2 =
      let n =
        String.compare
          (get_lsymbol_or_model_trace_name me1)
          (get_lsymbol_or_model_trace_name me2)
      in
      if n = 0 then Sattr.compare me1.me_attrs me2.me_attrs else n in
    let m_elements = List.sort cmp m_elements in
    fprintf fmt "  @[<v 2>Line %d:@ %a@]" line
      (print_model_elements ?sep:None ~print_attrs)
      m_elements in
  fprintf fmt "@[<v 0>File %s:@ %a@]" filename
    Pp.(print_list space pp) (Mint.bindings model_file)

let print_model ~print_attrs fmt model =
  Pp.print_list Pp.newline (print_model_file ~print_attrs)
    fmt (Mstr.bindings model.model_files)

let get_model_file model filename =
  Mstr.find_def empty_model_file filename model

let get_elements model_file line_number =
  Mint.find_def [] line_number model_file

let get_padding line =
  try
    let r = Re.Str.regexp " *" in
    ignore (Re.Str.search_forward r line 0) ;
    Re.Str.matched_string line
  with Not_found -> ""

(* This assumes that l is sorted and split the list of locations in two:
   those that are applied on this line and the others. For those that are on
   this line, we split the locations that appear on several lines. *)
let rec partition_loc line lc l =
  match l with
  | (hd, a) :: tl ->
      let f, bl, bc, el, ec = Loc.get hd in
      if bl = line then
        if ec > lc then
          let old_sloc = Loc.user_position f bl bc el lc in
          let newlc = ec - lc in
          let new_sloc = Loc.user_position f (bl + 1) 1 el newlc in
          let rem_loc, new_loc = partition_loc line lc tl in
          ((new_sloc, a) :: rem_loc, (old_sloc, a) :: new_loc)
        else
          let rem_loc, new_loc = partition_loc line lc tl in
          (rem_loc, (hd, a) :: new_loc)
      else (l, [])
  | _ -> (l, [])

(* Change a location so that it points to a different line number *)
let add_offset off (loc, a) =
  let f, bl, bc, el, ec = Loc.get loc in
  (Loc.user_position f (bl + off) bc (el + off) ec, a)

let interleave_line ~filename:_ ~print_attrs start_comment end_comment
    model_file
    (source_code, line_number, offset, remaining_locs, locs) line =
  let remaining_locs, list_loc =
    partition_loc line_number (String.length line) remaining_locs in
  let list_loc = List.map (add_offset offset) list_loc in
  try
    let model_elements = Mint.find line_number model_file in
    let cntexmp_line =
      asprintf "@[<h 0>%s%s%a%s@]" (get_padding line) start_comment
        (print_model_elements ~sep:Pp.semi ~print_attrs)
        model_elements end_comment in
    (* We need to know how many lines will be taken by the counterexample. This
       is ad hoc as we don't really know how the lines are split in IDE. *)
    let len_cnt = 1 + (String.length cntexmp_line / 80) in
    source_code ^ line ^ cntexmp_line ^ "\n",
    line_number + 1,
    offset + len_cnt,
    remaining_locs,
    list_loc @ locs
  with Not_found ->
    source_code ^ line,
    line_number + 1,
    offset,
    remaining_locs,
    list_loc @ locs

let interleave_with_source ~print_attrs ?(start_comment = "(* ")
    ?(end_comment = " *)") model ~rel_filename
    ~source_code ~locations =
  let locations =
    List.sort
      (fun x y -> compare (fst x) (fst y))
      (List.filter
         (fun x ->
           let f, _, _, _,_ = Loc.get (fst x) in
           f = rel_filename)
         locations) in
  try
    (* There is no way to compare rel_filename and the locations of filename in
       the file because they contain extra ".." which cannot be reliably removed
       (because of potential symbolic link). So, we use the basename.
    *)
    let rel_filename = Filename.basename rel_filename in
    let model_files =
      Mstr.filter
        (fun k _ -> Filename.basename k = rel_filename)
        model.model_files in
    let model_file = snd (Mstr.choose model_files) in
    let src_lines_up_to_last_cntexmp_el source_code model_file =
      let last_cntexmp_line, _ = Mint.max_binding model_file in
      Re.Str.bounded_split (Re.Str.regexp "^") source_code
        (last_cntexmp_line + 1) in
    let source_code, _, _, _, gen_loc =
      List.fold_left
        (interleave_line ~filename:rel_filename ~print_attrs start_comment
           end_comment model_file)
        ("", 1, 0, locations, [])
        (src_lines_up_to_last_cntexmp_el source_code model_file) in
    (source_code, gen_loc)
  with Not_found -> (source_code, locations)
(*
***************************************************************
**  Get element kinds
***************************************************************
*)

let loc_starts_le loc1 loc2 =
  loc1 <> Loc.dummy_position && loc2 <> Loc.dummy_position &&
  let f1, l1, b1, _, _ = Loc.get loc1 in
  let f2, l2, b2, _, _ = Loc.get loc2 in
  f1 = f2 && (l1 < l2 || (l1 = l2 && b1 <= b2))

let while_loop_kind vc_attrs var_loc =
  let is_inv_pres a =
    a.attr_string = "expl:loop invariant preservation" ||
    a.attr_string = "expl:loop variant decrease" in
  if Sattr.exists is_inv_pres vc_attrs then
    let loop_loc =
      let is_while a = Strings.has_prefix "loop:" a.attr_string in
      let attr = Sattr.choose (Sattr.filter is_while vc_attrs) in
      Scanf.sscanf attr.attr_string "loop:%[^:]:%d:%d:%d:%d"
        Loc.user_position in
    Some (
      if var_loc = loop_loc then
        Loop_previous_iteration
      else if loc_starts_le loop_loc var_loc then
        Loop_current_iteration
      else
        Loop_before )
  else None

let get_loop_kind vc_attrs oloc () =
  Option.bind oloc (while_loop_kind vc_attrs)

let get_loc_kind oloc attrs () =
  match oloc with
  | None -> None
  | Some loc ->
      let f,l,_,_,_ = Loc.get loc in
      let search a =
        try
          Scanf.sscanf a.attr_string "at:%[^:]:loc:%[^:]:%d"
            (fun label f' l' ->
               if Filename.basename f = Filename.basename f' && l = l' then
                 Some (if label = "'Old" then Old else At label)
               else
                 None)
        with _ -> None in
      try Some (Lists.first search (Sattr.elements attrs)) with
        Not_found -> None

let get_call_result_kind attrs () =
  Option.map (fun l -> Call_result l)
    (search_attribute_value get_call_result_loc attrs)

let get_result_kind attrs () =
  match Ident.get_model_trace_attr ~attrs with
  | exception Not_found -> None
  | a ->
      match Strings.(bounded_split '@' a.attr_string 3) with
      | _ :: "result" :: _ -> Some Result
      | _ -> None

let compute_kind vc_attrs oloc attrs =
  try
    Lists.first (fun f -> f ()) [
      get_loc_kind oloc attrs;
      get_call_result_kind attrs;
      get_result_kind attrs;
      get_loop_kind vc_attrs oloc;
    ]
  with Not_found -> Other

(*
***************************************************************
**  Building the model
***************************************************************
*)

let add_to_model_if_loc ?kind me model =
  match me.me_location with
  | None -> model
  | Some pos ->
      let filename, line_number, _, _, _ = Loc.get pos in
      let model_file = get_model_file model filename in
      let me = match kind with
        | None -> me
        | Some me_kind -> {me with me_kind}
      in
      let elements = me :: get_elements model_file line_number in
      let elements = elements in
      let model_file = Mint.add line_number elements model_file in
      Mstr.add filename model_file model

let remove_field :
    ( Sattr.t * term * concrete_syntax_term ->
      Sattr.t * term * concrete_syntax_term ) ref =
  ref (fun x -> x)
let register_remove_field f = remove_field := f

(** Build the model by adding the element at all relevant locations *)
let build_model_rec pm (elts: model_element list) : model_files =
  let vc_attrs = pm.Printer.vc_term_attrs in
  let process_me me =
    let attrs = Sattr.union me.me_attrs me.me_lsymbol.ls_name.id_attrs in
    Debug.dprintf debug "@[<h>Term attrs for %s at %a:@ %a@]@."
      (pretty_model_element_name me)
      (Pp.print_option_or_default "NO LOC" Loc.pp_position) me.me_location
      Pretty.print_attrs attrs;
    (* Remove some specific record field related to the front-end language.
        This function is registered. *)
    (* FIXME is it used? *)
    let attrs, me_value, me_concrete_value =
      !remove_field (attrs, me.me_value, me.me_concrete_value) in
    Some {
      me_kind= Other; (* will be updated later on *)
      me_value;
      me_concrete_value;
      me_location= me.me_location;
      me_attrs= attrs;
      me_lsymbol= me.me_lsymbol
    } in
  let add_with_loc_set_kind me loc model =
    if loc = None then model else
      let kind = compute_kind vc_attrs loc me.me_attrs in
      add_to_model_if_loc ~kind {me with me_location= loc} model in
  (* Add a model element at the relevant locations *)
  let add_model_elt model me =
    let kind = compute_kind vc_attrs me.me_location me.me_attrs in
    let model = add_to_model_if_loc ~kind me model in
    let oloc = me.me_lsymbol.ls_name.id_loc in
    let model = add_with_loc_set_kind me oloc model in
    let add_written_loc a =
      add_with_loc_set_kind me (get_written_loc a) in
    Sattr.fold add_written_loc me.me_attrs model in
  List.fold_left add_model_elt Mstr.empty (List.filter_map process_me elts)


(*
***************************************************************
**  Filtering the model
***************************************************************
*)

let add_loc orig_model new_model position =
  (* Add a given location from orig_model to new_model *)
  let file_name, line_num, _, _, _ = Loc.get position in
  let orig_model_file = get_model_file orig_model file_name in
  let new_model_file = get_model_file new_model file_name in
  if Mint.mem line_num new_model_file then
    (* the location already is in new_model *)
    new_model
  else
    try
      (* get the location from original model *)
      let line_map = Mint.find line_num orig_model_file in
      (* add the location to new model *)
      let new_model_file = Mint.add line_num line_map new_model_file in
      Mstr.add file_name new_model_file new_model
    with Not_found -> new_model

let add_first_model_line filename model_file model =
  let line_num, cnt_info = Mint.min_binding model_file in
  let mf = get_model_file model filename in
  let mf = Mint.add line_num cnt_info mf in
  Mstr.add filename mf model

let model_for_positions_and_decls model ~positions =
  (* Start with empty model and add locations from model that
     are in locations *)
  let model_filtered =
    List.fold_left (add_loc model.model_files) empty_model_files positions in
  (* For each file add mapping corresponding to the first line of the
     counter-example from model to model_filtered.
     This corresponds to function declarations *)
  let model_filtered =
    Mstr.fold add_first_model_line model.model_files model_filtered in
  set_model_files model model_filtered

(*
***************************************************************
** Model cleaning
***************************************************************
*)

let map_filter_model_files f =
  let f_list elts =
    match List.filter_map f elts with
    | [] -> None | l -> Some l in
  let f_files mf =
    let mf = Mint.map_filter f_list mf in
    if Mint.is_empty mf then None else Some mf in
  Mstr.map_filter f_files

let opt_bind_all os f =
  if List.for_all Option.is_some os then
    f (List.map Option.get os)
  else None

class clean = object (self)
  method model m =
    {m with model_files= map_filter_model_files self#element m.model_files}
  method element me =
    Option.bind (self#value me.me_concrete_value) @@ fun me_concrete_value ->
    Some {me with me_concrete_value}
  method value v = match v with
    | Var v -> self#var v
    | Const c -> self#const c
    | Apply (s, vs) -> self#apply s vs
    | If (b,t1,t2) -> self#cond b t1 t2
    | Epsilon (x,t) -> self#epsilon x t
    | Not t -> self#neg t
    | Quant (q,vars,t) -> self#quant q vars t
    | Binop (op,t1,t2) -> self#binop op t1 t2
    | Record fs -> self#record fs
    | Proj (s,v) -> self#proj s v
    | Function {args;body} -> self#func args body
    | FunctionLiteral {elts;others} -> self#funliteral elts others
    | Let (ll, tt) -> self#lett ll tt
  method var v = Some (Var v)
  method const c = match c with
    | String v -> self#string v
    | Integer v -> self#integer v
    | Real v -> self#real v
    | Fraction v -> self#fraction v
    | Float v -> self#float v
    | Boolean v -> self#boolean v
    | BitVector v -> self#bitvector v
  method string v = Some (Const (String v))
  method integer v = Some (Const (Integer v))
  method real v = Some (Const (Real v))
  method fraction v = Some (Const (Fraction v))
  method float v = Some (Const (Float v))
  method boolean v = Some (Const (Boolean v))
  method bitvector v = Some (Const (BitVector v))
  method neg v =
    Option.bind (self#value v) @@ fun v ->
    Some (Not v)
  method apply s vs =
    opt_bind_all (List.map self#value vs) @@ fun vs ->
    Some (Apply (s, vs))
  method cond b t1 t2 =
    Option.bind (self#value b) @@ fun b ->
    Option.bind (self#value t1) @@ fun t1 ->
    Option.bind (self#value t2) @@ fun t2 ->
    Some (If (b,t1,t2))
  method epsilon x t =
    Option.bind (self#value t) @@ fun t ->
    Some (Epsilon (x,t))
  method lett ll tt =
    Option.bind (self#value tt) @@ fun tt ->
    let ll' = List.filter_map (fun (v,t) -> Option.bind (self#value t) @@ fun t -> Some (v, t)) ll in
    Some (Let (ll',tt))
  method quant q vars t =
    Option.bind (self#value t) @@ fun t ->
    Some (Quant (q,vars,t))
  method binop op t1 t2 =
    Option.bind (self#value t1) @@ fun t1 ->
    Option.bind (self#value t2) @@ fun t2 ->
    Some (Binop (op,t1,t2))
  method func args body =
    Option.bind (self#value body) @@ fun body ->
    Some (Function {args; body})
  method funliteral elts others =
    let clean_elt { elts_index = v1; elts_value = v2 } =
      Option.bind (self#value v1) @@ fun v1 ->
      Option.bind (self#value v2) @@ fun v2 ->
      Some { elts_index = v1; elts_value = v2 } in
    opt_bind_all (List.map clean_elt elts) @@ fun elts ->
    Option.bind (self#value others) @@ fun others ->
    Some (FunctionLiteral {elts; others})
  method record fs =
    let clean_field (f, v) =
      Option.bind (self#value v) @@ fun v ->
      Some (f, v) in
    opt_bind_all (List.map clean_field fs) @@ fun fs ->
    Some (Record fs)
  method proj s v =
    Option.bind (self#value v) @@ fun v ->
    Some (Proj (s,v))
end

let clean = ref (new clean)
let clean_model c model =
  clean := (c :> clean);
  !clean#model model

(*
***************************************************************
** Registering model parser
***************************************************************
*)

type model_parser = printing_info -> string -> model
type raw_model_parser = printing_info -> string -> model_element list

let debug_elements elts =
  let print_elements = print_model_elements ~sep:Pp.semi ~print_attrs:true in
  Debug.dprintf debug "@[<v>Elements:@ %a@]@." print_elements elts;
  elts

let debug_files files =
  let print_file = print_model_file ~print_attrs:true in
   Debug.dprintf debug "@[<v>Files:@ %a@]@."
     (Pp.print_list Pp.newline print_file) (Mstr.bindings files);
   files

let model_parser (raw: raw_model_parser) : model_parser =
  fun ({Printer.vc_term_loc; vc_term_attrs} as pm) str ->
  raw pm str |> debug_elements |>
  build_model_rec pm |> debug_files |>
  fun model_files -> { model_files; vc_term_loc; vc_term_attrs }

exception KnownModelParser of string
exception UnknownModelParser of string

type reg_model_parser = Pp.formatted * model_parser

let model_parsers : reg_model_parser Hstr.t = Hstr.create 17

let register_model_parser ~desc s p =
  if Hstr.mem model_parsers s then raise (KnownModelParser s) ;
  Hstr.replace model_parsers s (desc, model_parser p)

let lookup_model_parser s =
  snd (Hstr.find_exn model_parsers (UnknownModelParser s) s)

let list_model_parsers () =
  Hstr.fold (fun k (desc, _) acc -> (k, desc) :: acc) model_parsers []

let () =
  register_model_parser
    ~desc:
      "Model@ parser@ with@ no@ output@ (used@ if@ the@ solver@ does@ not@ \
       support@ models."
    "no_model" (fun _ _ -> [])
