open Why3
open Ptree
open Gnat_ast
open Ptree_constructors

let debug = Debug.register_info_flag "gnat_ast" ~desc:"Output@ mlw@ file"

[@@@warning "-42"]

exception Conversion_error of {node_id: int; message: string}

let conversion_error node_id message () = raise (Conversion_error {node_id; message})

(** {1 Auxiliaries for conversion} *)

module Opt = struct
  let map f = function
    | None -> None
    | Some x -> Some (f x)

  let get default = function
    | Some x -> x
    | None -> default

  let force err = function
    | Some x -> x
    | None -> err ()

  let to_list = function
    | None -> []
    | Some x -> [x]
end

module List = struct
  include List

  let rec map_and_last for_not_last for_last l =
    match l with
    | [] -> []
    | [x] -> [for_last x]
    | x :: xs -> for_not_last x :: map_and_last for_not_last for_last xs

  let rec map_last for_last l =
    match l with
    | [] -> []
    | [x] -> [for_last x]
    | x :: xs -> x :: map_last for_last xs

  let rec get_last err = function
    | [x] -> x
    | _ :: xs -> get_last err xs
    | [] -> err ()

  let filter_map f l =
    map (Opt.force (fun () -> assert false))
      (filter ((<>) None)
         (map f l))
end

(** {1 Conversion functions from Gnat/JSON to Ptree} *)

let bigint_of_uint (Uint str) =
  BigInt.of_string str

let ident_add_suffix suffix id =
  {id with id_str=id.id_str^suffix}

let mk_label = function
  | No_symbol -> None
  | Symbol s -> Some (ATstr (Ident.create_attribute s))

let mk_location = function
  | Source_ptr r ->
      Some (Loc.user_position r.filename r.line 0 0)
  | No_location -> None

let mk_idents ~notation attrs =
  let f = Opt.get (fun s -> s) notation in
  List.map_and_last
    (mk_ident [])
    (fun s -> mk_ident attrs (f s))

let string_of_symbol = function
  | Symbol s -> Some s
  | No_symbol -> None

let strings_of_name (node : name_id) =
  let Name r = node.desc in
  let module_string =
    match r.module_ with
    | Some {desc=Module r} ->
        string_of_symbol r.name
    | _ -> None in
  let namespace_string = string_of_symbol r.namespace in
  let symb_string = string_of_symbol r.symb in
  Opt.(to_list module_string @ to_list namespace_string @ to_list symb_string)

let name_of_identifier (node: identifier_id) =
  let Identifier r = node.desc in
  r.name

let force_one err = function
  | [x] -> x
  | _ -> err ()

let mk_module_qident (node: module_id) =
  let Module m = node.desc in
  let file = mk_idents ~notation:None [] (Opt.to_list (string_of_symbol m.file)) in
  let name = mk_idents ~notation:None [] (Opt.to_list (string_of_symbol m.name)) in
  mk_qualid (file @ name)

let mk_idents_of_name ~notation attrs (node: name_id) =
  mk_idents ~notation attrs (strings_of_name node)

let mk_idents_of_identifier ~notation attrs (node: identifier_id) =
  mk_idents ~notation attrs (strings_of_name (name_of_identifier node))

let mk_ident_of_symbol id ~notation attrs sym =
  let notation = Opt.get (fun s -> s) notation in
  mk_ident attrs (notation (Opt.force (conversion_error id "empty symbol") (string_of_symbol sym)))

let mk_idents_of_type (node: type_id) =
  let Type r = node.desc in
  let idents = mk_idents_of_name ~notation:None [] r.name in
  if r.is_mutable then
    List.map_last (ident_add_suffix "__ref") idents
  else
    idents

let mk_include_declaration (node : include_declaration_id) =
  let Include_declaration r = node.desc in
  let qid = mk_module_qident r.module_ in
  match r.use_kind with
  | Import ->
      D.mk_useimport false [qid, None]
  | Export ->
      D.mk_useexport qid
  | Clone_default ->
      let Module m = r.module_.desc in
      D.mk_useimport false
        [qid, Some (mk_ident_of_symbol node.info.id ~notation:None [] m.name)]

let mk_pty_of_type (node : type_id) =
  Ty.mk_idapp (mk_qualid (mk_idents_of_type node)) []

let term_connector = function
  | Or_else -> `Or_asym
  | And_then -> `And_asym
  | Imply -> `Implies
  | Equivalent -> `Iff
  | Or -> `Or
  | And -> `And

let expr_connector id = function
  | And_then -> `And_asym
  | Or_else -> `Or_asym
  | _ -> conversion_error id "unexpected expression operator" ()

let unroll_name (node : name_id) =
  let Name {module_; symb} = node.desc in
  let aux (node: module_id) =
    let Module r = node.desc in
    string_of_symbol r.file, string_of_symbol r.name in
  Opt.map aux module_, string_of_symbol symb

let is_infix_identifier (node : identifier_id) =
  let Identifier r = node.desc in
  let Name r = r.name.desc in
  r.infix

(** Test if node is an unquantified OP1 *)
let is_op1 (node: identifier_id) =
  match List.rev (strings_of_name (name_of_identifier node)) with
  | s :: _ ->
      (* see why3/src/parser/parser.mly, lexer.mll *)
      List.exists (String.contains s)
        ['='; '<'; '>']
  | _ -> conversion_error node.info.id "empty operator identifier" ()

(** Test if node is an potentially quantified OP234 *)
let is_op234 (node: identifier_id) =
  match List.rev (strings_of_name (name_of_identifier node)) with
  | s :: _ ->
      (* see why3/src/parser/parser.mly, lexer.mll *)
      List.exists (String.contains s)
        ['+'; '-'; '*'; '/'; '\\'; '%'; '!'; '$'; '&'; '?'; '@'; '^'; '|']
  | _ -> conversion_error node.info.id "empty operator identifier" ()

let mk_pattern_of_prog (node : prog_id) =
  match node.desc with
  | _ -> failwith "mk_pattern_of_prog"

let mk_comment_attr = function
  | No_symbol -> None
  | Symbol s -> Some (mk_str ("GNAT-comment:"^s))

let mk_effects (effects: effects_id) =
  let Effects r = effects.desc in
  let reads =
    List.(map mk_qualid
            (map (mk_idents_of_identifier ~notation:None [])
               r.reads)) in
  let writes =
    List.(map (T.mk_var ?loc:None)
            (map mk_qualid
               (map (mk_idents_of_identifier ~notation:None [])
                  r.writes))) in
  let xpost =
    if r.raises = []
    then []
    else
      let aux id =
        mk_qualid (mk_idents_of_identifier ~notation:None [] id),
        None in
      [get_pos (), List.map aux r.raises] in
  reads, writes, xpost

module Curr = struct

  let loc_ref = ref No_location
  let marker_ref = ref No_symbol

  let with_ curr f =
    let push (loc, marker) =
      loc_ref := loc;
      marker_ref := marker in
    let pop () =
      let loc, marker = No_location, No_symbol in
      loc_ref := loc;
      marker_ref := marker in
    push curr;
    let res = f () in
    pop ();
    res

  let mk_attrs () =
    match !loc_ref with
    | No_location ->
        []
    | Source_ptr r ->
        let mark =
          match !marker_ref with
          | No_symbol -> ""
          | Symbol s -> "'@"^s^"@'" in
        Opt.(to_list (map mk_pos (mk_location (Source_ptr {r with filename=mark^r.filename}))))
end

let is_true t = match t.term_desc with
  | Ttrue -> true
  | _ -> false

let no_vcs_in_spec spec =
  spec.sp_post = [] && spec.sp_xpost = [] && spec.sp_variant = []

(** Check (syntactically) if an expression does not trigger any VCs, i.e. it does
    not contain any application (idapp, apply, infix, or innfix, any, which may
    generate preconditions), declaration (fun, rec, which may generate
    postconditions), or logical statement (absurd, assert, check). *)
let rec no_vcs_in_expr e = match e.expr_desc with
  | Eref | Etrue | Efalse | Econst _ | Eident _ | Easref _ ->
      true
  | Eidapp _ | Eapply _ | Einfix _ | Einnfix _ ->
      false (* preconditions of the callee *)
  | Elet (_, _, _, e1, e2) ->
      no_vcs_in_expr e1 && no_vcs_in_expr e2
  | Erec (funs, e) ->
      let aux (_, _, _, _, _, _, _, spec, e) =
        no_vcs_in_spec spec && no_vcs_in_expr e in
      List.for_all aux funs && no_vcs_in_expr e
  | Efun (_, _, _, _, spec, e) ->
      no_vcs_in_spec spec && no_vcs_in_expr e
  | Eany (_, _, _, _, _, spec) ->
      spec.sp_pre = [] (* existence *)
  | Etuple es ->
      List.for_all no_vcs_in_expr es
  | Erecord fs ->
      List.for_all (fun (_, e) -> no_vcs_in_expr e) fs
  | Eupdate (e, fs) ->
      no_vcs_in_expr e &&
      List.for_all (fun (_, e) -> no_vcs_in_expr e) fs
  | Eassign ans ->
      List.for_all (fun (e1, _, e2) -> no_vcs_in_expr e1 && no_vcs_in_expr e2) ans
  | Esequence (e1, e2) ->
      no_vcs_in_expr e1 && no_vcs_in_expr e2
  | Eif (e1, e2, e3) ->
      no_vcs_in_expr e1 && no_vcs_in_expr e2 && no_vcs_in_expr e3
  | Ewhile (e1, inv, var, e2) ->
      inv = [] && var = [] &&
      no_vcs_in_expr e1 && no_vcs_in_expr e2
  | Eand (e1, e2) | Eor (e1, e2) ->
      no_vcs_in_expr e1 && no_vcs_in_expr e2
  | Enot e ->
      no_vcs_in_expr e
  | Ematch (e, regs, exns) ->
      no_vcs_in_expr e &&
      List.for_all (fun (_, e) -> no_vcs_in_expr e) regs &&
      List.for_all (fun (_, _, e) -> no_vcs_in_expr e) exns
  | Eabsurd ->
      false
  | Epure _ | Eidpur _ | Eraise (_, None) ->
      true
  | Eraise (_, Some e) | Eexn (_, _, _, e) | Eoptexn (_, _, e) ->
      no_vcs_in_expr e
  | Efor (_, e1, _, e2, inv, e3) ->
      inv = [] && no_vcs_in_expr e1 && no_vcs_in_expr e2 && no_vcs_in_expr e3
  | Eassert (Expr.(Assert|Check), _) -> false
  | Eassert (Expr.Assume, _) -> true
  | Escope (_, e) | Elabel (_, e) | Ecast (e, _) | Eghost e | Eattr (_, e) ->
      no_vcs_in_expr e

(* The conversion from Gnat_ast to Ptree is parameterized in ['a]/[t] by the targeted type
   ([Ptree.expr] or [Ptree.term]) and the corresponding smart constructors from
   [PtreeConstructors]. Nodes that are converted to different syntaxes in expressions and
   terms ar differentiated using [E_or_T.expr_or_term]. Nodes that cannot be converted to
   the target type raise an exception [Failure] (but that should only happen when there is
   a problem in the generated [Gnat_ast]). *)

let process_call : 'a . (module E_or_T with type t = 'a) -> 'b why_node_id -> identifier_id -> 'a list  -> 'a =
  fun (type t) (module E_or_T : E_or_T with type t = t) (node : 'b why_node_id) id args : t ->
  (* Convert unquantified op1 operations (=, <, etc.) to innfix, binary only *)
  let open E_or_T in
  if is_infix_identifier id && is_op1 id then begin
    let op =
      List.get_last (conversion_error node.info.id "empty operator name")
        (mk_idents_of_identifier ~notation:(Some Ident.op_infix) [] id) in
    match args with
    | [arg0;arg1] -> mk_innfix arg0 op arg1
    | _ -> conversion_error node.info.id "op1 operations must be binary" ()
  end
  (* Convert unqualified op234 prefix operations (/, *, !, etc.) *)
  else if is_infix_identifier id && is_op234 id then begin
    match args with
    | [_] ->
      let qid =
        let ident =
          List.get_last (conversion_error node.info.id "empty operator name")
            (mk_idents_of_identifier ~notation:(Some Ident.op_prefix) [] id) in
        mk_qualid [ident] in
      mk_idapp qid args
    | [_;_] ->
    let qid =
      let ident =
        List.get_last (conversion_error node.info.id "empty operator name")
          (mk_idents_of_identifier ~notation:(Some Ident.op_infix) [] id) in
      mk_qualid [ident] in
      mk_idapp qid args
    | _ ->
        conversion_error node.info.id "operations with op234 operators must be unary or binary" ()
  end else (begin
    if is_infix_identifier id then
      Format.ksprintf (conversion_error node.info.id) "infix identifier %s must be op1 or op234"
        (String.concat "." (strings_of_name (name_of_identifier id))) ();
    let notation =
      if is_op1 id || is_op234 id then
        match List.length args with
        | 1 -> Some Ident.op_prefix
        | 2 -> Some Ident.op_infix
        | _ -> conversion_error node.info.id "operations with op234 operators must be unary or binary" ()
      else None in
      let f = mk_var (mk_qualid (mk_idents_of_identifier ~notation [] id)) in
      List.fold_left (mk_apply ?loc:None) f args
  end)

let rec mk_of_expr : 'a . (module E_or_T with type t = 'a) -> expr_id -> 'a =
  (* Signature type ^^^^^ variable ['a] required to make [mk_of_expr] strongly polymorphic *)
  fun (type t) (module E_or_T : E_or_T with type t = t) (node: expr_id) : t ->
  let open E_or_T in
  let mk_of_expr (node : expr_id) = (* Shortcut for direct recursive call *)
    mk_of_expr (module E_or_T: E_or_T with type t = t) node in
  let expr_only expr = (* Shortcut for nodes that can only translated to a expression *)
    expr_or_term ~expr:(fun () -> expr) () in
  let term_only term = (* Shortcut for nodes that can only translated to a expression *)
    expr_or_term ~term:(fun () -> term) () in
  let mk_field_association (node: field_association_id) =
    let Field_association r = node.desc in
    mk_qualid (mk_idents_of_name ~notation:None [] (name_of_identifier r.field)),
    mk_of_expr r.value in
  let mk_binder_of_identifier attrs pty node =
    let id =
      let err = conversion_error node.info.id "qualified or empty identifier" in
      force_one err (mk_idents_of_identifier ~notation:None attrs node) in
    get_pos (), Some id, false, Some pty in
  let mk_identifier_labels (node : identifier_id) =
    let Identifier r = node.desc in
    List.filter_map mk_label r.labels in
  let mk_seqs l =
    let not_unit = function
      | {expr_desc = Etuple []} -> false
      | _ -> true in
    let statements = List.filter not_unit l in
    let firsts, last =
      match List.rev statements with
      | [] -> [], E.mk_tuple []
      | last :: firsts -> List.rev firsts, last in
    List.fold_right (E.mk_seq ?loc:None) firsts last in
  let mk_comment s e =
    match mk_comment_attr s with
    | None -> e
    | Some a -> E.mk_attr a e in
  let mk_const_of_ureal id (Ureal r) =
    (* gnat/ureal.ads *)
    if r.base = 0 then
      let Uint numerator = r.numerator in
      let mk_const r = mk_const (Constant.ConstReal r) in
      if BigInt.(eq one (bigint_of_uint r.denominator)) then
        mk_const
          (Number.real_literal ~radix:10 ~neg:r.negative ~int:numerator ~frac:"0" ~exp:None)
      else
        conversion_error id "ureal with base = 0 and denominator /= 1" ()
        (* (\* Which operator /. for reals? *\)
          * let Uint denominator = r.denominator in
          * mk_idapp
          *   (mk_qualid [mk_ident [] (Ident.op_infix "/.")])
          *   (List.map mk_const
          *      [Number.real_literal ~radix:10 ~neg:r.negative ~int:numerator ~frac:"0" ~exp:None;
          *       Number.real_literal ~radix:10 ~neg:false ~int:denominator ~frac:"0" ~exp:None]) *)
    else
      let int =
        let int = bigint_of_uint r.numerator in
        if r.negative then BigInt.minus int else int in
      let exp = BigInt.(minus (bigint_of_uint r.denominator)) in
      match r.base with
      | 2 ->
          mk_const (Constant.real_const ~pow2:exp ~pow5:BigInt.zero int)
      | 10 ->
          mk_const (Constant.real_const ~pow2:exp ~pow5:exp int)
      | 16 ->
          let pow2 = BigInt.mul_int 4 exp in
          mk_const (Constant.real_const ~pow2 ~pow5:BigInt.zero int)
      | _ ->
          conversion_error id ("unsupported base "^string_of_int r.base^" for ureal") () in

  let curr_attrs = Curr.mk_attrs () in

  let res = match node.desc with

    (* Preds, Expr *)

    | Universal_quantif r ->
        term_only
          (let for_trigger (node : trigger_id) =
             let Trigger r = node.desc in
             List.map mk_term_of_expr (list_of_nonempty r.terms) in
           let for_triggers (node : triggers_id) =
             let Triggers r = node.desc in
             List.map for_trigger (list_of_nonempty r.triggers) in
           let curr_attrs = Curr.mk_attrs () in
           let binders =
             List.map (mk_binder_of_identifier (curr_attrs @ List.filter_map mk_label r.labels) (mk_pty_of_type r.var_type))
               (list_of_nonempty r.variables) in
           let triggers = Opt.(get [] (map for_triggers r.triggers)) in
           let body = mk_term_of_pred r.pred  in
           T.mk_quant Dterm.DTforall binders triggers body)

    | Existential_quantif r ->
        term_only
          (let binders =
             List.map
               (mk_binder_of_identifier (List.filter_map mk_label r.labels)
                  (mk_pty_of_type r.var_type))
               (list_of_nonempty r.variables) in
           let body = mk_term_of_pred r.pred in
           T.mk_quant Dterm.DTexists binders [] body)

    (* Preds, Progs, Expr *)

    | Not r ->
        mk_not (mk_of_expr r.right)

    | Connection r ->
        let module M = struct
          type 'a tree = Node of 'a | Binop of 'a tree * 'a tree
          let rec map node binop = function
            | Node x -> node x
            | Binop (t1, t2) ->
                let x1 = map node binop t1 in
                let x2 = map node binop t2 in
                binop x1 x2
          let mk_tree = function
            | [] -> None
            | exprs ->
                let a = Array.of_list exprs in
                let rec aux from to_ =
                  assert (to_ - from > 0);
                  if to_ - from = 1 then
                    Node a.(from)
                  else
                    let mid = (from + to_ + 1) / 2 in
                    Binop (aux from mid, aux mid to_) in
                Some (aux 0 (Array.length a))
        end in
        expr_or_term
          ~expr:(fun () ->
              let op = expr_connector node.info.id r.op in
              let e1 =
                let left = mk_expr_of_expr r.left in
                let right = mk_expr_of_expr r.right in
                E.mk_binop left op right in
              Opt.(get e1
                     (map (E.mk_binop e1 op)
                        (map (M.map mk_expr_of_expr (fun e -> E.mk_binop e op))
                           (M.mk_tree r.more_right)))))
          ~term:(fun () ->
              let op = term_connector r.op in
              let t1 =
                let left = mk_term_of_expr r.left in
                let right = mk_term_of_expr r.right in
                T.mk_binnop left op right in
              Opt.(get t1
                     (map (T.mk_binnop t1 op)
                        (map (M.map mk_term_of_expr (fun t -> T.mk_binnop t op))
                           (M.mk_tree r.more_right))))) ()

    | Label r ->
        let labels = List.filter_map mk_label r.labels in
        let body = mk_of_expr r.def in
        mk_attrs labels body

    | Loc_label r ->
        Curr.with_ (r.sloc, r.marker)
          (fun () ->
             let curr_attrs = Curr.mk_attrs () in
             let body = mk_of_expr r.def in
             mk_attrs curr_attrs body)

    (* Preds, Terms, Progs, Expr *)

    (* FIXGNAT sometimes the symbol contains a function application, e.g. "uint_in_range x" [sic!] *)
    | Identifier ({name={desc=Name ({symb=Symbol s} as name_r)} as name} as ident_r)
      when String.index_opt s ' ' <> None -> begin
        match String.split_on_char ' ' s with
        | s' :: args ->
            let node' = {
              node with desc = Identifier {
                ident_r with name = {name with desc=Name {
                name_r with symb = Symbol s'}}}} in
            let f = mk_var (mk_qualid (mk_idents_of_identifier ~notation:None [] node')) in
            let args = List.(map (mk_var ?loc:None) (map mk_qualid (map (fun s -> [mk_ident [] s]) args))) in
            List.fold_left (mk_apply ?loc:None) f args
        | _ -> assert false
      end

    | Identifier {name={desc=Name {symb=Symbol "absurd"}}} ->
        expr_only
          E.(mk_absurd ())

    | Identifier {name={desc=Name {symb=Symbol "()"}}} ->
        mk_tuple []

    | Identifier r ->
        mk_var (mk_qualid (mk_idents_of_name ~notation:None [] r.name))

    | Tagged ({tag=No_symbol} as r) ->
        term_only
          (mk_term_of_expr r.def)

    | Tagged ({tag=Symbol s} as r) ->
        term_only
          (let body = mk_term_of_expr r.def in
           let id =
             let s = if s = "old" then "'Old" else s in
             mk_ident [] s in
           T.mk_at body id)

    | Call r ->
        let args = List.map mk_of_expr r.args in
        process_call (module E_or_T: E_or_T with type t = t) node r.name args

    | Literal r ->
        if node.info.domain = Pred then
          mk_truth (match r.value with True -> true | False -> false)
        else
          mk_var (mk_qualid [mk_ident [] (match r.value with True -> "True" | False -> "False")])

    | Binding r ->
        let id =
          force_one (conversion_error r.name.info.id "qualified or empty identifier")
            (mk_idents_of_identifier ~notation:None
               (mk_identifier_labels r.name) r.name) in
        let def = mk_of_expr r.def in
        let body = mk_of_expr r.context in
        mk_let id def body

    | Elsif _ ->
        conversion_error node.info.id "unexpected elsif" ()

    | Epsilon r ->
        term_only
          (let id =
             force_one (conversion_error r.name.info.id "qualified or empty idenfitier")
               (mk_idents_of_identifier ~notation:None [] r.name) in
           let pty = mk_pty_of_type r.typ in
           let body = mk_term_of_pred r.pred in
           T.mk_eps id pty body)

    | Conditional r ->
        let rec mk_elsifs = function
          | [] ->
              let open Opt in
              get (expr_or_term
                     ~expr:(fun () -> E.mk_tuple [])
                     ~term:(fun () -> T.mk_truth true) ())
                (map mk_of_expr r.else_part)
          | {desc=Elsif r'} :: elsifs ->
              let condition' = mk_of_expr r'.condition in
              let then_part' = mk_of_expr r'.then_part in
              let elsif_parts' = mk_elsifs elsifs in
              mk_if condition' then_part' elsif_parts'
          | _ ->
              conversion_error node.info.id "unexpected elsif" ()
        in
        let condition = mk_of_expr r.condition in
        let then_part = mk_of_expr r.then_part in
        let elsif_parts = mk_elsifs r.elsif_parts in
        mk_if condition then_part elsif_parts

    (* Terms, Progs, Exprs *)

    | Integer_constant r ->
        let const = mk_const (Constant.int_const (bigint_of_uint r.value)) in
        let pty = Ty.mk_atomic_type ["int"] in
        mk_cast const pty

    | Range_constant r ->
        let const = mk_const (Constant.int_const (bigint_of_uint r.value)) in
        let pty = mk_pty_of_type r.typ in
        mk_cast const pty

    | Modular_constant r ->
        let const = mk_const (Constant.int_const (bigint_of_uint r.value)) in
        let pty =
          let Type r = r.typ.desc in
          match unroll_name r.name with
          | Some (Some "_gnatprove_standard", Some (("BV8"|"BV16"|"BV32"|"BV64"|"BV128" as s))), Some "t" ->
              Ty.mk_atomic_type [s; "t"]
          | _ ->
              conversion_error node.info.id "unknown module constant" () in
        mk_cast const pty

    | Fixed_constant r ->
        let const = mk_const (Constant.int_const (bigint_of_uint r.value)) in
        let pty = Ty.mk_atomic_type ["int"] in
        mk_cast const pty

    | Real_constant r ->
        mk_const_of_ureal node.info.id r.value

    | Float_constant r ->
        let prefix =
          let Type r = r.typ.desc in
          match unroll_name r.name with
          | Some (Some "_gnatprove_standard", Some ("Float32"|"Float64" as s)), Some "t" ->
              mk_ident [] s
          | _ ->
              conversion_error node.info.id "float_constant must be Float32.t or Float64.t" ()
        in
        let const =
          let Ureal r' = r.value in
          if r'.negative then
            (* negate the casted negation [neg (-r : t)]] *)
            mk_apply (mk_var (mk_qualid [prefix; mk_ident [] "neg"]))
              (mk_cast
                 (mk_const_of_ureal node.info.id (Ureal {r' with negative=false}))
                 (Ty.mk_idapp (mk_qualid [prefix; mk_ident [] "t"]) []))
          else
            mk_const_of_ureal node.info.id r.value in
        let pty = Ty.mk_idapp (mk_qualid [prefix; mk_ident [] "t"]) [] in
        mk_cast const pty

    | Comment r ->
        (* Using [()] won't play well in terms *)
        expr_only
          (let body = E.mk_tuple [] in
           mk_comment r.comment body)

    | Deref r ->
        let qid = mk_qualid (List.map_last (ident_add_suffix "__content") (mk_idents_of_type r.typ)) in
        let arg = mk_var (mk_qualid (mk_idents_of_identifier ~notation:None [] r.right)) in
        mk_idapp qid [arg]

    | Record_access r ->
        let qid = mk_qualid (mk_idents_of_identifier ~notation:None [] r.field) in
        let arg = mk_of_expr r.name in
        mk_idapp qid [arg]

    | Record_update r ->
        let record = mk_of_expr r.name in
        let assocs = List.map mk_field_association (list_of_nonempty r.updates) in
        mk_update record assocs


    | Record_aggregate r ->
        let assocs = List.map mk_field_association (list_of_nonempty r.associations) in
        mk_record assocs

    (* Progs, Expr *)

    | Any_expr r ->
        expr_only
          (let open E in
           let id = mk_ident [] "_f" in
           let value =
             let pty = mk_pty_of_type r.return_type in
             let spec =
               let open Opt in
               let pre =
                 let curr_attrs = Curr.mk_attrs () in
                 to_list
                   (map requires
                      (map (T.mk_attrs (List.filter_map mk_label r.labels @ curr_attrs))
                         (map mk_term_of_pred r.pre))) in
               let post =
                 let curr_attrs = Curr.mk_attrs () in
                 to_list
                   (map (ensures ?loc:None)
                      (map (T.mk_attrs curr_attrs)
                         (map mk_term_of_pred r.post))) in
               let reads, writes, xpost = Opt.(get ([], [], []) (map mk_effects r.effects)) in
               mk_spec ~pre ~post ~reads ~writes ~xpost () in
             mk_any [] Expr.RKnone (Some pty) P.(mk_wild ()) Ity.MaskVisible spec in
           let body = mk_var (Qident id) in
           mk_let id value body)

    | Assignment r ->
        expr_only
          (let open E in
           let left = mk_attrs (List.filter_map mk_label r.labels)
               (mk_var (mk_qualid (mk_idents_of_identifier ~notation:None [] r.name))) in
           let field = mk_qualid (List.map_last (ident_add_suffix "__content") (mk_idents_of_type r.typ)) in
           let value = mk_expr_of_prog r.value in
           mk_assign left (Some field) value)

    | Binding_ref r ->
        expr_only
          (let open E in
           let id =
             force_one (conversion_error r.name.info.id "quantified or empty name")
               (mk_idents_of_identifier ~notation:None (mk_identifier_labels r.name) r.name) in
           let ref =
             let field =
               let typ =
                 Opt.force (conversion_error r.name.info.id "missing type")
                   (let Identifier r = r.name.desc in r.typ) in
               mk_qualid
                 (List.map_last (ident_add_suffix "__content")
                    (mk_idents_of_type typ)) in
             let value = mk_expr_of_prog r.def in
             mk_record [field, value] in
           let body = mk_expr_of_prog r.context in
           mk_let id ref body)

    | Loop r ->
        (* Loops in the GNAT AST are of the form
            loop
              code before invariants
              invariants/variants
              code after invariants
            end

            We transform these loops into Why3 loops of the form
            code before
            while True loop
              invariant
              compute old values for variants
              code after
              code before
              compute new values for variants, compare with old values
            end

        *)
        expr_only
          (let true_expr = E.mk_var (mk_qualid [(mk_ident [] "True")]) in
           let false_pred = T.mk_var (mk_qualid [mk_ident [] "False"]) in
           let invariants = List.(map (T.name_term "LoopInvariant") (map mk_term_of_pred r.invariants)) in
           let mk_variant_ident (v : variant_id) =
             (* creating a unique tmp var for this loop variant, by using the node id *)
              mk_ident [] ("loop_var___" ^ string_of_int v.info.id) in
           let check_variant (v : variant_id) acc =
             (* checking a single variant; we compare the old value (stored in
                the tmp var) to the new value computed by the term. The
                comparison operator is provided in the tree.
                The accumulator contains the check coditions if this variant
                doesn't progress (stays the same). *)
              let Variant r = v.desc in
              let new_ = mk_term_of_term r.expr in
              let old = T.mk_var (mk_qualid [mk_variant_ident v]) in
              let expr = process_call (module T) v r.cmp_op [new_;old] in
              let eq = mk_ident [] (Ident.op_infix "=") in
              T.mk_attrs (List.filter_map mk_label r.labels)
                (T.mk_binop
                  expr
                  `Or_asym
                  (T.mk_binop (T.mk_infix new_ eq old) `And_asym acc)) in
           (* checking all variants of a given Variants node is just a fold
              which starts at the end, starting with the false condition. *)
           let check_variants (v : variants_id) =
              let Variants v = v.desc in
              let pred =
                List.fold_right check_variant (v.variants.elt0 :: v.variants.elts)
                  false_pred in
              E.mk_assert Expr.Assert pred in
           (* Each Variants node is checked indepently of the others, so here
              we just map over the list of Variants nodes.
            *)
           let check_variants =
             List.fold_right (E.mk_seq ?loc:None)
                (List.map check_variants r.variants)
                (E.mk_tuple []) in
           (* we introduce the temp vars to hold the old values of the variant
              nodes. We can do this in a single fold (no need to group by
              Variants). *)
           let intro_vars =
             List.fold_right (fun (v : variants_id) acc ->
                let Variants vs = v.desc in
                List.fold_right (fun v acc ->
                  let Variant r = v.desc in
                  let value = mk_expr_of_term r.expr in
                  E.mk_let (mk_variant_ident v) value acc)
                  (vs.variants.elt0 :: vs.variants.elts) acc) r.variants in
           let code_after = mk_expr_of_prog r.code_after in
           let code_before = mk_expr_of_prog r.code_before in
           let loop_body =
              mk_seqs
                [mk_comment
                  (Symbol "gnat_ast_to_ptree: code after the loop invariant")
                   code_after;
                 mk_comment (Symbol "gnat_ast_to_ptree: code before the loop invariant")
                   code_before;
                 mk_comment (Symbol "gnat_ast_to_ptree: code checking the variants")
                   check_variants
                ] in
           let loop_body = intro_vars loop_body in
           let loop = E.mk_while true_expr invariants [] loop_body in
           E.mk_seq code_before loop)

    | Statement_sequence r ->
        expr_only
          (let rec flatten_seq (node: prog_id) =
               match node.desc with
               | Statement_sequence r ->
                   flatten_seqs r.statements
               | _ -> [node]
             and flatten_seqs (nodes: prog_list) =
               List.(concat (map flatten_seq (list_of_nonempty nodes))) in
             mk_seqs (List.map mk_expr_of_prog (flatten_seqs r.statements)))

    | Abstract_expr r ->
        (* begin ensures { <r.post> } let _ = <r.expr> in () end *)
        expr_only
          E.(let post = mk_term_of_pred r.post in
             let expr = mk_expr_of_prog r.expr in
             if is_true post && no_vcs_in_expr expr then
               mk_tuple []
             else
               let pat = P.mk_wild () in
               let spec =
                 let post = [ensures post] in
                 mk_spec ~post () in
               let body =
                 let id = mk_ident [] "_" in
                 let body = mk_tuple [] in
                 mk_let id expr body in
               mk_fun [] None pat Ity.MaskVisible spec body)

    | Assert r ->
        expr_only
          (let assert_kind, str =
             match r.assert_kind with
             | Assert -> Expr.Assert, "Assert"
             | Check -> Expr.Check, "Check"
             | Assume -> Expr.Assume, "Assume" in
           let body =
             let curr_attrs = Curr.mk_attrs () in
             T.(name_term str (mk_attrs curr_attrs (mk_term_of_pred r.pred))) in
           E.(mk_assert assert_kind body))

    | Raise r ->
        expr_only
          (let e = E.mk_raise (mk_qualid (mk_idents_of_name ~notation:None [] r.name)) None in
           match r.typ with
           | None -> e
           | Some typ ->
               let pty = mk_pty_of_type typ in
               E.mk_cast e pty)

    | Try_block r ->
        expr_only
          (let expr = mk_expr_of_prog r.prog in
           let exn_handlers =
             let aux (node: handler_id) =
               let Handler r = node.desc in
               mk_qualid (mk_idents_of_name ~notation:None [] r.name),
               Opt.map mk_pattern_of_prog r.arg,
               mk_expr_of_prog r.def in
             List.map aux (list_of_nonempty r.handler) in
           E.mk_match expr [] exn_handlers)
  in

  let res =
    match node.desc with
    | Raise _ | Loop _ | Abstract_expr _ | Any_expr _ | Assert _ | Assignment _ | Binding_ref _ | Try_block _ ->
        mk_attrs curr_attrs res
    | _ -> res in
  res

(* Instantiate [MkOfExpr] for terms and expressions and tie the knot with the other specialized functions *)

and mk_expr_of_expr (node : expr_id) : expr =
  mk_of_expr (module E) node

and mk_term_of_expr (node : expr_id) : term =
  mk_of_expr (module T) node

and mk_expr_of_term (node : term_id) : expr =
  match node.desc with
 | Label _ | Loc_label _ | Identifier _ | Tagged _ | Call _ | Literal _
 | Binding _ | Elsif _ | Epsilon _ | Conditional _ | Integer_constant _
 | Range_constant _ | Modular_constant _ | Fixed_constant _ | Real_constant _
 | Float_constant _ | Comment _ | Deref _ | Record_access _
 | Record_update _ | Record_aggregate _ as desc ->
      mk_expr_of_expr {node with desc}

and mk_expr_of_prog (node : prog_id) =
  match node.desc with
  | Not _ | Connection _ | Label _ | Loc_label _ | Identifier _ | Tagged _ | Call _
  | Literal _ | Binding _ | Elsif _ | Epsilon _ | Conditional _ | Integer_constant _
  | Range_constant _ | Modular_constant _ | Fixed_constant _ | Real_constant _
  | Float_constant _ | Comment _ | Deref _ | Record_access _ | Record_update _
  | Record_aggregate _ | Any_expr _ | Assignment _ | Binding_ref _ | Loop _
  | Statement_sequence _ | Abstract_expr _ | Assert _ | Raise _ | Try_block _ as desc ->
      mk_expr_of_expr {node with desc}

and mk_term_of_pred (node : pred_id) : term =
  match node.desc with
  | Universal_quantif _ | Existential_quantif _ | Not _ | Connection _
  | Label _ | Loc_label _ | Identifier _ | Tagged _ | Call _ | Literal _
  | Binding _ | Elsif _ | Epsilon _ | Conditional _ as desc ->
      mk_term_of_expr {node with desc}

and mk_term_of_term (node : term_id) : term =
  match node.desc with
 | Label _ | Loc_label _ | Identifier _ | Tagged _ | Call _ | Literal _
 | Binding _ | Elsif _ | Epsilon _ | Conditional _ | Integer_constant _
 | Range_constant  _ | Modular_constant _ | Fixed_constant _
 | Real_constant _ | Float_constant _ | Comment _ | Deref _
 | Record_access _ | Record_update _ | Record_aggregate _  as desc ->
  mk_term_of_expr {node with desc}


let mk_function_decl (node: function_decl_id) =
  let Function_decl r = node.desc in
  let ident =
    force_one
      (conversion_error r.name.info.id "quantified or empty function name")
      (mk_idents_of_identifier ~notation:None
         (Opt.(to_list (map mk_pos (mk_location r.location))) @
          List.filter_map mk_label r.labels)
         r.name) in
  let res_pty =
    Opt.map mk_pty_of_type r.return_type in
  let params =
    let aux (node: binder_id) : param =
      let Binder r = node.desc in
      get_pos (),
      Opt.(map (force_one (conversion_error node.info.id "qualified or empty parameter name"))
             (map (mk_idents_of_identifier ~notation:None [])
                r.name)),
      false,
      mk_pty_of_type r.arg_type in
    List.map aux r.binders in
  let binders =
    let aux (loc, id, gh, pty) : binder =
      loc, id, gh, Some pty in
    List.map aux params in
  let decl = {
    ld_ident = ident; ld_params = params; ld_type = res_pty;
    ld_loc = get_pos (); ld_def = None;
  } in
  match node.info.domain with
  | Term ->
      (* function <id> <params> : <res_ty> <*)
      [D.mk_logic [{decl with ld_def = Opt.map mk_term_of_expr r.def}]]
  | Pterm ->
      if params = [] then
        (* val constant <id> : <res_ty> [ensures {result = <def>}] *)
        let mk_post def =
          ensures
            T.(let left = mk_var (Qident result_ident) in
               let op = mk_ident [] (Ident.op_infix "=") in
               let right =
                 let curr_attrs = Curr.mk_attrs () in
                 mk_attrs curr_attrs (mk_term_of_expr def) in
               mk_infix left op right) in
        let value =
          let pat = P.mk_wild () in
          let spec = mk_spec ~post:Opt.(to_list (map mk_post r.def)) () in
          E.mk_any [] Expr.RKnone res_pty pat Ity.MaskVisible spec in
        [D.mk_let ident false Expr.RKfunc value]
      else if r.def = None then
        (* val function <id> <params> : <res_ty> *)
        let value =
          let pat = P.mk_wild () in
          let spec = mk_spec () in
          E.mk_any params Expr.RKnone res_pty pat Ity.MaskVisible spec in
        [D.mk_let ident false Expr.RKfunc value]
      else
        (* function <id> <params> : <res_ty> = <def>
           val <id> <params> : <res_typ> ensures { result = <id> <params> }*)
        let arg_for_param (_, id, _, pty) =
          T.(mk_cast (mk_var (Qident (Opt.get (mk_ident [] "???") id))) pty) in
        let logic_decl =
          D.mk_logic [{decl with ld_def=Opt.map mk_term_of_expr r.def}] in
        let let_decl =
          let value =
            let pat = P.mk_wild () in
            let spec =
              let post =
                [ensures (* result = <id> <params> *)
                   T.(let left = mk_var (Qident result_ident) in
                      let op = mk_ident [] (Ident.op_infix "=") in
                      let right =
                        let p = mk_var (Qident ident) in
                        let args = List.map arg_for_param params in
                        List.fold_left (mk_apply ?loc:None) p args in
                      mk_infix left op right)] in
              mk_spec ~post () in
            E.mk_any params Expr.RKnone res_pty pat Ity.MaskVisible spec in
          D.mk_let ident false Expr.RKnone value in
        [logic_decl; let_decl]
  | Prog ->
      Curr.with_ (r.location, No_symbol)
        (fun () ->
           let spec =
             let pre = let open Opt in
               let curr_attrs = Curr.mk_attrs () in
               to_list
                 (map requires
                    (map (T.mk_attrs curr_attrs)
                       (map mk_term_of_pred r.pre))) in
             let post = let open Opt in
               let curr_attrs = Curr.mk_attrs () in
               to_list
                 (map (ensures ?loc:None)
                    (map (T.mk_attrs curr_attrs)
                       (map mk_term_of_pred r.post))) in
             let reads, writes, xpost = Opt.(get ([], [], []) (map mk_effects r.effects)) in
             (mk_spec ~pre ~post ~reads ~writes ~xpost ()) in
           let expr =
             match r.def with
             | None ->
                 (* val <id> <params> : <res_ty> <spec> *)
                 let pat = P.mk_wild () in
                 E.mk_any params Expr.RKnone res_pty pat Ity.MaskVisible spec
             | Some def ->
                 (* let <id> <params> : <res_ty> <spec> = [@vc:divergent] <def> *)
                 let pat = P.mk_wild () in
                 let body =
                   let attr = mk_str "vc:divergent" in
                   let body = mk_expr_of_expr def in
                   E.mk_attr attr body in
                 E.mk_fun binders res_pty pat Ity.MaskVisible spec body
           in
           [D.mk_let ident false Expr.RKnone expr])
  | Pred ->
      let opt_def = Opt.map mk_term_of_expr r.def in
      begin match opt_def with
        | None ->
            (* val predicate <id> <params> *)
            let any = E.mk_any params Expr.RKnone None (P.mk_wild ()) Ity.MaskVisible (mk_spec ()) in
            [D.mk_let ident false Expr.RKpred any]
        | Some def ->
            let mk_arg_of_param node (_, id_opt, _, pty) =
              match id_opt with
              | Some id -> T.(mk_cast (mk_var (Qident id)) pty)
              | None -> conversion_error node.info.id "missing parameter name" () in
            let predicate_def =
              (* predicate <id> <params> = <def> *)
              let def =
                Opt.(get def
                       (map (fun pos -> T.mk_attr pos def)
                          (map mk_pos (mk_location r.location)))) in
              D.mk_logic [{decl with ld_type=None; ld_def=Some def}] in
            let val_def =
              (* val <id> <params> : bool ensures { result = <id> <params> }*)
              let value =
                let pat = P.mk_wild () in
                let pty = Ty.mk_atomic_type ["bool"] in
                let spec =
                  let post = [
                    ensures
                      T.(let left = mk_term (Tident (Qident result_ident)) in
                         let right =
                           let p = mk_var (Qident ident) in
                           let args = List.map2 mk_arg_of_param r.binders params in
                           List.fold_left (mk_apply ?loc:None) p args in
                         mk_binop left `Iff right)
                  ] in
                  mk_spec ~post () in
                E.mk_any params Expr.RKnone (Some pty) pat Ity.MaskVisible spec in
              D.mk_let ident false Expr.RKnone value in
            [predicate_def; val_def]
      end

let mk_record_binder (node : record_binder_id) =
  let Record_binder r = node.desc in
  let ident =
    let name = Opt.force (conversion_error node.info.id "missing name") r.name in
    let idents = mk_idents_of_identifier ~notation:None (List.filter_map mk_label r.labels) name in
    force_one (conversion_error node.info.id "quantified or empty name") idents in
  let pty = mk_pty_of_type r.arg_type in
  {f_ident = ident; f_pty = pty; f_mutable = r.is_mutable;
   f_ghost = false; f_loc = get_pos ()}

let rec mk_declaration (node : declaration_id) =
  match node.desc with
  | Type_decl r ->
      let ident =
        force_one (conversion_error node.info.id "quantified or empty name")
          (mk_idents_of_name ~notation:None (List.filter_map mk_label r.labels) r.name) in
      let args =
        let aux node ids =
          force_one (conversion_error node.info.id "quantified or empty argument name") ids in
        List.(map2 aux r.args (map (mk_idents_of_identifier ~notation:None []) r.args)) in
      let def, vis =
        match r.definition with
        | None ->
            TDrecord [], Ptree.Abstract (* empty type definition *)
        | Some definition ->
            let def =
              match definition.desc with
              | Transparent_type_definition r ->
                  TDalias (mk_pty_of_type r.type_definition)
              | Record_definition r ->
                  TDrecord
                    (List.map mk_record_binder
                       (list_of_nonempty r.fields))
              | Range_type_definition r ->
                  TDrange (bigint_of_uint r.first, bigint_of_uint r.last)
              | Record_binder _ -> (* This should not be here *)
                  conversion_error definition.info.id "record binder in type definition" () in
            def, Ptree.Public in
      [D.mk_type [{
           td_ident = ident; td_params = args; td_def = def; td_mut = false;
           td_loc = get_pos (); td_inv = []; td_wit = []; td_vis = vis
         }]]
  | Function_decl _ as desc ->
      mk_function_decl {info=node.info; desc}
  | Global_ref_declaration r ->
      (* val <ident> : <ref_typ> *)
      let ident =
        let labels =
          Opt.(to_list (map mk_pos (mk_location r.location))) @
          List.filter_map mk_label r.labels in
        force_one (conversion_error r.name.info.id "quantified or empty name of global reference")
          (mk_idents_of_identifier ~notation:None labels r.name) in
      let pty =
        let qid = mk_qualid (List.map_last (ident_add_suffix "__ref")
                               (mk_idents_of_type r.ref_type)) in
        Ty.mk_idapp qid [] in
      let value =
        let pat = P.mk_wild () in
        let spec = mk_spec () in
        E.mk_any [] Expr.RKnone (Some pty) pat Ity.MaskVisible spec in
      [D.mk_let ident false Expr.RKnone value]
  | Meta_declaration r ->
      let name =
        Opt.force (conversion_error node.info.id "empty name symbol in meta declaration")
          (string_of_symbol r.name) in
      let parameter =
        Opt.force (conversion_error node.info.id "empty parameter symbol in meta declaration")
           (string_of_symbol r.parameter) in
      let id = mk_ident [] name in
      let metarg =
        match String.split_on_char ' ' parameter with
        | "function" :: strs -> Mfs (Qident (mk_ident [] (String.concat " " strs)))
        | _ -> conversion_error node.info.id
            ("meta declaration "^parameter^" not yet support (please report)") () in
      [D.mk_meta id [metarg]]
  | Clone_declaration r -> begin
      let mk_clone_substitution (node : clone_substitution_id) =
        let Clone_substitution r = node.desc in
        let qident1 =
          let notation =
            let Name r = r.orig_name.desc in
            if r.infix then Some Ident.op_infix else None in
          mk_qualid (mk_idents_of_name ~notation [] r.orig_name) in
        let qident2 =
          let notation =
            let Name r = r.image.desc in
            if r.infix then Some Ident.op_infix else None in
          mk_qualid (mk_idents_of_name ~notation [] r.image) in
        match r.kind with
        | Type_subst ->
            CStsym (qident1, [], PTtyapp (qident2, []))
        | Function ->
            CSfsym (qident1, qident2)
        | Predicate ->
            CSpsym (qident1, qident2)
        | Namepace | Lemma | Goal ->
            failwith "Not implemented: mk_declaration Clone_declaration" in
      match r.clone_kind with
      | Export ->
          if r.as_name <> No_symbol then
            failwith "mk_declaration: clone export as";
          let qid = mk_module_qident r.origin in
          let substs =
            CSprop Decl.Paxiom (* axiom . *) ::
            List.map mk_clone_substitution r.substitutions in
          [D.mk_cloneexport qid substs]
      | Import | Clone_default ->
          let qid = mk_module_qident r.origin in
          let as_name =
            if r.as_name <> No_symbol
            then Some (mk_ident_of_symbol node.info.id ~notation:None [] r.as_name)
            else None in
          let substs =
            CSprop Decl.Paxiom (* axiom . *) ::
            List.map mk_clone_substitution r.substitutions in
          [D.mk_cloneimport true qid as_name substs]
    end
  | Include_declaration _ as desc ->
      [mk_include_declaration {node with desc}]
  | Axiom r ->
      let id = mk_ident_of_symbol node.info.id ~notation:None [mk_str "useraxiom"] r.name in
      let body = mk_term_of_pred r.def in
      [D.mk_prop Decl.Paxiom id body]
  | Goal r ->
      let id = mk_ident_of_symbol node.info.id ~notation:None [] r.name in
      let body = mk_term_of_pred r.def in
      [D.mk_prop Decl.Pgoal id body]
  | Namespace_declaration r ->
      let id = mk_ident_of_symbol node.info.id ~notation:None [] r.name in
      let decls = List.concat (List.map mk_declaration r.declarations) in
      [D.mk_scope false id decls]
  | Exception_declaration r ->
      let id =
        force_one (conversion_error node.info.id "quantified or empty name in exception declaration")
          (mk_idents_of_name ~notation:None [] r.name) in
      let pty = Opt.(get (Ty.mk_tuple []) (map mk_pty_of_type r.arg)) in
      [D.mk_exn id pty Ity.MaskVisible]

let read_mlw_file filename =
  let ic = open_in filename in
  let buf = Lexing.from_channel ic in
  let res = Lexer.parse_mlw_file buf in
  close_in ic;
  res

let locate_file_name file_name =
  let open Filename in
  let concats = List.fold_left concat in
  let from_share =
    let base = (* $(dirname $0)/../../.. *)
      concats (dirname Sys.executable_name)
        [parent_dir_name; parent_dir_name; parent_dir_name] in
    concats base ["share"; "spark"; "theories"; file_name] in
  let from_proof_dir =
    let proof_dir = (* TODO Use Gnat_config.proof_dir instead *)
      let rec search = function
        | [] -> None
        | "--proof-dir" :: s :: _ -> Some s
        | _ :: ss -> search ss in
      search (Array.to_list Sys.argv) in
    Opt.map (fun d -> concats d ["_theories"; file_name]) proof_dir in
  if Sys.file_exists from_share then
    from_share
  else match from_proof_dir with
    | Some dir when Sys.file_exists dir -> dir
    | _ ->
        Format.ksprintf failwith "locate_file_name: cannot read theory full_name %S"
          file_name

let mk_custom_declaration (node: custom_declaration_id) =
  let Custom_declaration r = node.desc in
  let file_name =
    match r.file_name with
    | Symbol s -> s
    | No_symbol -> "" in
  let file_name = locate_file_name file_name in
  match read_mlw_file file_name with
  | Modules modules -> modules
  | Decls _ ->
      Format.ksprintf invalid_arg
        "mk_generic_theory: %s contains decls not modules" file_name

let mk_generic_theory (node : generic_theory_id) =
  match node.desc with
  | Theory_declaration r ->
      (* Ignore [r.kind], because theory and module is the same *)
      let name =
        let curr_attrs = Opt.to_list (mk_comment_attr r.comment) in
        mk_ident_of_symbol node.info.id ~notation:None curr_attrs r.name in
      let includes = List.map mk_include_declaration r.includes in
      let declarations = List.concat (List.map mk_declaration r.declarations) in
      [name, includes @ declarations]
  | Custom_substitution r ->
      Format.ksprintf invalid_arg "mk_generic_theory: custom substitution %s"
        (Opt.get "NO_SYMBOL" (string_of_symbol r.from))
  | Custom_declaration _ as desc ->
      mk_custom_declaration {node with desc=desc}

let mlw_file nodes =
  Modules (List.concat (List.map mk_generic_theory nodes))

(** {1 JSON auxiliaries} *)

(** Pretty-print a JSON path *)
let pp_path fmt =
  let open Format in
  let pp_sep _ () = () in
  let pp fmt d = fprintf fmt "[%d]" d in
  fprintf fmt ".%a" (pp_print_list ~pp_sep pp)

(** Recursively find the path to a JSON element *)
let find_path needle node =
  let exception Found of int list in
  let rec aux path node =
    if node == needle then
      raise (Found (List.rev path))
    else
      match node with
      | `Null | `String _ | `Int _ | `Bool _ -> ()
      | `List l -> List.iteri (fun i -> aux (i :: path)) l
      | _ -> Format.kasprintf failwith "find_path: %a" pp_path (List.rev path) in
  try
    aux [] node;
    raise Not_found
  with Found path ->
    path

(** {1 Registration of Gnat/JSON parser} *)

exception Unexpected_json of string * int list

(* The locations in the generated ptree are unique but useless because they do not
   correspond to any concrete syntax. In case of a typing error in the generated
   ptree, we instruct the mlw-printer to mark the corresponding node by [(*XXX*)],
   using [Mlw_printer.set_marker]. The exception [Located_by_marker (file, e)]
   is then reported to the user with a hint to the marker in the given file. *)

exception Located_by_marker of string * exn

let read_channel env path filename c =
  let json = Yojson.Safe.from_channel c in
  let gnat_file =
    let open Gnat_ast in
    try From_json.file_from_json json
    with From_json.Unexpected_Json (s, node) ->
      raise (Unexpected_json (s, find_path node json)) in
  (* Debug printing of intermediate GNAT ast *)
  if Debug.test_flag debug then begin
      let out = open_out (filename^".gnat_ast") in
      Format.fprintf (Format.formatter_of_out_channel out) "%a@."
        Gnat_ast_pretty.pp_file gnat_file
  end;
  let mlw_file = mlw_file gnat_file.theory_declarations in
  (* Defer printing of mlw file until after the typing, to set the marker of located
     exceptions *)
  let print_mlw_file () =
    let out = open_out (filename^".mlw") in
    Format.fprintf (Format.formatter_of_out_channel out) "%a@."
      Mlw_printer.pp_mlw_file mlw_file;
    close_out out in
  match Typing.type_mlw_file env path filename mlw_file with
  | res ->
      if Debug.test_flag debug then
        print_mlw_file ();
      res
  | exception Loc.Located (pos, e) ->
      (* The positions in the generated ptree are useless - we set the marker for
         printing the mlw file and report that. *)
      Mlw_printer.set_marker pos;
      print_mlw_file ();
      raise (Located_by_marker (Filename.basename filename^".mlw", e))
  | exception e ->
      print_mlw_file ();
      raise e


let gnat_json_format = "gnat-json"

let () =
  Env.register_format ~desc:"Gnat@ AST@ in@ JSON@ format"
    Pmodule.mlw_language gnat_json_format ["gnat-json"] read_channel

let () =
  Exn_printer.register
    (fun fmt exn -> match exn with
       | Unexpected_json (s, path) ->
           (* Errors in the conversion from JSON to Gnat_ast are reported with their path,
              because the id is not guaranteed to be available. *)
           Format.fprintf fmt "Unexpected Json for %s at path %a@."
             s pp_path path
       | Conversion_error r ->
           (* Errors in the conversion from Gnat_ast to Why3 Ptree are reported with their
              id. *)
           Format.fprintf fmt "Conversion error for node with ID %d: %s" r.node_id r.message
       | Located_by_marker (filename, e) ->
           (* Located errors (i.e. typing errors) are reported with an hint on the marker, which
              is inserted into the mlw file by the mlw-printer. *)
           Format.fprintf fmt "File %s, marked by (*XXX*)(...):@\n%a"
             filename Exn_printer.exn_printer e
       | _ -> raise exn)
