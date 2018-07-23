(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Coq printer *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer

let black_list =
  [ "at"; "cofix"; "exists2"; "fix"; "IF"; "left"; "mod"; "Prop";
    "return"; "right"; "Set"; "Type"; "using"; "where"; ]

(* wrong: ' not allowed as first character in Coq identifiers
let char_to_alpha c =
  match c with
    | '\'' -> String.make 1 c
    | _ -> Ident.char_to_alpha c
*)

let char_to_alnumus c =
  match c with
    | '\'' -> String.make 1 c
    | _ -> Ident.char_to_alnumus c

let syntax_arguments s f fmt l =
  let sl = Strings.split ' ' s in
  pp_open_box fmt 1;
  print_list space (fun fmt s -> syntax_arguments s f fmt l) fmt sl;
  pp_close_box fmt ()

let fresh_printer () =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let iprinter = fresh_printer ()

let forget_all () = forget_all iprinter

let tv_set = ref Sid.empty

(* info *)

type info = {
  info_syn : syntax_map;
  symbol_printers : (string * ident_printer) Mid.t;
  realization : bool;
  ssreflect: bool;
}

(* type variables *)

let print_tv info ~whytypes fmt tv =
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s" n;
  if whytypes && not info.ssreflect then fprintf fmt " %s_WT" n

let print_tv_binder info ~whytypes ~implicit fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  if info.ssreflect then
    fprintf fmt "{%s: why3Type}" n
  else begin
    if implicit then fprintf fmt "{%s:Type}" n else fprintf fmt "(%s:Type)" n;
    if whytypes then fprintf fmt " {%s_WT:WhyType %s}" n n
  end

let print_tv_binders info ~whytypes ~implicit fmt stv =
  Stv.iter (fprintf fmt "@ %a" (print_tv_binder info ~whytypes ~implicit)) stv

let print_tv_binders_list info ~whytypes ~implicit fmt ltv =
  List.iter (fprintf fmt "@ %a" (print_tv_binder info ~whytypes ~implicit)) ltv

let print_params info ~whytypes fmt stv =
  if Stv.is_empty stv then () else
    fprintf fmt "@[<2>forall%a,@]@ "
      (print_tv_binders info ~whytypes ~implicit:true) stv

let print_params_list info ~whytypes fmt ltv =
  match ltv with
  | [] -> ()
  | _ ->
    fprintf fmt "forall%a,@ "
      (print_tv_binders_list info ~whytypes ~implicit:false) ltv

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables *)
let print_vs fmt vs =
  let n = id_unique iprinter vs.vs_name in
  fprintf fmt "%s" n

let forget_var vs = forget_id iprinter vs.vs_name

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique iprinter ts.ts_name)

let print_ls fmt ls =
  fprintf fmt "%s" (id_unique iprinter ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique iprinter pr.pr_name)

let ls_ty_vars ls =
  let ty_vars_args = List.fold_left Ty.ty_freevars Stv.empty ls.ls_args in
  let ty_vars_value = Opt.fold Ty.ty_freevars Stv.empty ls.ls_value in
  (ty_vars_args, ty_vars_value, Stv.union ty_vars_args ty_vars_value)


(* unused printing function
let print_path = print_list (constant_string ".") string
*)

let print_id fmt id = string fmt (id_unique iprinter id)

let print_id_real info fmt id =
  try
    let path,ipr = Mid.find id info.symbol_printers in
    fprintf fmt "%s.%s" path (id_unique ipr id)
  with Not_found -> print_id fmt id

let print_ls_real info fmt ls =
  print_id_real info fmt ls.ls_name

let print_ts_real info fmt ts = print_id_real info fmt ts.ts_name
(* unused printing function
let print_pr_real info fmt pr = print_id_real info fmt pr.pr_name
*)

(** Types *)

let print_ts_tv info fmt ts =
  match ts.ts_args with
  | [] -> fprintf fmt "%a" print_ts ts
  | _ -> fprintf fmt "(%a %a)" print_ts ts
    (print_list space (print_tv info ~whytypes:false)) ts.ts_args

let protect_on ?(boxed=false) x s =
  if x then "@[<1>(" ^^ s ^^ ")@]"
  else if not boxed then "@[" ^^ s ^^ "@]"
  else s

let rec print_type info fmt ty = print_ty false info fmt ty
and print_op_type info fmt ty = print_ty true info fmt ty
and print_ty op info fmt ty =
  begin match ty.ty_node with
  | Tyvar v -> print_tv info ~whytypes:false fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      begin
        match tl with
        | [] -> fprintf fmt "unit"
        | [ty] -> print_ty op info fmt ty
        | _ -> fprintf fmt "(%a)%%type" (print_list star (print_op_type info)) tl
      end
  | Tyapp (ts, [l;r]) when ts_equal ts ts_func ->
      fprintf fmt (protect_on op "%a ->@ %a") (print_op_type info) l (print_type info) r
  | Tyapp (ts, tl) ->
    begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_op_type info) fmt tl
      | None ->
        begin
          match tl with
          | [] -> (print_ts_real info) fmt ts
          | l -> fprintf fmt (protect_on op "%a%a") (print_ts_real info) ts
             (print_list_pre space (print_op_type info)) l
        end
    end
  end

(* can the type of a value be derived from the type of the arguments? *)
let unambig_fs fs =
  let rec lookup v ty = match ty.ty_node with
    | Tyvar u when tv_equal u v -> true
    | _ -> ty_any (lookup v) ty
  in
  let lookup v = List.exists (lookup v) fs.ls_args in
  let rec inspect ty = match ty.ty_node with
    | Tyvar u when not (lookup u) -> false
    | _ -> ty_all inspect ty
  in
  match fs.ls_value with
  | None -> true
  | Some v -> inspect v

(** Patterns, terms, and formulas *)

let lparen_r fmt () = fprintf fmt "@[<1>("
let rparen_r fmt () = fprintf fmt ")@]"
let print_paren_r f =
  print_list_delim ~start:lparen_r ~stop:rparen_r ~sep:comma f

let arrow fmt () = fprintf fmt " ->@ "
let print_arrow_list fmt x = print_list_suf arrow fmt x

let rec print_pattern info fmt p = print_pat false info fmt p
and print_pat op info fmt p = match p.pat_node with
  | Pwild -> fprintf fmt "_"
  | Pvar v -> print_vs fmt v
  | Pas (p,v) ->
      fprintf fmt (protect_on op "%a as %a") (print_pat true info) p print_vs v
  | Por (p,q) ->
      fprintf fmt (protect_on op "%a|%a") (print_pat true info) p (print_pat true info) q
  | Papp (cs,pl) when is_fs_tuple cs ->
      print_paren_r (print_pat false info) fmt pl
  | Papp (cs,pl) ->
      begin match query_syntax info.info_syn cs.ls_name with
        | Some s -> syntax_arguments s (print_pat true info) fmt pl
        | _ when pl = [] -> print_ls_real info fmt cs
        | _ -> fprintf fmt (protect_on op "%a@ %a")
          (print_ls_real info) cs (print_list space (print_pat true info)) pl
      end

let print_vsty info fmt v =
  fprintf fmt "@[<1>(%a:@,%a)@]" print_vs v (print_type info) v.vs_ty

let print_binop fmt = function
  | Tand -> fprintf fmt "/\\"
  | Tor -> fprintf fmt "\\/"
  | Timplies -> fprintf fmt "->"
  | Tiff -> fprintf fmt "<->"

(* [opl] means that there is no delimiter on the left of the term, so
   parentheses should be put around the term if it does not start with a
   delimiter; [opr] is similar, but on the right of the term  *)

let rec print_term info fmt t = print_tnode false false info fmt t
and print_opl_term info fmt f = print_tnode true  false info fmt f
and print_opr_term info fmt t = print_tnode false true  info fmt t
and print_tnode ?(boxed=false) opl opr info fmt t =
  print_comments fmt "(*" ~end_tok:"*)" t;
  match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      let number_format = {
          Number.long_int_support = true;
          Number.extra_leading_zeros_support = true;
          Number.negative_int_support = Number.Number_custom "(-%a)%%Z";
          Number.dec_int_support =
            if info.ssreflect then Number.Number_custom "%s%%:Z"
            else Number.Number_custom "%s%%Z";
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_unsupported;
          Number.negative_real_support = Number.Number_custom "(-%a)%%R";
          Number.dec_real_support = Number.Number_unsupported;
          Number.hex_real_support = Number.Number_unsupported;
          Number.frac_real_support = Number.Number_custom
            (Number.PrintFracReal ("%s%%R", "(%s * %s)%%R", "(%s / %s)%%R"));
          Number.def_real_support = Number.Number_unsupported;
        } in
      Number.print number_format fmt c
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a :=@ %a in@ %a")
        print_vs v (print_term info) t1 (print_term info) t2;
      forget_var v
  | Tcase (t,bl) ->
      fprintf fmt "@[<v>match %a with@,%a@,end@]"
        (print_term info) t
        (print_list pp_print_cut (print_tbranch info)) bl
  | Teps _ ->
      let vl,_,t0 = t_open_lambda t in
      if vl = [] then unsupportedTerm t "???"
      else begin
        if t0.t_ty = None then unsupportedTerm t
          "Coq: Prop-typed lambdas are not supported";
        fprintf fmt (protect_on opr "fun %a =>@ %a")
          (print_list space (print_vsty info)) vl
          (print_opl_term info) t0;
        List.iter forget_var vl
      end
  | Tapp (fs,[]) when is_fs_tuple fs ->
      fprintf fmt "tt"
  | Tapp (fs,pl) when is_fs_tuple fs ->
      fprintf fmt "%a" (print_paren_r (print_term info)) pl
  | Tapp (fs,[l;r]) when ls_equal fs fs_func_app ->
      fprintf fmt (protect_on (opl || opr) "%a@ %a") (print_opr_term info) l (print_opl_term info) r
  | Tapp (fs, tl) ->
    begin match query_syntax info.info_syn fs.ls_name with
      | Some s ->
          syntax_arguments s (print_opr_term info) fmt tl
      | _ -> if unambig_fs fs
          then
            if tl = [] then fprintf fmt "%a" (print_ls_real info) fs
            else fprintf fmt (protect_on (opl || opr) "%a@ %a")
              (print_ls_real info) fs
              (print_list space (print_opr_term info)) tl
          else fprintf fmt (protect_on (opl || opr) "@[%a%a@] :@ %a")
            (print_ls_real info) fs (print_list_pre space (print_opr_term info)) tl
            (print_type info) (t_type t)
    end
  | Tquant (Tforall,fq) ->
      let vl,_tl,f = t_open_quant fq in
      fprintf fmt (protect_on ~boxed opr "@[<2>forall %a@],@ %a")
        (print_list space (print_vsty info)) vl
        (print_tnode ~boxed:true false false info) f;
      List.iter forget_var vl
  | Tquant (Texists,fq) ->
      let vl,_tl,f = t_open_quant fq in
      let rec aux fmt vl =
        match vl with
        | [] -> print_term info fmt f
        | v::vr ->
            fprintf fmt "exists %a:@,%a,@ %a" print_vs v (print_type info) v.vs_ty aux vr in
      fprintf fmt (protect_on opr "%a") aux vl;
      List.iter forget_var vl
  | Ttrue ->
      fprintf fmt "True"
  | Tfalse ->
      fprintf fmt "False"
  | Tbinop (b,f1,f2) ->
     (match b with
     | Tand | Tor ->
       fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
               (print_opr_term info) f1 print_binop b (print_opl_term info) f2
     | Timplies ->
         (* implication has so low a precedence that its rhs does not need protection *)
         fprintf fmt (protect_on ~boxed (opl || opr) "%a ->@ %a")
           (print_opr_term info) f1 (print_tnode ~boxed:true false false info) f2
     | Tiff ->
         fprintf fmt (protect_on (opl || opr) "%a <->@ %a")
           (print_opr_term info) f1 (print_opl_term info) f2)
  | Tnot f ->
      fprintf fmt "~ %a" (print_tnode true true info) f
  | Tif (f1,f2,f3) ->
      fprintf fmt (protect_on opr
        "if %a then@ %a@ else@ %a")
        (print_term info) f1 (print_term info) f2 (print_term info) f3

and print_tbranch info fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<4>| %a =>@ %a@]"
    (print_pattern info) p (print_term info) t;
  Svs.iter forget_var p.pat_vars

(** Declarations *)

let print_constr info ts fmt (cs,_) =
  fprintf fmt "@[<4>| %a : %a%a%a@]" print_ls cs
    (print_arrow_list (print_op_type info)) cs.ls_args
    print_ts ts
      (print_list_pre space (print_tv info ~whytypes:false)) ts.ts_args

(*

  copy of old user scripts

*)

type content_type =
  Notation | (*Gallina |*) Vernacular

type statement =
  | Info  of string  (* name *)
  | Axiom of string (* name *)
  | Query of string * content_type * string (* name and content *)
  | Other of string (* content *)

exception StringValue of string

let read_generated_name =
  let def = Str.regexp "\\(Definition\\|Fixpoint\\|Inductive\\|CoInductive\\)[ ]+\\([^ :(.]+\\)" in
  fun ch ->
  try
    while true do
      let s = input_line ch in
      if Str.string_match def s 0 then
        raise (StringValue (Str.matched_group 2 s))
    done;
    assert false
  with StringValue name -> name

(** no nested comment *)
let read_comment =
  let start_comment = Str.regexp "(\\*[ ]+\\([^ :]+\\)" in
  let end_comment = Str.regexp ".*\\*)" in
  fun ch ->
    let line = ref "" in
    (* look for "( * name" *)
    let name =
      try
        while true do
          let s = input_line ch in
          if Str.string_match start_comment s 0 then begin
            line := s;
            raise (StringValue (Str.matched_group 1 s))
          end
        done;
        assert false
      with StringValue name -> name in
    (* look for end of comment *)
    while not (Str.string_match end_comment (!line) 0) do
      line := input_line ch
    done;
    name

let read_until re s i ch =
  if not (Str.string_match re s i) then
    while not (Str.string_match re (input_line ch) 0) do () done

let read_until_or_eof re s i ch =
  try
    read_until re s i ch; false
  with
  | End_of_file -> true

let read_old_proof =
  let def = Str.regexp "\\(Definition\\|Notation\\|Lemma\\|Theorem\\|Variable\\|Hypothesis\\)[ ]+\\([^ :({.]+\\)" in
  let def_end = Str.regexp ".*[.]$" in
  let old_intros = Str.regexp "^ *([*] Why3 intros " in
  let old_end = Str.regexp ".*[*])" in
  let qed = Str.regexp "\\(Qed\\|Defined\\|Save\\|Admitted\\)[.]" in
  fun ch ->
  try
    let start = ref (pos_in ch) in
    let s = input_line ch in
    if not (Str.string_match def s 0) then raise (StringValue s);
    let kind = Str.matched_group 1 s in
    let name = Str.matched_group 2 s in
    let end_app = ref "" in
    read_until def_end s (Str.match_end ()) ch;
    match kind with
    | "Variable" | "Hypothesis" -> Axiom name
    | _  ->
      let k =
        if kind = "Notation" then Notation
        else begin
          start := pos_in ch;
          let s = input_line ch in
          let read_end start =
            (* true if we reached EOF *)
            if read_until_or_eof qed start 0 ch then
              end_app := "Qed." in
          if Str.string_match old_intros s 0 then begin
            read_until old_end s (Str.match_end ()) ch;
            start := pos_in ch;
            read_end (input_line ch)
          end else
            read_end s;
          Vernacular
        end in
      let len = pos_in ch - !start in
      let s = Bytes.create len in
      seek_in ch !start;
      really_input ch s 0 len;
      Query (name, k, Bytes.unsafe_to_string s)
  with StringValue s -> Other s

(* Load old-style proofs where users were confined to a few sections. *)
let read_deprecated_script ch in_context =
  let sc = ref [] in
  let context = ref in_context in
  try
    while true do
      let pos = pos_in ch in
      let s = input_line ch in
      if !context then
        if s = "(* DO NOT EDIT BELOW *)" then context := false else
        sc := Other s :: !sc
      else if s <> "" then begin
        seek_in ch pos;
        sc := read_old_proof ch :: Other "" :: !sc;
        raise End_of_file
      end
    done;
    assert false
  with
  | End_of_file -> !sc

let read_old_script =
  let axm = Str.regexp "\\(Axiom\\|Parameter\\)[ ]+\\([^ :(.]+\\)" in
  let prelude = Str.regexp "(\\* This file is generated by Why3.*\\*)" in
  fun ch ->
  let skip_to_empty = ref false in
  let last_empty_line = ref 0 in
  let sc = ref [] in
  try
    while true do
      let s = input_line ch in
      if s = "" then last_empty_line := pos_in ch;
      if !skip_to_empty then (if s = "" then skip_to_empty := false) else
      if s = "(* Why3 comment *)" then
        (let name = read_comment ch in sc := Info name :: !sc;
         skip_to_empty := true) else
      if s = "(* Why3 assumption *)" then
        (let name = read_generated_name ch in sc := Axiom name :: !sc;
        skip_to_empty := true) else
      if Str.string_match axm s 0 then
        (let name = Str.matched_group 2 s in sc := Axiom name :: !sc;
        skip_to_empty := true) else
      if s = "(* Why3 goal *)" then
        (sc := read_old_proof ch :: !sc; skip_to_empty := true) else
      if Str.string_match prelude s 0 then
        (sc := Info "Why3 prelude" :: !sc;
         skip_to_empty := true) else
      if s = "(* YOU MAY EDIT THE CONTEXT BELOW *)" then
        (sc := read_deprecated_script ch true; raise End_of_file) else
      if s = "(* YOU MAY EDIT THE PROOF BELOW *)" then
        (seek_in ch !last_empty_line;
        sc := read_deprecated_script ch false;
        raise End_of_file) else
      sc := Other s :: !sc
    done;
    assert false
  with
  | End_of_file ->
    let rec rmv = function
      | Other "" :: t -> rmv t
      | l -> l in
    List.rev (rmv !sc)

(* Output all the Other entries of the script that occur before the
   location of name. Modify the script by removing the name entry and all
   these outputs. Return the user content. *)
let output_till_statement fmt script name =
  let print i =
    let rec aux acc = function
      | h :: l when h == i ->
        let l = match l with
          | Other "" :: l -> l
          | _ -> l in
        script := List.rev_append acc l
      | Other o :: l -> fprintf fmt "%s@\n" o; aux acc l
      | h :: l -> aux (h :: acc) l
      | [] -> assert false in
    aux [] !script in
  let rec find = function
    | Info n as o :: _ when n = name -> print o; Some o
    | Axiom n as o :: _ when n = name -> print o; Some o
    | Query (n,_,_) as o :: _ when n = name -> print o; Some o
    | [] -> None
    | _ :: t -> find t in
  find !script

let output_remaining fmt script =
  List.iter (function
    | Info _ | Axiom _ -> ()
    | Query (n,_,c) -> fprintf fmt "(* Unused content named %s@\n%s *)@\n" n c
    | Other c -> fprintf fmt "%s@\n" c) script

let rec intros_hyp n fmt f =
  match f.t_node with
    | Tbinop(Tand,f1,f2) ->
      fprintf fmt "(";
      let (m,vsl1) = intros_hyp n fmt f1 in
      fprintf fmt ",";
      let (k,vsl2) = intros_hyp m fmt f2 in
      fprintf fmt ")";
      (k,vsl1@vsl2)
    | Tquant(Texists,fq) ->
      let vsl,_trl,f = t_open_quant fq in
      let rec aux n vsl =
        match vsl with
          | [] -> intros_hyp n fmt f
          | v::l ->
            fprintf fmt "(%a," print_vs v;
            let m = aux n l in
            fprintf fmt ")";
            m
      in
      aux n vsl
    | _ ->
      fprintf fmt "h%d" n;
      (n+1,[])

let rec do_intros n fmt fmla =
  match fmla.t_node with
    | Tlet(_,fb) ->
      let vs,f = t_open_bound fb in
      fprintf fmt "@ %a" print_vs vs;
      do_intros n fmt f;
      forget_var vs
    | Tquant(Tforall,fq) ->
      let vsl,_trl,f = t_open_quant fq in
      List.iter
        (fun v -> fprintf fmt "@ %a" print_vs v) vsl;
      do_intros n fmt f;
      List.iter forget_var vsl
    | Tbinop(Timplies, f1, f2) ->
      fprintf fmt "@ ";
      let m,vsl = intros_hyp n fmt f1 in
      do_intros m fmt f2;
      List.iter forget_var vsl
    | _ -> ()

let need_intros fmla =
  match fmla.t_node with
  | Tlet _
  | Tquant(Tforall,_)
  | Tbinop(Timplies, _, _) -> true
  | _ -> false

let intros fmt fmla =
  fprintf fmt "@[intros%a.@]" (do_intros 1) fmla

let print_empty_proof fmt def =
  match def with
    | Some (_params,fmla) ->
      fprintf fmt "Proof.@\n";
      if need_intros fmla then intros fmt fmla;
      fprintf fmt "@\n@\nQed.@\n"
    | None ->
      fprintf fmt "Proof.@\n@\nDefined.@\n"

let print_previous_proof def info fmt previous =
  match previous with
  | None ->
    print_empty_proof fmt def
  | Some (Query (_,Vernacular,c)) ->
    begin match def with
    | Some (_p, f) when not info.realization && need_intros f ->
        fprintf fmt "@[(* Why3 %a *)@]@\n" (fun fmt f -> intros fmt f) f
    | _ -> ()
    end;
    fprintf fmt "%s" c
  | Some (Query (_,Notation,_))
  | Some (Axiom _) | Some (Other _) | Some (Info _) ->
    assert false

let print_type_decl ~prev info fmt ts =
  if is_ts_tuple ts then () else
  match ts.ts_def with
    | NoDef | Range _ | Float _ ->
      if info.realization then
        match prev with
        | Some (Query (_,Notation,c)) ->
          fprintf fmt "(* Why3 goal *)@\n%s@\n" c
        | Some (Axiom _) ->
          fprintf fmt "(* Why3 goal *)@\n@[<hv 2>Variable %a :@ @[%aType.@]@]@\n@[<hv 2>Hypothesis %a_WhyType :@ @[%aWhyType %a.@]@]@\nExisting Instance %a_WhyType.@\n@\n"
            print_ts ts (print_params_list info ~whytypes:false) ts.ts_args
            print_ts ts (print_params_list info ~whytypes:true)
              ts.ts_args (print_ts_tv info) ts print_ts ts
        | _ ->
          fprintf fmt "(* Why3 goal *)@\n@[<hv 2>Definition %a :@ @[%aType.@]@]@\n%a@\n"
            print_ts ts (print_params_list info ~whytypes:false) ts.ts_args
            (print_previous_proof None info) prev
      else begin
        fprintf fmt "@[<hv 2>Axiom %a :@ @[%aType.@]@]@\n"
          print_ts ts (print_params_list info ~whytypes:false) ts.ts_args;
        if not info.ssreflect then begin
          fprintf fmt "@[<hv 2>Parameter %a_WhyType :@ @[%aWhyType %a.@]@]@\n"
            print_ts ts (print_params_list info ~whytypes:true) ts.ts_args
            (print_ts_tv info) ts;
          fprintf fmt "Existing Instance %a_WhyType.@\n"
            print_ts ts
        end;
        fprintf fmt "@\n"
      end
    | Alias ty ->
      fprintf fmt "(* Why3 assumption *)@\n@[<2>Definition %a%a :=@ %a.@]@\n@\n"
        print_ts ts
          (print_list_pre space
             (print_tv_binder info ~whytypes:false ~implicit:false)) ts.ts_args
        (print_type info) ty

let print_type_decl ~prev info fmt ts =
  if not (Mid.mem ts.ts_name info.info_syn) then
    (print_type_decl ~prev info fmt ts; forget_tvs ())

let print_data_decl ~first info fmt ts csl =
  let name = id_unique iprinter ts.ts_name in
  if first then
    fprintf fmt "(* Why3 assumption *)@\n@[<2>Inductive"
  else fprintf fmt "@\nwith";
  fprintf fmt " %s%a :=@\n@[%a@]"
    name (print_list_pre space
            (print_tv_binder info ~whytypes:false ~implicit:false)) ts.ts_args
    (print_list newline (print_constr info ts)) csl;
  name

let print_data_whytype_and_implicits info fmt (name,ts,csl) =
  if not info.ssreflect then
    fprintf fmt "@[<2>Axiom %s_WhyType : %aWhyType %a.@]@\nExisting Instance %s_WhyType.@\n"
      name (print_params_list info ~whytypes:true) ts.ts_args
      (print_ts_tv info) ts name;
  List.iter
    (fun (cs,_) ->
      let _, _, all_ty_params = ls_ty_vars cs in
      if not (Stv.is_empty all_ty_params) then
        let print fmt tv =
          fprintf fmt "{%a}" (print_tv info ~whytypes:false) tv in
        fprintf fmt "@[<2>Arguments %a@ %a.@]@\n"
          print_ls cs
          (print_list space print) ts.ts_args)
    csl;
  fprintf fmt "@\n"

let print_data_decls info fmt tl =
  let none,d =
    List.fold_left
      (fun ((first,l) as acc) (ts,csl) ->
        if is_ts_tuple ts || Mid.mem ts.ts_name info.info_syn
        then acc else
        let name = print_data_decl info ~first fmt ts csl in
        forget_tvs ();
        (false,(name,ts,csl)::l))
      (true,[]) tl
  in
  if none then () else
    begin
      fprintf fmt ".@]@\n";
      List.iter (print_data_whytype_and_implicits info fmt) d
    end

let print_ls_type info fmt = function
  | None -> fprintf fmt "Prop"
  | Some ty -> print_type info fmt ty

let print_param_decl ~prev info fmt ls =
  let _, _, all_ty_params = ls_ty_vars ls in
  if info.realization then
    match prev with
    | Some (Query (_,Notation,c)) ->
      fprintf fmt "(* Why3 goal *)@\n%s@\n" c
    | Some (Axiom _) ->
      fprintf fmt "(* Why3 goal *)@\n@[<2>Variable %a: %a%a%a.@]@\n@\n"
        print_ls ls (print_params info ~whytypes:true) all_ty_params
        (print_arrow_list (print_op_type info)) ls.ls_args
        (print_ls_type info) ls.ls_value
    | (* Some Info *) _ when Mid.mem ls.ls_name info.info_syn ->
      let vl =
        List.map (fun ty -> create_vsymbol (id_fresh "x") ty) ls.ls_args in
      let e = Term.t_app ls (List.map Term.t_var vl) ls.ls_value in
      fprintf fmt
        "(* Why3 comment *)@\n\
         (* %a is replaced with %a by the coq driver *)@\n@\n"
        print_ls ls
        (print_term info) e;
      List.iter forget_var vl
    | _ ->
      fprintf fmt "(* Why3 goal *)@\n@[<hv 2>Definition @[<h>%a%a@] :@ @[%a%a.@]@]@\n%a@\n"
        print_ls ls
        (print_tv_binders info ~whytypes:true ~implicit:true) all_ty_params
        (print_arrow_list (print_op_type info)) ls.ls_args
        (print_ls_type info) ls.ls_value
        (print_previous_proof None info) prev
  else
    fprintf fmt "@[<hv 2>Parameter %a:@ @[%a%a%a.@]@]@\n@\n"
      print_ls ls (print_params info ~whytypes:true) all_ty_params
      (print_arrow_list (print_op_type info)) ls.ls_args
      (print_ls_type info) ls.ls_value

let print_param_decl ~prev info fmt ls =
  if info.realization || not (Mid.mem ls.ls_name info.info_syn) then
    (print_param_decl ~prev info fmt ls; forget_tvs ())

let print_logic_decl info fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let vl,e = open_ls_defn ld in
  fprintf fmt "(* Why3 assumption *)@\n@[<hv 2>@[<4>Definition %a%a%a :@ %a@] :=@ @[%a.@]@]@\n"
    print_ls ls
    (print_tv_binders info ~whytypes:true ~implicit:true) all_ty_params
    (print_list_pre space (print_vsty info)) vl
    (print_ls_type info) ls.ls_value
    (print_term info) e;
  List.iter forget_var vl;
  fprintf fmt "@\n"

let print_equivalence_lemma ~prev info fmt name (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let def_formula = ls_defn_axiom ld in
  fprintf fmt
    "(* Why3 goal *)@\n@[<hv 2>Lemma @[<h>%s%a@] :@ @[%a.@]@]@\n%a@\n"
    name
    (print_tv_binders info ~whytypes:true ~implicit:true) all_ty_params
    (print_term info) def_formula
    (print_previous_proof (Some (all_ty_params,def_formula)) info) prev

let print_equivalence_lemma ~old info fmt ((ls,_) as d) =
  if info.realization && (Mid.mem ls.ls_name info.info_syn) then
    let name = Ident.string_unique iprinter
      ((id_unique iprinter ls.ls_name)^"_def") in
    let prev = output_till_statement fmt old name in
    (print_equivalence_lemma ~prev info fmt name d; forget_tvs ())

let print_logic_decl ~old info fmt d =
  (* During realization the definition of a "builtin" symbol is
     printed and an equivalence lemma with associated coq function is
     requested *)
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_logic_decl info fmt d; forget_tvs ())
  else if info.realization then
    print_equivalence_lemma ~old info fmt d

let print_recursive_decl info fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let i = match Decl.ls_defn_decrease ld with
    | [i] -> i | _ -> assert false in
  let vl,e = open_ls_defn ld in
  fprintf fmt "%a%a%a {struct %a}: %a :=@ %a@]"
    print_ls ls
    (print_tv_binders info ~whytypes:true ~implicit:true) all_ty_params
    (print_list_pre space (print_vsty info)) vl
    print_vs (List.nth vl i)
    (print_ls_type info) ls.ls_value
    (print_term info) e;
  List.iter forget_var vl

let print_recursive_decl ~old info fmt dl =
  let dl_syn, dl_no_syn =
    List.partition (fun (ls,_) ->
      info.realization && (Mid.mem ls.ls_name info.info_syn)) dl in
  if dl_no_syn <> [] then begin
    fprintf fmt "(* Why3 assumption *)@\n";
    print_list_delim
      ~start:(fun fmt () -> fprintf fmt "@[<2>Fixpoint ")
      ~stop:(fun fmt () -> fprintf fmt ".@]@\n")
      ~sep:(fun fmt () -> fprintf fmt "@]@\n@[<2>with ")
      (fun fmt d -> print_recursive_decl info fmt d; forget_tvs ())
      fmt dl_no_syn;
    fprintf fmt "@\n";
  end;
  List.iter (print_equivalence_lemma ~old info fmt) dl_syn

let print_ind info fmt (pr,f) =
  fprintf fmt "@[<hv 4>| %a :@ @[%a@]@]" print_pr pr (print_term info) f

let print_ind_decl info fmt ps bl =
  let _, _, all_ty_params = ls_ty_vars ps in
  fprintf fmt " %a%a: %aProp :=@ @[%a@]"
    print_ls ps
    (print_tv_binders info ~whytypes:true ~implicit:true) all_ty_params
    (print_arrow_list (print_op_type info)) ps.ls_args
    (print_list newline (print_ind info)) bl

let print_ind_decls info s fmt tl =
  let none =
    List.fold_left (fun first (ps,bl) ->
      if Mid.mem ps.ls_name info.info_syn then first
      else begin
        if first then
          fprintf fmt "(* Why3 assumption *)@\n@[<2>%s"
            (match s with Ind -> "Inductive" | Coind -> "CoInductive")
          else fprintf fmt "@\nwith";
        print_ind_decl info fmt ps bl;
        forget_tvs ();
        false
      end) true tl in
  if not none then fprintf fmt ".@]@\n@\n"

let print_prop_decl ~prev info fmt (k,pr,f) =
  ignore prev;
  let params = t_ty_freevars Stv.empty f in
  let stt = match k with
    | Paxiom when info.realization -> "Lemma"
    | Paxiom -> ""
    | Plemma -> "Lemma"
    | Pgoal -> "Theorem"
  in
  if stt <> "" then
    match prev with
    | Some (Axiom _) when stt = "Lemma" ->
      fprintf fmt "(* Why3 goal *)@\n@[<hv 2>Hypothesis %a :@ @[%a%a.@]@]@\n@\n"
        print_pr pr (print_params info ~whytypes:true) params
        (print_term info) f
    | _ ->
      fprintf fmt "(* Why3 goal *)@\n@[<hv 2>%s @[<h>%a%a@] :@ @[%a.@]@]@\n%a@\n"
        stt print_pr pr
        (print_tv_binders info ~whytypes:true ~implicit:true) params
        (print_term info) f
        (print_previous_proof (Some (params,f)) info) prev
  else
    fprintf fmt "@[<hv 2>Axiom %a :@ @[%a%a.@]@]@\n@\n"
      print_pr pr (print_params info ~whytypes:true) params
      (print_term info) f;
  forget_tvs ()

let print_decl ~old info fmt d =
  let name =
    match d.d_node with
    | Dtype ts
    | Ddata ((ts, _)::_) -> id_unique iprinter ts.ts_name
    | Dparam ls
    | Dlogic ((ls,_)::_)
    | Dind (_, (ls,_)::_) -> id_unique iprinter ls.ls_name
    | Dprop (_,pr,_) -> id_unique iprinter pr.pr_name
    | Ddata []
    | Dlogic []
    | Dind (_, []) -> assert false in
  let prev = output_till_statement fmt old name in
  match d.d_node with
  | Dtype ts ->
      print_type_decl ~prev info fmt ts
  | Ddata tl -> print_data_decls info fmt tl
  | Dparam ls ->
      print_param_decl ~prev info fmt ls
  | Dlogic [s,_ as ld] when not (Sid.mem s.ls_name d.d_syms) ->
      print_logic_decl ~old info fmt ld
  | Dlogic ll ->
      print_recursive_decl ~old info fmt ll
  | Dind (s, il) ->
      print_ind_decls info s fmt il
  | Dprop (_,pr,_) when not info.realization && Mid.mem pr.pr_name info.info_syn ->
      ()
  | Dprop pr ->
      print_prop_decl ~prev info fmt pr

let print_decls ~old info fmt dl =
  fprintf fmt "@\n@[%a@]" (print_list nothing (print_decl ~old info)) dl

let print_task printer_args ~realize ~ssreflect ?old fmt task =
  (* eprintf "Task:%a@.@." Pretty.print_task task; *)
  forget_all ();
  (* find theories that are both used and realized from metas *)
  let realized_theories =
    Task.on_meta meta_realized_theory (fun mid args ->
      match args with
      | [Theory.MAstr s1; Theory.MAstr s2] ->
        (* TODO: do not split string; in fact, do not even use a string argument *)
        let f,id =
          let l = Strings.rev_split '.' s1 in
          List.rev (List.tl l), List.hd l in
        let th = Env.read_theory printer_args.env f id in
        Mid.add th.Theory.th_name (th, if s2 = "" then s1 else s2) mid
      | _ -> assert false
    ) Mid.empty task in
  (* 2 cases: goal is use T or goal is a real goal *)
  let rec upd_realized_theories = function
    | Some { Task.task_decl = { Theory.td_node =
               Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, _, _) }}} ->
        realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Use th }} ->
        Sid.iter (fun id -> ignore (id_unique iprinter id)) th.Theory.th_local;
        Mid.remove th.Theory.th_name realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Meta _ };
             Task.task_prev = task } ->
        upd_realized_theories task
    | _ -> assert false in
  let realized_theories = upd_realized_theories task in
  let realized_theories' = Mid.map fst realized_theories in
  let realized_symbols = Task.used_symbols realized_theories' in
  let local_decls = Task.local_decls task realized_symbols in
  (* eprintf "local_decls:%i@." (List.length local_decls); *)
  (* associate a special printer to each symbol in a realized theory *)
  let symbol_printers =
    let printers =
      Mid.map (fun th ->
        let pr = fresh_printer () in
        Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
        pr
      ) realized_theories' in
    Mid.map (fun th ->
      (snd (Mid.find th.Theory.th_name realized_theories),
       Mid.find th.Theory.th_name printers)
    ) realized_symbols in
  let info = {
    info_syn = get_syntax_map task;
    symbol_printers = symbol_printers;
    realization = realize;
    ssreflect = ssreflect;
  }
  in
  let old = ref (match old with
    | None -> []
    | Some ch -> read_old_script ch) in
  ignore (output_till_statement fmt old "Why3 prelude");
  print_prelude fmt printer_args.prelude;
  print_th_prelude task fmt printer_args.th_prelude;
  Mid.iter (fun _ (_, s) -> fprintf fmt "Require %s.@\n" s) realized_theories;
  print_decls ~old info fmt local_decls;
  output_remaining fmt !old

let print_task_full args ?old fmt task =
  print_task args ~realize:false ~ssreflect:false ?old fmt task

let print_task_real args ?old fmt task =
  print_task args ~realize:true  ~ssreflect:false ?old fmt task

let () = register_printer "coq" print_task_full
  ~desc:"Printer@ for@ the@ Coq@ proof@ assistant@ \
         (without@ realization@ capabilities)."
let () = register_printer "coq-realize" print_task_real
  ~desc:"Printer@ for@ the@ Coq@ proof@ assistant@ \
         (with@ realization@ capabilities)."

let print_task_full_ssr args ?old fmt task =
  print_task args ~realize:false ~ssreflect:true ?old fmt task
let () = register_printer "coq-ssr" print_task_full_ssr
  ~desc:"Printer@ for@ the@ Coq@ proof@ assistant,@ ssreflect@ extension\
         (without@ realization@ capabilities)."


(* specific printer for realization of theories *)
(* OBSOLETE

open Theory

let print_tdecl ~old info fmt d = match d.td_node with
  | Decl d ->
      print_decl ~old info fmt d
  | Use t ->
      fprintf fmt "Require %s.@\n@\n"
        (id_unique iprinter t.th_name)
  | Meta _ -> assert false (* TODO ? *)
  | Clone _ -> assert false (* TODO *)

let print_tdecls ~old info fmt dl =
  fprintf fmt "@[<hov>%a@\n@]"
    (print_list nothing (print_tdecl ~old info)) dl

let print_theory _env pr thpr ?old fmt th =
  forget_all ();
  print_prelude fmt pr;
  print_prelude_for_theory th fmt thpr;
  let info = {
    info_syn = (Mid.empty : string Ident.Mid.t)
      (* get_syntax_map_of_theory th*);
    realization = true;
  }
  in
  let old = match old with
    | None -> None
    | Some ch -> Some(ref NoWhere,ch)
  in
  print_tdecls ~old info fmt th.th_decls;
  produce_remaining_contexts_and_proofs ~old fmt

*)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. "
End:
*)
