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

(** Gappa printer *)

open Format
open Pp
open Printer
open Ident
open Term
open Decl
open Theory
open Task

let syntactic_transform transf =
  Trans.on_meta meta_syntax_logic (fun metas ->
    let symbols = List.fold_left (fun acc meta_arg ->
      match meta_arg with
      | [MAls ls; MAstr _; MAint _] -> Sls.add ls acc
      | _ -> assert false) Sls.empty metas in
    transf (fun ls -> Sls.mem ls symbols))

let () =
  Trans.register_transform "abstract_unknown_lsymbols"
    (syntactic_transform Abstraction.abstraction)
    ~desc:"Abstract@ applications@ of@ non-built-in@ symbols@ with@ \
      constants.@ Used@ by@ the@ Gappa@ pretty-printer.";
  Trans.register_transform "simplify_unknown_lsymbols"
    (syntactic_transform (fun check_ls -> Trans.goal (fun pr f ->
      [create_prop_decl Pgoal pr (Simplify_formula.fmla_cond_subst
        (fun t1 t2 -> match t1.t_node with
          | Tconst _ -> false
          | Tapp(_,[]) ->
            begin match t2.t_node with
            | Tconst _ | Tapp(_,[]) -> true
            | _ -> false
            end
          | Tapp(ls,_) -> not (check_ls ls)
          | _ -> true) f)
      ])))
    ~desc:"Same@ as@ simplify_trivial_quantification_in_goal,@ but@ instead@ \
      of@ substituting@ quantified@ variables,@ substitute@ applications@ \
      of@ non-built-in@ symbols.@ Used@ by@ the@ Gappa@ pretty-printer."

(* patterns (TODO: add a parser and generalize it out of Gappa) *)

type pattern =
  | PatHole of int
  | PatApp of Env.pathname * string * string list * pattern list

let incremental_pat_match env holes =
  let rec aux p t =
    match p, t.t_node with
    | PatHole i, _ ->
        begin match holes.(i) with
        | None -> holes.(i) <- Some t
        | Some t' -> if not (t_equal t t') then raise Not_found
        end
    | PatApp (sp,ss,sl,pl), Tapp (ls,tl) ->
        if List.length pl <> List.length tl then raise Not_found;
        let th = Env.read_theory env sp ss in
        let s = ns_find_ls th.th_export sl in
        if not (ls_equal s ls) then raise Not_found;
        List.iter2 aux pl tl
    | _, _ -> raise Not_found in
  aux

let pat_match env nb_holes p t =
  let holes = Array.make nb_holes None in
  incremental_pat_match env holes p t;
  Array.map (function None -> raise Not_found | Some t -> t) holes

(* Gappa pre-compilation *)

type info = {
  info_env : Env.env;
  info_symbols : Sid.t;
  info_ops_of_rel : (string * string * string) Mls.t;
  info_syn : syntax_map;
}

let int_minus = ref ps_equ
let real_minus = ref ps_equ

(** lsymbol, ""/"not ", op, rev_op *)
let arith_meta = register_meta "gappa arith"
  [MTlsymbol;MTstring;MTstring;MTstring]
  ~desc:"Specify@ how@ to@ pretty-print@ arithmetic@ \
          operations@ in@ the@ Gappa@ format:@\n  \
    @[\
     @[<hov 2>- first@ argument:@ the@ symbol@]@\n\
     @[<hov 2>- second@ argument:@ the@ prefix@ to@ put@ before@ the@ term@]@\n\
     @[<hov 2>- third@ argument:@ the@ operator@ to@ print@]@\n\
     @[<hov 2>- fourth@ argument:@ the@ inverse@ operator@]\
    @]"

let find_th env file th =
  let theory = Env.read_theory env [file] th in
  fun id -> Theory.ns_find_ls theory.Theory.th_export [id]

let get_info env task =
  (* unary minus for constants *)
  int_minus := find_th env "int" "Int" (op_prefix "-");
  real_minus := find_th env "real" "Real" (op_prefix "-");
  (* handling of inequalities *)
  let ops = on_meta arith_meta (fun acc meta_arg ->
    match meta_arg with
    | [MAls ls; MAstr s; MAstr op; MAstr rev_op] ->
        Mls.add ls (s,op,rev_op) acc
    | _ -> assert false) Mls.empty task in
  (* sets of known symbols *)
  let syn = get_syntax_map task in
  let symb = Mid.map (Util.const ()) syn in
  let symb = Mls.fold (fun ls _ acc -> Sid.add ls.ls_name acc) ops symb in
  let symb = Sid.add ps_equ.ls_name symb in
  {
    info_env = env;
    info_symbols = symb;
    info_ops_of_rel = ops;
    info_syn = syn;
  }

(* Gappa printing *)

let ident_printer =
  let bls = [
      "sqrt"; "fma";
      "float"; "fixed"; "int";
      "homogen80x"; "homogen80x_init"; "float80x";
      "add_rel"; "sub_rel"; "mul_rel"; "fma_rel";
    ] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let number_format = {
    Number.long_int_support = true;
    Number.extra_leading_zeros_support = true;
    Number.negative_int_support = Number.Number_custom "-%a";
    Number.dec_int_support = Number.Number_default;
    Number.hex_int_support = Number.Number_default;
    Number.oct_int_support = Number.Number_unsupported;
    Number.bin_int_support = Number.Number_unsupported;
    Number.def_int_support = Number.Number_unsupported;
    Number.negative_real_support = Number.Number_custom "-%a";
    Number.dec_real_support = Number.Number_default;
    Number.hex_real_support = Number.Number_default;
    Number.frac_real_support = Number.Number_unsupported;
    Number.def_real_support = Number.Number_unsupported;
  }

type constant = Enum of term * int | Value of term | Varying

let rec constant_value defs t =
  match t.t_node with
  | Tconst c ->
      asprintf "%a" (Number.print number_format) c
  | Tapp (ls, [{ t_node = Tconst c}])
      when ls_equal ls !int_minus || ls_equal ls !real_minus ->
      asprintf "-%a" (Number.print number_format) c
  | Tapp (ls, []) ->
    begin
      match Hid.find defs ls.ls_name with
      | Enum (_,i) -> Printf.sprintf "%d" i
      | Value c -> constant_value defs c
      | Varying -> raise Not_found
    end
  | _ -> raise Not_found

(* terms *)

let rec print_term info defs fmt t =
  let term = print_term info defs in
  try
    match t.t_node with
    | Tapp ( { ls_name = id }, [] ) ->
       begin match query_syntax info.info_syn id with
       | Some s -> syntax_arguments s term fmt []
       | None -> fprintf fmt "%s" (constant_value defs t)
       end
    | _ -> fprintf fmt "%s" (constant_value defs t)
  with Not_found ->
  match t.t_node with
  | Tconst _ -> assert false
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp ( { ls_name = id }, [] ) ->
      print_ident fmt id
  | Tapp (ls, tl) ->
      begin match query_syntax info.info_syn ls.ls_name with
        | Some s -> syntax_arguments s term fmt tl
        | None ->
            unsupportedTerm t
              ("gappa: function '" ^ ls.ls_name.id_string ^ "' is not supported")
      end
  | Tlet _ -> unsupportedTerm t
      "gappa: you must eliminate let in term"
  | Tif _ -> unsupportedTerm t
      "gappa: you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t
      "gappa: you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "gappa: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)


(* predicates *)

let rel_error_pat =
  PatApp (["real"], "Real", [op_infix "<="], [
    PatApp (["real"], "Abs", ["abs"], [
      PatApp (["real"], "Real", [op_infix "-"], [
        PatHole 0;
        PatHole 1])]);
    PatApp (["real"], "Real", [op_infix "*"], [
      PatHole 2;
        PatApp (["real"], "Abs", ["abs"], [
          PatHole 1])])])

let rec print_fmla info defs fmt f =
  let term = print_term info defs in
  let fmla = print_fmla info defs in
  match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
    begin match query_syntax info.info_syn id with
      | Some s -> syntax_arguments s term fmt []
      | None -> fprintf fmt "%a in [1,1]" print_ident id
    end
  | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
      (* TODO: distinguish between type of t1 and t2
         the following is OK only for real of integer
      *)
      begin try
        let c1 = constant_value defs t1 in
        fprintf fmt "%a in [%s,%s]" term t2 c1 c1
      with Not_found ->
        try
          let c2 = constant_value defs t2 in
          fprintf fmt "%a in [%s,%s]" term t1 c2 c2
        with Not_found ->
          fprintf fmt "%a - %a in [0,0]" term t1 term t2
      end
  | Tapp (ls, [t1;t2]) when Mls.mem ls info.info_ops_of_rel ->
      let s,op,rev_op = try Mls.find ls info.info_ops_of_rel
        with Not_found -> assert false
      in
      begin try
        let t = pat_match info.info_env 3 rel_error_pat f in
        let c = constant_value defs t.(2) in
        fprintf fmt "|%a -/ %a| <= %s" term t.(0) term t.(1) c
      with Not_found -> try
        let c1 = constant_value defs t1 in
        fprintf fmt "%s%a %s %s" s term t2 rev_op c1
      with Not_found ->
        try
          let c2 = constant_value defs t2 in
          fprintf fmt "%s%a %s %s" s term t1 op c2
        with Not_found ->
          fprintf fmt "%s%a - %a %s 0" s term t1 term t2 op
      end
  | Tapp (ls, tl) ->
      begin match query_syntax info.info_syn ls.ls_name with
        | Some s -> syntax_arguments s term fmt tl
        | None ->
            unsupportedTerm f
              ("gappa: predicate '" ^ ls.ls_name.id_string ^ "' is not supported")
      end
  | Tquant (_q, _fq) ->
      unsupportedTerm f
        "gappa: quantifiers are not supported"
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "(%a /\\@ %a)" fmla f1 fmla f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "(%a \\/@ %a)" fmla f1 fmla f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" fmla f1 fmla f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "((%a ->@ %a) /\\@ (%a ->@ %a))" fmla f1 fmla f2 fmla f2 fmla f1
  | Tnot f ->
      fprintf fmt "not %a" fmla f
  | Ttrue ->
      fprintf fmt "(0 in [0,0])"
  | Tfalse ->
      fprintf fmt "(1 in [0,0])"
  | Tif (_f1, _f2, _f3) ->
      unsupportedTerm f
        "gappa: you must eliminate if in formula"
  | Tlet _ -> unsupportedTerm f
      "gappa: you must eliminate let in formula"
  | Tcase _ -> unsupportedTerm f
      "gappa: you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

let get_constant defs t =
  let rec follow neg_ls t =
    match t.t_node with
    | Tconst _ ->
      begin
        match neg_ls with
        | Some ls -> Value (t_app_infer ls [t])
        | None -> Value t
      end
    | Tapp (ls, [t])
        when ls_equal ls !int_minus || ls_equal ls !real_minus ->
        follow (match neg_ls with None -> Some ls | Some _ -> None) t
    | Tapp (ls, []) ->
      begin
        match Hid.find defs ls.ls_name with
        | Value t -> follow neg_ls t
        | Enum _ as e -> e
        | Varying -> Varying
        | exception Not_found -> Varying
      end
    | _ -> Varying in
  follow None t

let rec simpl_fmla defs truths f =
  match f.t_node with
  | Tapp (ls, []) ->
    begin
      try if Hid.find truths ls.ls_name then t_true else t_false
      with Not_found -> f
    end
  | Tapp (ls, [{ t_node = Tapp (t1, []) }; t2])
      when ls_equal ls ps_equ && t_equal t2 t_bool_true ->
    begin
      try if Hid.find truths t1.ls_name then t_true else t_false
      with Not_found -> f
    end
  | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
    begin
      match get_constant defs t1, get_constant defs t2 with
      | Enum (_, i1), Enum (_, i2) ->
        if i1 = i2 then t_true else t_false
      | _, _ -> f
    end
  | Tbinop _ | Tnot _ -> t_map_simp (simpl_fmla defs truths) f
  | _ -> f


exception AlreadyDefined
exception Contradiction

let split_hyp defs truths pr acc f =
  let rec split acc pos f =
    match f.t_node with
    | Tbinop (Tand, f1, f2) when pos ->
        split (split acc true f1) true f2
    | Tbinop (Tor, f1, f2) when not pos ->
        split (split acc false f1) false f2
    | Tbinop (Timplies, f1, f2) when not pos ->
        split (split acc true f1) false f2
    | Tapp (ls,[]) ->
        let () =
          try if Hid.find truths ls.ls_name <> pos then raise Contradiction
          with Not_found -> Hid.add truths ls.ls_name pos in
        acc
    | Tapp (ls, [{ t_node = Tapp (t1, []) }; t2])
        when ls_equal ls ps_equ && t_equal t2 t_bool_true ->
        let () =
          try if Hid.find truths t1.ls_name <> pos then raise Contradiction
          with Not_found -> Hid.add truths t1.ls_name pos in
        acc
    | Ttrue -> if pos then acc else raise Contradiction
    | Tfalse -> if pos then raise Contradiction else acc
    | Tnot f -> split acc (not pos) f
    | Tapp (ls, [t1; t2]) when pos && ls_equal ls ps_equ ->
      begin
        let try_equality t c =
          match t.t_node with
          | Tapp (ls,[]) -> Hid.add defs ls.ls_name c; acc
          | _ -> (pr,f)::acc in
        match get_constant defs t1, get_constant defs t2 with
        | Enum (_, i1), Enum (_, i2) ->
          if i1 = i2 then acc else raise Contradiction
        | (Enum _ as c1), Varying -> try_equality t2 c1
        | Varying, (Enum _ as c2) -> try_equality t1 c2
        | _, _ -> (pr,f)::acc
      end
    | _ -> if pos then (pr,f)::acc else (pr, t_not f)::acc in
  split acc true f

let prepare defs ints truths acc d =
  match d.d_node with
  | Dtype _ -> acc
  | Ddata dl ->
    List.iter (fun (_, dl) ->
      let _ = List.fold_left (fun idx (cs,cl) ->
        match cl with
        | [] ->
          Hid.replace defs cs.ls_name (Enum (t_app_infer cs [], idx));
          idx + 1
        | _ -> idx
        ) 0 dl in ()) dl;
    acc
  | Dparam ({ ls_args = []; ls_value = Some ty; } as ls) when Ty.ty_equal ty Ty.ty_int ->
    ints := ls::!ints; acc
  | Dparam _ | Dlogic _ -> acc
  | Dind _ ->
      unsupportedDecl d
        "please remove inductive definitions before calling gappa printer"
  | Dprop (Paxiom, pr, f) ->
      split_hyp defs truths pr acc (simpl_fmla defs truths f)
  | Dprop (Pgoal, pr, f) ->
      split_hyp defs truths pr acc (simpl_fmla defs truths (t_not f))
  | Dprop (Plemma, _, _) ->
      unsupportedDecl d "gappa: lemmas are not supported"

let filter_hyp defs (eqs, hyps) ((pr, f) as hyp) =
  match f.t_node with
  | Tapp(ls,[t1;t2]) when ls_equal ls ps_equ ->
    begin
      let try_equality t1 t2 =
        let l =
          match t1.t_node with
          | Tapp (l,[]) -> l
          | _ -> raise AlreadyDefined in
        if Hid.mem defs l.ls_name then raise AlreadyDefined;
        if t_s_any (fun _ -> false) (fun ls -> ls_equal ls l) t2
        then raise AlreadyDefined;
        let c = get_constant defs t2 in
        Hid.add defs l.ls_name c;
        match c with
        | Varying ->
           t_s_fold (fun _ _ -> ())
             (fun _ ls ->
              if not (Hid.mem defs ls.ls_name) then Hid.add defs ls.ls_name Varying)
             () t2;
           ((pr,t1,t2)::eqs, hyps)
        | _ -> (eqs, hyps) in
      try
        try_equality t1 t2
      with AlreadyDefined -> try
        try_equality t2 t1
      with AlreadyDefined ->
        (eqs, hyp::hyps)
    end
  | _ -> (eqs, hyp::hyps)

let find_used_equations eqs hyps =
  let used = Hid.create 17 in
  let mark_used f =
    t_s_fold (fun _ _ -> ()) (fun _ ls -> Hid.replace used ls.ls_name ()) () f in
  List.iter (fun (_,f) -> mark_used f) hyps;
  List.fold_left (fun acc ((_, v, t) as eq) ->
    let v = match v.t_node with Tapp (l,[]) -> l.ls_name | _ -> assert false in
    if Hid.mem used v then begin
      mark_used t;
      eq :: acc
    end else acc
  ) [] eqs

let rec find_used_bools known acc f =
  match f.t_node with
  | Tapp(ls,[]) ->
      if Hid.mem known ls.ls_name then acc
      else (Hid.add known ls.ls_name (); ls.ls_name :: acc)
  | Tbinop (_, f1, f2) ->
      find_used_bools known (find_used_bools known acc f2) f1
  | Tnot f ->
      find_used_bools known acc f
  | _ -> acc

let print_equation info defs fmt (pr,t1,t2) =
  fprintf fmt "# equation '%a'@\n" print_ident pr.pr_name;
  fprintf fmt "%a = %a ;@\n" (print_term info defs) t1 (print_term info defs) t2

let print_bool fmt ls =
  fprintf fmt "(%a in [0,0] \\/ %a in [1,1]) ->@\n"
          print_ident ls print_ident ls

let print_bool2 fmt ls =
  fprintf fmt "%a in (0.5)" print_ident ls

let print_hyp info defs fmt (pr,f) =
  fprintf fmt "# hypothesis '%a'@\n" print_ident pr.pr_name;
  fprintf fmt "%a ->@\n" (print_fmla info defs) f

let print_ints fmt ls =
  fprintf fmt "@FIX(%a,0) ->@\n" print_ident ls.ls_name

let print_task args ?old:_ fmt task =
  forget_all ident_printer;
  let info = get_info args.env task in
  print_prelude fmt args.prelude;
  print_th_prelude task fmt args.th_prelude;
  try
    let defs = Hid.create 17 in
    let ints = ref [] in
    (* get hypotheses and simplify them *)
    let hyps =
      let truths = Hid.create 17 in
      let rec iter old_nb hyps =
        let hyps =
          List.fold_left
            (fun acc (pr,f) ->
             split_hyp defs truths pr acc (simpl_fmla defs truths f))
            [] hyps in
        let hyps = List.rev hyps in
        let nb = Hid.length truths in
        if nb > old_nb then iter nb hyps
        else hyps in
      let hyps = List.fold_left (prepare defs ints truths) [] (Task.task_decls task) in
      iter (Hid.length truths) (List.rev hyps) in
    (* extract equations and keep the needed ones *)
    let (eqs, hyps) = List.fold_left (filter_hyp defs) ([],[]) hyps in
    let hyps = List.rev hyps in
    let eqs = find_used_equations eqs hyps in
    (* find needed booleans *)
    let bools =
      let bools = Hid.create 17 in
      List.fold_left (fun acc (_,f) -> find_used_bools bools acc f) [] hyps in
    (* print equalities *)
    List.iter (print_equation info defs fmt) eqs;
    (* print formula *)
    match List.rev hyps with
    | [] -> fprintf fmt "{ 1 in [0,0] }@\n"
    | (_,goal) :: hyps ->
      fprintf fmt "@[<v 2>{ %a%a%a%a }@]@\n%a"
        (print_list nothing print_bool) bools
        (print_list nothing print_ints) (!ints)
        (print_list nothing (print_hyp info defs)) hyps
        (print_fmla info defs) (t_not_simp goal)
        (print_list_delim
           ~start:(fun fmt () -> fprintf fmt "$ ")
           ~stop:(fun fmt () -> fprintf fmt ";@\n")
           ~sep:comma print_bool2) bools
  with Contradiction -> fprintf fmt "{ 0 in [0,0] }@\n"

let () = register_printer "gappa" print_task
  ~desc:"Printer@ for@ the@ Gappa@ theorem@ prover@ specialized@ in@ \
         floating@ point@ reasoning."
