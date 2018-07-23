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

(** Mathematica printer *)

open Format
open Pp
open Printer
open Ident
open Ty
open Term
open Decl
open Theory
open Task

(* patterns (TODO: add a parser and generalize it out of Mathematica) *)

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

(* Mathematica pre-compilation *)

type info = {
  info_env : Env.env;
  info_symbols : Sid.t;
  info_ops_of_rel : (string * string * string) Mls.t;
  info_syn : syntax_map;
  (*mutable info_vars : vsymbol list;*)
}

let int_minus = ref ps_equ
let real_minus = ref ps_equ

(** lsymbol, ""/"not ", op, rev_op *)
let arith_meta = register_meta "math arith"
  [MTlsymbol;MTstring;MTstring;MTstring]
  ~desc:"Specify@ how@ to@ pretty-print@ arithmetic@ \
          operations@ in@ the@ Mathematica@ format:@\n  \
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
    (*info_vars = [];*)
  }

(* Mathematica printing *)

let ident_printer =
  let bls = [] in (* TODO *)
  let san = sanitizer char_to_lalpha char_to_alnum in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let print_const fmt c =
  let number_format = {
    Number.long_int_support = true;
    Number.extra_leading_zeros_support = true;
    Number.negative_int_support = Number.Number_default;
    Number.dec_int_support = Number.Number_default;
    Number.hex_int_support = Number.Number_default;
    Number.oct_int_support = Number.Number_unsupported;
    Number.bin_int_support = Number.Number_unsupported;
    Number.def_int_support = Number.Number_unsupported;
    Number.negative_real_support = Number.Number_default;
    Number.dec_real_support = Number.Number_unsupported;
    Number.hex_real_support = Number.Number_unsupported;
    Number.frac_real_support =
      Number.Number_custom (Number.PrintFracReal ("%s", "(%s/%s)", "(%s/%s)"));
    Number.def_real_support = Number.Number_unsupported;
  } in
    (Number.print number_format) fmt c

let constant_value =
  fun t -> match t.t_node with
    | Tconst c ->
        asprintf "%a" print_const c
    | Tapp(ls, [{ t_node = Tconst c}])
        when ls_equal ls !int_minus || ls_equal ls !real_minus ->
        asprintf "-%a" print_const c
    | _ -> raise Not_found


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

(* terms *)

let rec print_term info fmt t =
  let term = print_term info in
  let fmla = print_fmla info in
  match t.t_node with
  | Tconst c ->
      (*Pretty.print_const fmt c*)
      print_const fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp ( { ls_name = id } ,[] ) ->
    begin match query_syntax info.info_syn id with
      | Some s -> syntax_arguments s term fmt []
      | None -> print_ident fmt id
    end
  | Tapp ( { ls_name = id } ,[t] )
      when try String.sub id.id_string 0 6 = "index_" with Invalid_argument _
        -> false ->
            fprintf fmt "%a" term t
  | Tapp (ls, tl) ->
      begin match query_syntax info.info_syn ls.ls_name with
        | Some s -> syntax_arguments s term fmt tl
        (*| None ->
            unsupportedTerm t
              ("math: function '" ^ ls.ls_name.id_string ^ "' is not supported")*)
        | None -> begin match tl with
            | [] -> fprintf fmt "%a" print_ident ls.ls_name
            | _ -> fprintf fmt "%a[%a]"
                print_ident ls.ls_name (print_list comma term) tl
          end
      end

  | Tif (f, t1, t2) ->
      fprintf fmt "If[%a,@ %a,@ %a]" fmla f term t1 term t2
  (*| Tif _ -> unsupportedTerm t
      "math: you must eliminate if_then_else"*)

  | Tlet _ -> unsupportedTerm t
      "math: you must eliminate let in term"

  | Tcase _ -> unsupportedTerm t
      "math: you must eliminate match"
  (*| Tcase (t,bl) ->
      print_case print_term info fmt t bl*)

  | Teps _ -> unsupportedTerm t
      "math: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)


(* predicates *)

(*let rec*) and print_fmla info fmt f =
  let term = print_term info in
  let fmla = print_fmla info in
  match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
    begin match query_syntax info.info_syn id with
      | Some s -> syntax_arguments s term fmt []
      | None -> fprintf fmt "%a == 0" print_ident id
    end
  | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
      (* TODO: distinguish between type of t1 and t2
         the following is OK only for real or integer
      *)
      begin try
        let c1 = constant_value t1 in
        fprintf fmt "%a == %s" term t2 c1
      with Not_found ->
        try
          let c2 = constant_value t2 in
          fprintf fmt "%a == %s" term t1 c2
        with Not_found ->
          fprintf fmt "%a - %a == 0" term t1 term t2
      end
  | Tapp (ls, [t1;t2]) when Mls.mem ls info.info_ops_of_rel ->
      let s,op,rev_op = try Mls.find ls info.info_ops_of_rel
        with Not_found -> assert false
      in
      begin try
        let t = pat_match info.info_env 3 rel_error_pat f in
        let c = constant_value t.(2) in
        fprintf fmt "|%a -/ %a| <= %s" term t.(0) term t.(1) c
      with Not_found -> try
        let c1 = constant_value t1 in
        fprintf fmt "%s%a %s %s" s term t2 rev_op c1
      with Not_found ->
        try
          let c2 = constant_value t2 in
          fprintf fmt "%s%a %s %s" s term t1 op c2
        with Not_found ->
          fprintf fmt "%s%a - %a %s 0" s term t1 term t2 op
      end
  | Tapp (ls, tl) ->
      begin match query_syntax info.info_syn ls.ls_name with
        | Some s -> syntax_arguments s term fmt tl
        | None ->
            (*unsupportedTerm f
              ("math: predicate '" ^ ls.ls_name.id_string ^ "' is not supported")*)
            begin match tl with
              | [] -> fprintf fmt "%a" print_ident ls.ls_name
              | _ -> fprintf fmt "%a[%a]"
                print_ident ls.ls_name (print_list comma (print_term info)) tl
            end
      end
  (*| Tquant _ ->
      unsupportedTerm f "math: quantifiers are not supported"*)
  (*| Tquant (Tforall, fq) ->
      let vl, _tl, f = t_open_quant fq in
        info.info_vars <- List.append info.info_vars vl;
        fprintf fmt "%a" fmla f*)
  | Tquant (Tforall, fq) ->
      let vl, _tl, f = t_open_quant fq in
      let var fmt v = (* TODO: type check v.vs_ty *)
        print_ident fmt v.vs_name in
        fprintf fmt "ForAll[{%a}, %a]" (print_list comma var) vl fmla f
  | Tquant (Texists, fq) ->
      let vl, _tl, f = t_open_quant fq in
      let var fmt v = (* TODO: type check v.vs_ty *)
        print_ident fmt v.vs_name in
        fprintf fmt "Exists[{%a}, %a]" (print_list comma var) vl fmla f
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "(%a &&@ %a)" fmla f1 fmla f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "(%a ||@ %a)" fmla f1 fmla f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "Implies[%a,@ %a]" fmla f1 fmla f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "Equivalent[%a,@ %a]" fmla f1 fmla f2
  | Tnot f ->
      fprintf fmt "Not[%a]" fmla f
  | Ttrue ->
      fprintf fmt "True"
  | Tfalse ->
      fprintf fmt "False"
  | Tif (f1, f2, f3) ->
      fprintf fmt "If[%a,@ %a,@ %a]" fmla f1 fmla f2 fmla f3
  | Tlet _ -> unsupportedTerm f
      "math: you must eliminate let in formula"

  | Tcase _ -> unsupportedTerm f
      "math: you must eliminate match"
  (*| Tcase (t,bl) ->
      print_case print_fmla info fmt t bl*)

  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)


exception AlreadyDefined

(* TODO *)
let is_number = function
  | Tyapp (ts, _) ->
      ts.ts_name.id_string = "int" || ts.ts_name.id_string = "real"
  | _ -> false


let filter_logic info ((params,funs,preds,types) as acc) (ls,ld) =
  if (not (Mid.mem ls.ls_name info.info_symbols)) then
    match ls.ls_args, ls.ls_value with
    | _, Some _ty (*when is_number ty.ty_node*) -> (* functions *)
      (params,(ls,ld)::funs,preds,types)

    | _, None -> (* predicates *)
      (params,funs,(ls,ld)::preds,types)

    (*| _, _, None -> (* funs/preds without definitions *)
        (*unsupported "math: funs/preds without definitions"*)
        acc *)
  else acc


let rec filter_hyp info params defs eqs hyps pr f =
  match f.t_node with
  | Tapp(ls,[t1;t2]) when ls == ps_equ -> (* parameter definition *)
      let try_equality t1 t2 =
        match t1.t_node with
          | Tapp(l,[]) ->
              if Hid.mem defs l.ls_name then raise AlreadyDefined;
              Hid.add defs l.ls_name ();
              t_s_fold (fun _ _ -> ()) (fun _ ls ->
                  Hid.replace defs ls.ls_name ()) () t2;
              (* filters out the defined parameter *)
              let params = List.filter (fun p -> p.ls_name <> l.ls_name) params
              in
              (params, (pr,t1,t2)::eqs, hyps)
          | _ -> raise AlreadyDefined in
      begin try
        try_equality t1 t2
      with AlreadyDefined -> try
        try_equality t2 t1
      with AlreadyDefined ->
        (params, eqs, (pr,f)::hyps)
      end
  | Tbinop (Tand, f1, f2) ->
      let (params,eqs,hyps) = filter_hyp info params defs eqs hyps pr f2 in
      filter_hyp info params defs eqs hyps pr f1
  | Tapp(_,[]) ->
      (* Discard (abstracted) predicate variables.
         While Mathematica would handle them, it is usually just noise from
         Mathematica's point of view and better delegated to a SAT solver. *)
      (params,eqs,hyps)
  | Ttrue -> (params,eqs,hyps)
  | _ ->
      (params, eqs, (pr,f)::hyps)

type filter_goal =
  | Goal_good of Decl.prsymbol * term
  | Goal_bad of string
  | Goal_none

let filter_goal pr f =
  match f.t_node with
    | Tapp(ps,[]) ->
        Goal_bad ("symbol " ^ ps.ls_name.Ident.id_string ^ " unknown")
        (* todo: filter more goals *)
    | _ ->
        Goal_good(pr,f)


let prepare info defs ((params,funs,preds,eqs,hyps,goal,types) as acc) d =
  match d.d_node with
    (*| Dtype [ts, Talgebraic csl] ->
        (params,funs,preds,eqs,hyps,goal,(ts,csl)::types)*)
    (*| Dtype [ts, Tabstract] ->
        printf "abst type: %a@\n" print_ident ts.ts_name;
        if Mid.mem ts.ts_name types then acc else
        let types = Mid.add (ts.ts_name,[]) types in
          (params,funs,preds,eqs,hyps,goal,types)*)
    | Dtype _ -> acc

    | Dparam ls ->
        begin match ls.ls_args, ls.ls_value with
          | [], Some ty -> if is_number ty.ty_node then (* params *)
              (ls::params,funs,preds,eqs,hyps,goal,types)
            else
              acc
          | _ -> acc
        end

    | Dlogic dl ->
        (* TODO *)
        let (params,funs,preds,types) = List.fold_left
          (filter_logic info) (params,funs,preds,types) dl
        in (params,funs,preds,eqs,hyps,goal,types)
    | Dprop (Paxiom, pr, f) ->
        let (params,eqs,hyps) = filter_hyp info params defs eqs hyps pr f in
        (params,funs,preds,eqs,hyps,goal,types)
    | Dprop (Pgoal, pr, f) ->
        begin
          match goal with
            | Goal_none ->
                let goal = filter_goal pr f in
                (params,funs,preds,eqs,hyps,goal,types)
            | _ -> assert false
        end

    | Dind _ ->
        unsupportedDecl d
          "please remove inductive definitions before calling Mathematica printer"
    | Dprop (Plemma, _, _) ->
        unsupportedDecl d
          "math: lemmas are not supported"

    | _ -> acc

let print_equation info fmt (pr,t1,t2) =
  (* TODO *)
  fprintf fmt "(* equation '%a'*)@\n" print_ident pr.pr_name;
  fprintf fmt "%a = %a;@\n" (print_term info) t1 (print_term info) t2

let print_logic_binder _info fmt v =
  fprintf fmt "%a_" print_ident v.vs_name

let print_fun_def info fmt (ls,ld) =
  let vl,e = open_ls_defn ld in
    fprintf fmt "(* function '%a' *)@\n" print_ident ls.ls_name;
    fprintf fmt "@[<hov 2>%a[%a] :=@ %a;@]@\n@\n"
      print_ident ls.ls_name
      (print_list comma (print_logic_binder info)) vl
      (print_term info) e

let print_pred_def info fmt (ls,ld) =
  let vl,e = open_ls_defn ld in
    fprintf fmt "(* predicate '%a'*)@\n" print_ident ls.ls_name;
    fprintf fmt "@[<hov 2>%a[%a] :=@ %a;@]@\n"
      print_ident ls.ls_name
      (print_list comma (print_logic_binder info)) vl
      (print_fmla info) e;
    (*if String.sub ls.ls_name.id_string 0 8 = "index_c_" then
      fprintf fmt "@[<hov 2>%a[];@]@\n" print_ident ls.ls_name;*)
    fprintf fmt "@\n"

let print_type_def _info fmt (ts,csl) =
  fprintf fmt "(* algebraic type %a*)@\n" print_ident ts.ts_name;

  let alen = List.length csl in
  let print_def fmt () =
    if alen >= 1 then begin
      fprintf fmt "x = 1";
      for i = 2 to alen do
        fprintf fmt " || x = %d" i
      done end
    else ()
  in
    fprintf fmt "Is%a[x_] := %a;@\n" print_ident ts.ts_name
      print_def ();

  let print_args fmt () =
    for i = 1 to alen do
      fprintf fmt ", v%d" i done in
  let rec print_case fmt n =
    if n > 1 then
      fprintf fmt "If[x == %d, v%d, %a]" n n print_case (n-1)
    else
      fprintf fmt "If[x == 1, v1, 0]"
  in
    fprintf fmt "Match%a[x_%a] := %a;@\n" print_ident ts.ts_name
      print_args () print_case alen

let print_hyp info fmt (pr,f) =
  fprintf fmt "(* hypothesis '%a' *)@\n" print_ident pr.pr_name;
  fprintf fmt "%a \\[Implies]@\n" (print_fmla info) f

let is_integer = function
  | Tyapp (ts, _) ->
      ts.ts_name.id_string = "int"
  | _ -> false

let print_dom _info fmt lsymbol =
  match lsymbol.ls_value with
  (* TODO: algebraic types *)
  | Some ty when is_integer ty.ty_node ->
      fprintf fmt "Element[%a,Integers] &&@\n" print_ident lsymbol.ls_name
      (*unsupportedType ty "math: integers are not supported"*)
  | _ -> ()

let print_param _info fmt lsymbol =
  fprintf fmt "%a" print_ident lsymbol.ls_name

let print_var info fmt vsymbol =
  (*fprintf fmt "%a" print_ident vsymbol.vs_name*)
  begin match query_syntax info.info_syn vsymbol.vs_name with
    | Some s -> syntax_arguments s (print_term info) fmt []
    | None -> print_ident fmt vsymbol.vs_name
  end

let print_goal info fmt g =
  match g with
    | Goal_good(pr,f) ->
        fprintf fmt "(* goal '%a' *)@\n" print_ident pr.pr_name;
        fprintf fmt "%a@\n" (print_fmla info) f
    | Goal_bad msg ->
        fprintf fmt "(* unsupported kind of goal: %s *)@\n" msg;
        fprintf fmt "False@\n"
    | Goal_none ->
        fprintf fmt "(* no goal at all ?? *)@\n";
        fprintf fmt "False@\n"


let print_task args ?old:_ fmt task =
  forget_all ident_printer;
  let info = get_info args.env task in
  print_prelude fmt (List.append args.prelude ["$MaxExtraPrecision = 256;\
  ClearAll[vcWhy,varsWhy,resWhy];"]);
  print_th_prelude task fmt args.th_prelude;
  let params,funs,preds,eqs,hyps,goal,types =
    List.fold_left (prepare info (Hid.create 17)) ([],[],[],[],[],Goal_none,[])
    (Task.task_decls task)
  in
  List.iter (print_equation info fmt) (List.rev eqs);
  List.iter (print_fun_def  info fmt) (List.rev funs);
  List.iter (print_pred_def info fmt) (List.rev preds);
  List.iter (print_type_def info fmt) (List.rev types);
  fprintf fmt
    "@[<hov 2>vcWhy = %a(%a%a);@]@\n"
    (print_list nothing (print_hyp info)) (List.rev hyps)
    (*"@[<hov 2>vcWhy = (@\n%a%a@,);@]@\n" *)
    (print_list nothing (print_dom info)) params
    (print_goal info) goal;

  (*fprintf fmt "@[<hov 2>varsWhy = {%a%s@ %a};@]@\n" *)
  fprintf fmt "@[<hov 2>varsWhy = {%a};@]@\n"
    (print_list simple_comma (print_param info)) params;
    (*(if List.length params = 0 then "" else ",")
    (print_list simple_comma (print_var   info)) info.info_vars;*)

  fprintf fmt "@[<hov 2>resWhy = FullSimplify[vcWhy];@]@\n";
  fprintf fmt "@[<hov 2>If[resWhy, Print[True], Print[False],@,";
  fprintf fmt "resWhy = FindInstance[Not[resWhy],varsWhy,Reals];@,";
  fprintf fmt "@[<hov 2>If[Head[resWhy]==List&&Length[resWhy]==0,@,";
  fprintf fmt "Print[True],@,";
  fprintf fmt "resWhy = Reduce[vcWhy,varsWhy,Reals];@,";
  fprintf fmt "If[resWhy, Print[True], Print[False], Print[resWhy]] ]@] ];@]"
  (*fprintf fmt "@[<hov 2>Quit[];@]@\n"*)
(*
  print_decls ?old info fmt (Task.task_decls task)
*)

let () = register_printer "mathematica" print_task
  ~desc:"Printer@ for@ the@ Mathematica@ specialized@ in@ computational@ algebla."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
