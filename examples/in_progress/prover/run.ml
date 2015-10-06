
open Firstorder_symbol_impl__Types
open Firstorder_term_impl__Types
open Firstorder_formula_impl__Types
open Firstorder_formula_list_impl__Types

open Format

let pr_symbol fmt s =
  match s with
  | NLFVar_symbol v ->
    fprintf fmt "f%s" (Why3extract.Why3__BigInt.to_string v)
  | NLBruijn_symbol n ->
    fprintf fmt "v%s" (Why3extract.Why3__BigInt.to_string n)

let rec pr_term fmt t =
  match t with
  | NLFVar_fo_term v ->
    fprintf fmt "f%s" (Why3extract.Why3__BigInt.to_string v)
  | NLBruijn_fo_term n ->
    fprintf fmt "v%s" (Why3extract.Why3__BigInt.to_string n)
  | NL_App(s,tl) ->
    fprintf fmt "%a%a" pr_symbol s pr_term_list tl

and pr_term_list fmt tl =
  match tl with
  | NL_FONil -> fprintf fmt "()"
  | NL_FOCons(t,tl) ->
      fprintf fmt "@[<hov 2>(%a%a)@]" pr_term t pr_term_list_tail tl

and pr_term_list_tail fmt tl =
  match tl with
    | NL_FONil -> ()
    | NL_FOCons(t,tl) ->
      fprintf fmt ",@ %a%a" pr_term t pr_term_list_tail tl

let pr_term_impl fmt t = pr_term fmt t.nlrepr_fo_term_field

let rec pr_formula fmt f =
  match f with
  | NL_Forall f -> fprintf fmt "@[<hov 2>(forall@ %a)@]" pr_formula f
  | NL_Exists f  -> fprintf fmt "@[<hov 2>(exists@ %a)@]" pr_formula f
  | NL_And(f1,f2) ->
    fprintf fmt "@[<hov 2>(%a@ and %a)@]" pr_formula f1 pr_formula f2
  | NL_Or(f1,f2) ->
    fprintf fmt "@[<hov 2>(%a@ or %a)@]" pr_formula f1 pr_formula f2
  | NL_Not f -> fprintf fmt "@[<hov 2>(not@ %a)@]" pr_formula f
  | NL_FTrue -> fprintf fmt "true"
  | NL_FFalse -> fprintf fmt "false"
  | NL_PApp(s,tl) ->
    fprintf fmt "@[<hov 2>%a%a@]" pr_symbol s pr_term_list tl

and pr_formula_list fmt l =
  match l with
  | NL_FOFNil -> fprintf fmt "[]"
  | NL_FOFCons(f,l) ->
    fprintf fmt "@[<hov 2>[ %a%a ]@]" pr_formula f pr_formula_list_tail l

and pr_formula_list_tail fmt l =
  match l with
  | NL_FOFNil -> ()
  | NL_FOFCons(f,l) ->
    fprintf fmt ";@ %a%a" pr_formula f pr_formula_list_tail l

let pr_formula_impl fmt f = pr_formula fmt f.nlrepr_fo_formula_field

let pr_formula_list_impl fmt l =
  pr_formula_list fmt l.nlrepr_fo_formula_list_field

let n = Why3extract.Why3__BigInt.of_int

let run_test name l =
  Format.printf "Running the test '%s'@." name;
  Format.printf "Formulas: %a@." pr_formula_list_impl l;
  let t = Unix.gettimeofday () in
  let n = ProverMain__Impl.main l (n 1) in
  let t = Unix.gettimeofday () -. t in
  Format.printf "Unsat (time = %.02f, depth=%s)@.@." t
                (Why3extract.Why3__BigInt.to_string n)

let run_all_tests () =
  run_test "drinker" (ProverTest__Impl.drinker ());
  run_test "group" (ProverTest__Impl.group ());
  run_test "bidon1" (ProverTest__Impl.bidon1 ());
  run_test "bidon2" (ProverTest__Impl.bidon2 ());
  run_test "bidon3" (ProverTest__Impl.bidon3 ());
  run_test "bidon4" (ProverTest__Impl.bidon4 ());
  run_test "pierce" (ProverTest__Impl.pierce ());
  run_test "zenon5" (ProverTest__Impl.zenon5 ());
(* too long -> sat ?
  run_test "zenon6" (ProverTest__Impl.zenon6 ());
*)
  run_test "zenon10 2" (ProverTest__Impl.zenon10 (n 2));
(* too long -> sat !
  run_test "zenon10 3" (ProverTest__Impl.zenon10 (n 3))
*)
  run_test "zenon10 4" (ProverTest__Impl.zenon10 (n 4));
  run_test "zenon10 6" (ProverTest__Impl.zenon10 (n 6));
  run_test "zenon10 8" (ProverTest__Impl.zenon10 (n 8));
  run_test "zenon10 10" (ProverTest__Impl.zenon10 (n 10));
  run_test "zenon10 12" (ProverTest__Impl.zenon10 (n 12));
(* warning: the following needs around 6 minutes *)
(*
  run_test "zenon10 14" (ProverTest__Impl.zenon10 (n 14));
*)
  printf "End of tests.@."

open Tptp_ast

exception Unsupported of string

let unsupported s = raise (Unsupported s)

exception Ill_Typed of string

let ill_typed s = raise (Ill_Typed s)

let mk_not f =
  let o = Firstorder_formula_impl__Types.NLC_Not f in
  Firstorder_formula_impl__Impl.construct_fo_formula o

type env =
  { cnf : bool;
    var_cnt : Why3extract.Why3__BigInt.t;
    var_assoc : (string * Why3extract.Why3__BigInt.t) list;
    sym_cnt : Why3extract.Why3__BigInt.t;
    sym_assoc : (string * Why3extract.Why3__BigInt.t) list }

let find_var env v =
  try
    let n = List.assoc v env.var_assoc in
    env,n
  with Not_found ->
    if env.cnf then
      let n = env.var_cnt in
      { env with
        var_cnt = Why3extract.Why3__BigInt.succ n;
        var_assoc = (v,n)::env.var_assoc }, n
    else
      ill_typed ("unknown variable id " ^ v)

let add_var env (v,_ty) =
  let n = env.var_cnt in
  { env with
    var_cnt = Why3extract.Why3__BigInt.succ n;
    var_assoc = (v,n)::env.var_assoc }, n

let find_sym env s =
  try
    let n = List.assoc s env.sym_assoc in
    env,n
  with Not_found ->
    let n = env.sym_cnt in
    { env with
      sym_cnt = Why3extract.Why3__BigInt.succ n;
      sym_assoc = (s,n)::env.sym_assoc }, n

let rec tr_term env e =
  match e.e_node with
  | Elet(e1,e2) -> unsupported "let"
  | Eite(e1,e2,e3) -> unsupported "ite"
  | Eqnt(q,vl,e) -> ill_typed "quantifier in term"
  | Ebin(op,e1,e2) -> ill_typed "bin op in term"
  | Enot e -> ill_typed "'not' in term"
  | Eequ(e1,e2) -> ill_typed "'equ' in term"
  | Eapp(w,el) ->
    let fotnil =
      let o = Firstorder_term_impl__Types.NLC_FONil in
      Firstorder_term_impl__Impl.construct_fo_term_list o
    in
    let env,tl =
      List.fold_right
        (fun e (env,acc) ->
          let env,t = tr_term env e in
          let o = Firstorder_term_impl__Types.NLC_FOCons (t, acc) in
          (env,Firstorder_term_impl__Impl.construct_fo_term_list o))
        el
        (env,fotnil)
    in
    let env,sym = find_sym env w in
    let o = Firstorder_symbol_impl__Types.NLCVar_symbol sym in
    let sym = Firstorder_symbol_impl__Impl.construct_symbol o in
    let o = Firstorder_term_impl__Types.NLC_App (sym, tl) in
    env,Firstorder_term_impl__Impl.construct_fo_term o
  | Edef(w,el) -> unsupported "def"
  | Edob d -> unsupported "dob"
  | Enum n -> unsupported "num"
  | Evar v ->
    let env,v = find_var env v in
    let o =
      Firstorder_term_impl__Types.NLCVar_fo_term v
    in
    env,Firstorder_term_impl__Impl.construct_fo_term o

let rec mk_bin_op op phi1 phi2 =
  let phi =
    match op with
    | BOequ -> unsupported "BOequ"
    | BOnequ -> unsupported "BOnequ"
    | BOimp ->
      Firstorder_formula_impl__Types.NLC_Or (mk_not phi1, phi2)
    | BOpmi -> unsupported "BOpmi"
    | BOand ->  Firstorder_formula_impl__Types.NLC_And (phi1, phi2)
    | BOor -> Firstorder_formula_impl__Types.NLC_Or (phi1, phi2)
    | BOnand ->
      Firstorder_formula_impl__Types.NLC_Not (mk_bin_op BOand phi1 phi2)
    | BOnor ->
      Firstorder_formula_impl__Types.NLC_Not (mk_bin_op BOor phi1 phi2)
  in
  Firstorder_formula_impl__Impl.construct_fo_formula phi

let rec tr_fmla env e =
  match e.e_node with
  | Elet(e1,e2) -> unsupported "let"
  | Eite(e1,e2,e3) -> unsupported "ite"
  | Eqnt(q,vl,e) ->
    let env1,nl =
      List.fold_right
        (fun v (env,vl) ->
          let env,n = add_var env v in
          (env,n::vl))
        vl (env,[])
    in
    let env2,phi = tr_fmla env1 e in
    (* suppressing quantified variables from the env *)
    let env =
      { env2 with var_cnt = env.var_cnt; var_assoc = env.var_assoc }
    in
    let phi = match q with
      | Qforall ->
        List.fold_right
          (fun n phi ->
            let o =
              Firstorder_formula_impl__Types.NLC_Forall (n,phi)
            in
            Firstorder_formula_impl__Impl.construct_fo_formula o)
          nl phi
      | Qexists ->
        List.fold_right
          (fun n phi ->
            let o =
              Firstorder_formula_impl__Types.NLC_Exists (n,phi)
            in
            Firstorder_formula_impl__Impl.construct_fo_formula o)
          nl phi
    in env, phi
  | Ebin(op,e1,e2) ->
    let env1,phi1 = tr_fmla env e1 in
    let env2,phi2 = tr_fmla env1 e2 in
    env2, mk_bin_op op phi1 phi2
  | Enot e ->
    let env1,phi1 = tr_fmla env e in
    env1,mk_not phi1
  | Eequ(e1,e2) -> unsupported "equ"
  | Eapp(w,el) ->
    let fotnil =
      let o = Firstorder_term_impl__Types.NLC_FONil in
      Firstorder_term_impl__Impl.construct_fo_term_list o
    in
    let env,tl =
      List.fold_right
        (fun e (env,acc) ->
          let env,t = tr_term env e in
          let o = Firstorder_term_impl__Types.NLC_FOCons (t, acc) in
          (env,Firstorder_term_impl__Impl.construct_fo_term_list o))
        el
        (env,fotnil)
    in
    let env,sym = find_sym env w in
    let o = Firstorder_symbol_impl__Types.NLCVar_symbol sym in
    let sym = Firstorder_symbol_impl__Impl.construct_symbol o in
    let o = Firstorder_formula_impl__Types.NLC_PApp (sym, tl) in
    env,Firstorder_formula_impl__Impl.construct_fo_formula o
  | Edef(DP(DPfalse),[]) ->
     let o =
      Firstorder_formula_impl__Types.NLC_FFalse
    in
    env,Firstorder_formula_impl__Impl.construct_fo_formula o
  | Edef(w,el) -> unsupported "def"
  | Edob d -> unsupported "dob"
  | Enum n -> unsupported "num"
  | Evar v -> ill_typed "var in formula"

let tr_cnf env e =
  let rec tr env e =
    match e.e_node with
    | Elet(e1,e2) -> unsupported "let in cnf"
    | Eite(e1,e2,e3) -> unsupported "ite in cnf"
    | Eqnt(q,vl,e) -> unsupported "qnt in cnf"
    | Ebin(op,e1,e2) ->
      let env1,phi1 = tr env e1 in
      let env2,phi2 = tr env1 e2 in
      env2, mk_bin_op op phi1 phi2
    | Enot e ->
      let env1,phi1 = tr env e in
      env1,mk_not phi1
    | Eequ(e1,e2) -> unsupported "equ"
    | Eapp(w,el) ->
      let fotnil =
        let o = Firstorder_term_impl__Types.NLC_FONil in
        Firstorder_term_impl__Impl.construct_fo_term_list o
      in
      let env,tl =
        List.fold_right
          (fun e (env,acc) ->
            let env,t = tr_term env e in
            let o = Firstorder_term_impl__Types.NLC_FOCons (t, acc) in
            (env,Firstorder_term_impl__Impl.construct_fo_term_list o))
          el
          (env,fotnil)
      in
      let env,sym = find_sym env w in
      let o = Firstorder_symbol_impl__Types.NLCVar_symbol sym in
      let sym = Firstorder_symbol_impl__Impl.construct_symbol o in
      let o = Firstorder_formula_impl__Types.NLC_PApp (sym, tl) in
      env,Firstorder_formula_impl__Impl.construct_fo_formula o
    | Edef(w,el) -> unsupported "def in cnf"
    | Edob d -> unsupported "dob in cnf"
    | Enum n -> unsupported "num in cnf"
    | Evar v -> ill_typed "var in cnf"
  in
  let env,phi = tr env e in
  let phi =
    List.fold_right
      (fun (_,n) phi ->
        let o =
          Firstorder_formula_impl__Types.NLC_Forall (n,phi)
        in
        Firstorder_formula_impl__Impl.construct_fo_formula o)
      env.var_assoc phi
  in
  { env with
    var_cnt = Why3extract.Why3__BigInt.zero;
    var_assoc = [] }, phi

let empty_env () =
{ cnf = false;
  var_cnt = Why3extract.Why3__BigInt.zero;
  var_assoc = [];
  sym_cnt = Why3extract.Why3__BigInt.zero;
  sym_assoc = [] }

let tr_top_formula env kind role f =
  match f with
  | TypedAtom _ -> unsupported "TypedAtom"
  | Sequent _ -> unsupported "Sequent"
  | LogicFormula e ->
    let env,f =
      match kind with
      | FOF -> tr_fmla { env with cnf = false } e
      | CNF -> (* assert false *) tr_cnf { env with cnf = true } e
      | TFF -> assert false
    in
    let phi =
      match role with
      | Axiom -> f
      | Hypothesis -> f
      | Definition -> unsupported "Definition"
      | Assumption -> f
      | Corollary -> unsupported "corollary" (* mk_not f ? *)
      | Lemma -> unsupported "lemma" (* mk_not f ? *)
      | Theorem -> unsupported "theorem" (* mk_not f ? *)
      | Conjecture -> mk_not f
      | Negated_conjecture -> f
      | Type -> unsupported "Type"
    in env,phi

let tr_decl (env,acc) d =
  match d with
  | Include _ -> unsupported "Include"
  | Formula(TFF,_,role,top_formula,_) -> unsupported "TFF"
  | Formula(CNF,_,role,top_formula,_) -> unsupported "CNF"
  | Formula(kind,_,role,top_formula,_) ->
    let env,phi = tr_top_formula env kind role top_formula in
    let o = Firstorder_formula_list_impl__Types.NLC_FOFCons (phi, acc) in
    let acc = Firstorder_formula_list_impl__Impl.construct_fo_formula_list o in
    env,acc

let tr_file a =
  let fonil =
    let o = Firstorder_formula_list_impl__Types.NLC_FOFNil in
    Firstorder_formula_list_impl__Impl.construct_fo_formula_list o
  in
  List.fold_left tr_decl (empty_env (),fonil) a

(*** output in FOF format *)

let comma fmt () = fprintf fmt ",@ "

let rec print_list_pre sep print fmt = function
  | [] -> ()
  | x :: r -> sep fmt (); print fmt x; print_list_pre sep print fmt r

let print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; print_list_pre sep print fmt r

let pr_var fmt (v,_) = pp_print_string fmt v

let rec pr_fof_expr fmt e =
  match e.e_node with
  | Elet(e1,e2) -> unsupported "let"
  | Eite(e1,e2,e3) -> unsupported "ite"
  | Eqnt(q,vl,e) ->
     let q = match q with Qforall -> "!" | Qexists -> "?" in
     fprintf fmt "@[(%s[%a]:@ %a)@]" q
        (print_list comma pr_var) vl pr_fof_expr e
  | Ebin(op,e1,e2) ->
     let s = match op with
       | BOand -> "&" | BOor -> "|" | BOimp -> "=>"
       | _ -> unsupported "binop"
     in
     fprintf fmt "@[(%a@ %s %a)@]" pr_fof_expr e1 s pr_fof_expr e2
  | Enot e -> fprintf fmt "~@ %a" pr_fof_expr e
  | Eequ(e1,e2) -> unsupported "equ"
  | Eapp(w,[]) -> fprintf fmt "%s" w
  | Eapp(w,el) ->
     fprintf fmt "@[%s(%a)@]" w (print_list comma pr_fof_expr) el
  | Edef(w,el) -> unsupported "def"
  | Edob d -> unsupported "dob"
  | Enum n -> unsupported "num"
  | Evar v -> fprintf fmt "%s" v

let rec add x l =
  match l with
  | [] -> [x]
  | y :: r as l -> if x = y then l else y :: add x r

let get_vars e =
  let rec aux env e =
    match e.e_node with
    | Elet(e1,e2) -> unsupported "let"
    | Eite(e1,e2,e3) -> unsupported "ite"
    | Eqnt(q,vl,e) -> unsupported "quant in cnf"
    | Ebin(op,e1,e2) -> aux (aux env e1) e2
    | Enot e -> aux env e
    | Eequ(e1,e2) -> unsupported "equ"
    | Eapp(w,el) -> List.fold_left aux env el
    | Edef(w,el) -> unsupported "def"
    | Edob d -> unsupported "dob"
    | Enum n -> unsupported "num"
    | Evar v -> add v env
  in
  aux [] e

let pr_role fmt r =
  match r with
  | Axiom -> fprintf fmt "axiom"
  | Hypothesis -> fprintf fmt "hypothesis"
  | Definition -> unsupported "Definition"
  | Assumption -> fprintf fmt "assumption"
  | Corollary -> unsupported "corollary"
  | Lemma -> unsupported "lemma"
  | Theorem -> unsupported "theorem"
  | Conjecture -> fprintf fmt "conjecture"
  | Negated_conjecture -> fprintf fmt "negated_conjecture"
  | Type -> unsupported "Type"

let pr_fof_top_formula fmt name kind role f =
  match f with
  | TypedAtom _ -> unsupported "TypedAtom"
  | Sequent _ -> unsupported "Sequent"
  | LogicFormula e ->
     match kind with
     | FOF -> fprintf fmt "@[fof(%s,@ %a,@ %a).@]@\n"
                      name pr_role role pr_fof_expr e
     | CNF ->
        let r = match role with
          | Conjecture -> unsupported "conjecture in CNF format"
          | Negated_conjecture -> Axiom
          | Axiom -> role
          | Hypothesis -> role
          | Definition | Assumption
          | Corollary|Lemma|Theorem|Type -> unsupported "role"
        in
        begin
          match get_vars e with
          | [] -> fprintf fmt "@[fof(%s,@ %a,@ %a).@]@\n"
                          name pr_role r pr_fof_expr e
          | l -> fprintf fmt "@[fof(%s,@ %a,@ (![%a]: %a)).@]@\n"
                         name pr_role r
                         (print_list comma pp_print_string) l
                         pr_fof_expr e
        end
     | TFF -> assert false

let pr_fof_decl fmt k d =
  match d with
  | Include _ -> unsupported "Include"
  | Formula(TFF,_,role,top_formula,_) -> unsupported "TFF"
  | Formula(kind,name,role,top_formula,_) ->
    pr_fof_top_formula fmt name kind role top_formula;
    match k with
    | None -> Some kind
    | Some k' -> if k'=kind then k else unsupported "mixed CNF/FOF"


let pr_fof fmt a =
  let k = List.fold_left (pr_fof_decl fmt) None a in
  match k with
  | Some CNF ->
    fprintf fmt "fof(contradiction,conjecture,$false).@."
  | None -> unsupported "empty file ??"
  | _ -> fprintf fmt "@."

let run_file ~print file =
  try
    let ast = Tptp_lexer.load file in
    printf "File '%s': parsing OK.@." file;
    if print then
      begin
        let ch = open_out "tmp.p" in
        let fmt = formatter_of_out_channel ch in
        pr_fof fmt ast;
        close_out ch
      end
    else
      let _,l = tr_file ast in
      run_test (Filename.basename file) l;
    exit 0
  with
  | Tptp_lexer.FileNotFound f ->
    eprintf "File not found: %s@." f; exit 2
  | Unsupported s ->
      eprintf "File %s: '%s' is not supported@." file s; exit 1
  | e ->
    eprintf "Parsing error: %a@." Why3.Exn_printer.exn_printer e;
    exit 2

let () =
  printf "The safe prover, version 0.0.1@.";
  if Array.length Sys.argv = 1 then run_all_tests ()
  else
    try
      let arg = Sys.argv.(1) in
      match arg with
      | "-version" -> exit 0
      | "-print" ->
         if Array.length Sys.argv <> 3 then raise Exit;
         run_file ~print:true Sys.argv.(2)
      | _ ->
         if Array.length Sys.argv <> 2 then raise Exit;
         run_file ~print:false arg
    with Exit ->
      begin
        eprintf "Usage: %s [options] [file]@\n\
                  -version: prints the version@\n\
                  -print  : reprints the file in TPTP/FOF without includes@\n\
                 Internal tests are run if no file is given@."
                Sys.argv.(0);
        exit 2
      end
