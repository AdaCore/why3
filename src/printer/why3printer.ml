(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Why3 printer *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer
open Theory
open Task

(* Labels and locations can be printed by setting the appropriate flags *)
let debug_print_labels = Debug.register_info_flag "print_labels"
  ~desc:"Print@ labels@ of@ identifiers@ and@ expressions."

let debug_print_locs = Debug.register_info_flag "print_locs"
  ~desc:"Print@ locations@ of@ identifiers@ and@ expressions."

let id_unique tables id = id_unique_label tables.printer id

(*
let forget_tvs () =
  forget_all aprinter

let _forget_all () =
  forget_all iprinter;
  forget_all aprinter;
  forget_all tprinter;
  forget_all pprinter
*)

(* type variables always start with a quote *)
let print_tv tables fmt tv =
  fprintf fmt "'%s" (id_unique tables tv.tv_name)

(* logic variables always start with a lower case letter *)
let print_vs tables fmt vs =
  fprintf fmt "%s" (id_unique tables vs.vs_name)

let forget_var tables vs = forget_id tables.printer vs.vs_name

(* theory names always start with an upper case letter *)
let print_th tables fmt th =
  fprintf fmt "%s" (id_unique tables th.th_name)

let print_ts tables fmt ts =
  fprintf fmt "%s" (id_unique tables ts.ts_name)

let print_ls tables fmt ls =
  fprintf fmt "%s" (id_unique tables ls.ls_name)

let print_cs tables fmt ls =
  fprintf fmt "%s" (id_unique tables ls.ls_name)

let print_pr tables fmt pr =
  fprintf fmt "%s" (id_unique tables pr.pr_name)

(* info *)

type info = { info_syn : syntax_map ; itp : bool; }

let info = ref { info_syn = Mid.empty ; itp = false ; }

let query_syntax id = query_syntax !info.info_syn id
let query_remove id = Mid.mem id !info.info_syn

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_ty_node inn tables fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv tables fmt v
  | Tyapp (ts, tl) -> begin match query_syntax ts.ts_name with
      | Some s -> syntax_arguments s (print_ty_node false tables) fmt tl
      | None -> begin match tl with
          | [] -> print_ts tables fmt ts
          | tl -> fprintf fmt (protect_on inn "%a@ %a")
              (print_ts tables) ts (print_list space (print_ty_node true tables)) tl
          end
      end

let print_ty = print_ty_node false

(*
let print_vsty tables fmt v =
  fprintf fmt "%a:@,%a" (print_vs tables) v (print_ty tables) v.vs_ty
 *)

(** Forgetting function for stability of errors *)
let print_forget_vsty tables fmt v =
  if (Ident.known_id tables.printer v.vs_name) then
    fprintf fmt "%a:@,%a" (print_vs tables) v (print_ty tables) v.vs_ty
  else
    begin
      fprintf fmt "%a:@,%a" (print_vs tables) v (print_ty tables) v.vs_ty;
      forget_var tables v
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
  Opt.fold (fun _ -> inspect) true fs.ls_value

(** Patterns, terms, and formulas *)

let rec print_pat_node pri tables fmt p = match p.pat_node with
  | Pwild ->
      fprintf fmt "_"
  | Pvar v ->
      print_vs tables fmt v
  | Pas (p, v) ->
      fprintf fmt (protect_on (pri > 1) "%a as %a")
        (print_pat_node 1 tables) p (print_vs tables) v
  | Por (p, q) ->
      fprintf fmt (protect_on (pri > 0) "%a | %a")
        (print_pat_node 0 tables) p (print_pat_node 0 tables) q
  | Papp (cs, pl) -> begin match query_syntax cs.ls_name with
      | Some s -> syntax_arguments s (print_pat_node 0 tables) fmt pl
      | None -> begin match pl with
          | [] -> print_cs tables fmt cs
          | pl -> fprintf fmt (protect_on (pri > 1) "%a@ %a")
              (print_cs tables) cs (print_list space (print_pat_node 2 tables)) pl
          end
      end

let print_pat = print_pat_node 0

(*
let print_const = Number.print_constant
 *)

let print_vsty tables fmt v =
  fprintf fmt "%a:@,%a" (print_vs tables) v (print_ty tables) v.vs_ty

let print_quant = Pretty.print_quant
let print_binop = Pretty.print_binop

let prio_binop = function
  | Tand -> 3
  | Tor -> 2
  | Timplies -> 1
  | Tiff -> 1

let print_label = Pretty.print_label
let print_labels = print_iter1 Slab.iter space print_label

let print_ident_labels fmt id =
  if Debug.test_flag debug_print_labels &&
    not (Slab.is_empty id.id_label) then
    fprintf fmt "@ %a" print_labels id.id_label;
  if Debug.test_flag debug_print_locs then
    Opt.iter (fprintf fmt "@ %a" Pretty.print_loc) id.id_loc

(*  if not (Slab.is_empty id.id_label) then
    fprintf fmt "@ %a" print_labels id.id_label*)

let rec print_term tables fmt t = print_lterm 0 tables fmt t

and print_lterm pri tables fmt t =
  if (Slab.is_empty t.t_label || not (Debug.test_flag debug_print_labels)) then
    print_tnode pri tables fmt t
  else fprintf fmt (protect_on (pri > 0) "%a %a")
      print_labels t.t_label (print_tnode 0 tables) t

and print_app pri fs tables fmt tl =
  match query_syntax fs.ls_name with
    | Some s -> syntax_arguments s (print_term tables) fmt tl
    | None -> begin match tl with
        | [] -> print_ls tables fmt fs
        | tl -> fprintf fmt (protect_on (pri > 5) "%a@ %a")
            (print_ls tables) fs (print_list space (print_lterm 6 tables)) tl
        end

and print_tnode pri tables fmt t = match t.t_node with
  | Tvar v ->
      print_vs tables fmt v
  | Tconst c ->
      Number.print_constant fmt c
  | Tapp (fs, tl) when unambig_fs fs ->
      print_app pri fs tables fmt tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on (pri > 0) "%a:%a")
        (print_app 5 fs tables) tl (print_ty tables) (t_type t)
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on (pri > 0) "if @[%a@] then %a@ else %a")
        (print_term tables) f (print_term tables) t1 (print_term tables) t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        (print_vs tables) v (print_lterm 4 tables) t1 (print_term tables) t2;
      forget_var tables v
  | Tcase (t1,bl) ->
      fprintf fmt "match @[%a@] with@\n@[<hov>%a@]@\nend"
        (print_term tables) t1 (print_list newline (print_tbranch tables)) bl
  | Teps fb ->
      let vl,tl,e = t_open_lambda t in
      if vl = [] then begin
        let v,f = t_open_bound fb in
        fprintf fmt (protect_on (pri > 0) "epsilon %a.@ %a")
          (print_vsty tables) v (print_term tables) f
      end else begin
        fprintf fmt (protect_on (pri > 0) "\\ %a%a.@ %a")
          (print_list comma (print_vsty tables)) vl (print_tl tables) tl (print_term tables) e
      end;
      List.iter (forget_var tables) vl
  | Tquant (q,fq) ->
      let vl,tl,f = t_open_quant fq in
      fprintf fmt (protect_on (pri > 0) "%a %a%a.@ %a") print_quant q
        (print_list comma (print_vsty tables)) vl (print_tl tables) tl (print_term tables) f;
      List.iter (forget_var tables) vl
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tbinop (b,f1,f2) ->
      let asym = Slab.mem Term.asym_label f1.t_label in
      let p = prio_binop b in
      fprintf fmt (protect_on (pri > p) "%a %a@ %a")
        (print_lterm (p + 1) tables) f1 (print_binop ~asym) b (print_lterm p tables) f2
  | Tnot f ->
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lterm 4 tables) f

and print_tbranch tables fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat tables) p (print_term tables) t;
  Svs.iter (forget_var tables) p.pat_vars

and print_tl tables fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_term tables))) tl

(** Declarations *)

let print_tv_arg tables fmt tv = fprintf fmt "@ %a" (print_tv tables) tv
let print_ty_arg tables fmt ty = fprintf fmt "@ %a" (print_ty_node true tables) ty
let print_vs_arg tables fmt vs = fprintf fmt "@ (%a)" (print_vsty tables) vs

let print_constr tables fmt (cs,pjl) =
  let add_pj pj ty pjl = (pj,ty)::pjl in
  let print_pj fmt (pj,ty) = match pj with
    | Some ls -> fprintf fmt "@ (%a:@,%a)" (print_ls tables) ls (print_ty tables) ty
    | None -> print_ty_arg tables fmt ty
  in
  fprintf fmt "@[<hov 4>| %a%a%a@]" (print_cs tables) cs
    print_ident_labels cs.ls_name
    (print_list nothing print_pj)
    (List.fold_right2 add_pj pjl cs.ls_args [])

let print_type_decl tables fmt ts = match ts.ts_def with
  | NoDef ->
      fprintf fmt "@[<hov 2>type %a%a%a@]@\n"
        (print_ts tables) ts print_ident_labels ts.ts_name
        (print_list nothing (print_tv_arg tables)) ts.ts_args
  | Alias ty ->
      fprintf fmt "@[<hov 2>type %a%a%a =@ %a@]@\n"
        (print_ts tables) ts print_ident_labels ts.ts_name
        (print_list nothing (print_tv_arg tables)) ts.ts_args (print_ty tables) ty
  | Range _ir -> (* TODO *)
      fprintf fmt "@[<hov 2>type %a%a%a =@ <range ...>@]@\n@\n"
        (print_ts tables) ts print_ident_labels ts.ts_name
        (print_list nothing (print_tv_arg tables)) ts.ts_args
  | Float _fp -> (* TODO *)
      fprintf fmt "@[<hov 2>type %a%a%a =@ <float ...>@]@\n@\n"
        (print_ts tables) ts print_ident_labels ts.ts_name
        (print_list nothing (print_tv_arg tables)) ts.ts_args

let print_type_decl tables fmt ts =
  if not (query_remove ts.ts_name) then
    (print_type_decl tables fmt ts)

let print_data_decl fst tables fmt (ts,csl) =
  fprintf fmt "@[<hov 2>%s %a%a%a =@\n@[<hov>%a@]@]@\n"
    (if fst then "type" else "with") (print_ts tables) ts
    print_ident_labels ts.ts_name
    (print_list nothing (print_tv_arg tables)) ts.ts_args
    (print_list newline (print_constr tables)) csl

let print_data_decl first tables fmt d =
  if not (query_remove (fst d).ts_name) then
    (print_data_decl first tables fmt d)

let print_ls_type tables fmt = fprintf fmt " :@ %a" (print_ty tables)

let print_ls_kind ~fst fmt ls =
  if not !info.itp then
    fprintf fmt "%s "
            (if fst then
               if ls.ls_value = None then "predicate" else "function"
             else "with")

let print_param_decl tables fmt ls =
  fprintf fmt "@[<hov 2>%a%a%a%a%a@]@\n"
    (print_ls_kind ~fst:true) ls (print_ls tables) ls
    print_ident_labels ls.ls_name
    (print_list nothing (print_ty_arg tables)) ls.ls_args
    (print_option (print_ls_type tables)) ls.ls_value

let print_param_decl tables fmt ls =
  if not (query_remove ls.ls_name) then
    (print_param_decl tables fmt ls)

let print_logic_decl fst tables fmt (ls,ld) =
  let vl,e = open_ls_defn ld in
  fprintf fmt "@[<hov 2>%a%a%a%a%a =@ %a@]@\n"
    (print_ls_kind ~fst) ls (print_ls tables) ls
    print_ident_labels ls.ls_name
    (print_list nothing (print_vs_arg tables)) vl
    (print_option (print_ls_type tables)) ls.ls_value (print_term tables) e;
  List.iter (forget_var tables) vl

let print_logic_decl first tables fmt d =
  if not (query_remove (fst d).ls_name) then
    (print_logic_decl first tables fmt d)

let print_ind tables fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a%a :@ %a@]"
    (print_pr tables) pr print_ident_labels pr.pr_name (print_term tables) f

let ind_sign = function
  | Ind   -> "inductive"
  | Coind -> "coinductive"

let print_ind_decl s fst tables fmt (ps,bl) =
  fprintf fmt "@[<hov 2>%s %a%a%a =@ @[<hov>%a@]@]@\n"
    (if fst then ind_sign s else "with") (print_ls tables) ps
    print_ident_labels ps.ls_name
    (print_list nothing (print_ty_arg tables)) ps.ls_args
    (print_list newline (print_ind tables)) bl

let print_ind_decl s first tables fmt d =
  if not (query_remove (fst d).ls_name) then
    (print_ind_decl s first tables fmt d)

let print_pkind fmt k =
  if not !info.itp then fprintf fmt "%a " Pretty.print_pkind k

let print_prop_decl tables fmt (k,pr,f) =
  fprintf fmt "@[<hov 2>%a%a%a : %a@]@\n" print_pkind k
    (print_pr tables) pr print_ident_labels pr.pr_name (print_term tables) f

let print_prop_decl tables fmt (k,pr,f) = match k with
  | Paxiom when query_remove pr.pr_name -> ()
  | _ -> print_prop_decl tables fmt (k,pr,f)

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_decl tables fmt d = match d.d_node with
  | Dtype ts  -> print_type_decl tables fmt ts
  | Ddata tl  -> print_list_next nothing (fun f -> print_data_decl f tables) fmt tl
  | Dparam ls -> print_param_decl tables fmt ls
  | Dlogic ll -> print_list_next nothing (fun f -> print_logic_decl f tables) fmt ll
  | Dind (s, il) -> print_list_next nothing (fun u -> print_ind_decl s u tables) fmt il
  | Dprop p   -> print_prop_decl tables fmt p

let print_inst_ts tables fmt (ts1,ts2) =
  fprintf fmt "type %a = %a" (print_ts tables) ts1 (print_ts tables) ts2

let print_inst_ls tables fmt (ls1,ls2) =
  fprintf fmt "%a%a = %a"
          (print_ls_kind ~fst:true) ls1 (print_ls tables) ls1 (print_ls tables) ls2

let print_inst_pr tables fmt (pr1,pr2) =
  fprintf fmt "prop %a = %a" (print_pr tables) pr1 (print_pr tables) pr2

let print_meta_arg tables fmt = function
  | MAty ty -> fprintf fmt "type %a" (print_ty tables) ty
  | MAts ts -> fprintf fmt "type %a" (print_ts tables) ts
  | MAls ls -> fprintf fmt "%a%a" (print_ls_kind ~fst:true) ls (print_ls tables) ls
  | MApr pr -> fprintf fmt "prop %a" (print_pr tables) pr
  | MAstr s -> fprintf fmt "\"%s\"" s
  | MAint i -> fprintf fmt "%d" i

let print_qt tables fmt th =
  if th.th_path = [] then print_th tables fmt th else
  fprintf fmt "%a.%a"
    (print_list (constant_string ".") string) th.th_path
    (print_th tables) th

let _print_tdecl tables fmt td = match td.td_node with
  | Decl d ->
      fprintf fmt "%a@\n" (print_decl tables) d
  | Use th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]@\n@\n" (print_qt tables) th
  | Clone (th,sm) when is_empty_sm sm ->
      fprintf fmt "@[<hov 2>(* use %a *)@]@\n@\n" (print_qt tables) th
  | Clone (th,sm) ->
      let tm = Mts.fold (fun x y a -> (x,y)::a) sm.sm_ts [] in
      let lm = Mls.fold (fun x y a -> (x,y)::a) sm.sm_ls [] in
      let pm = Mpr.fold (fun x y a -> (x,y)::a) sm.sm_pr [] in
      fprintf fmt "@[<hov 2>(* clone %a with %a,@ %a,@ %a *)@]@\n@\n"
        (print_qt tables) th (print_list comma (print_inst_ts tables)) tm
                    (print_list comma (print_inst_ls tables)) lm
                    (print_list comma (print_inst_pr tables)) pm
  | Meta (m,al) ->
      fprintf fmt "@[<hov 2>(* meta %s %a *)@]@\n@\n"
        m.meta_name (print_list comma (print_meta_arg tables)) al

(*
let print_tdecls tables =
  let print_tdecl sm tables fmt td =
    info := {info_syn = sm; itp = false}; print_tdecl tables fmt td; sm, [] in
  let print_tdecl tables = Printer.sprint_tdecl (fun sm -> print_tdecl sm tables) in
  let print_tdecl tables task acc = print_tdecl tables task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm -> Trans.fold (print_tdecl tables) (sm,[]))
*)

(* TODO print_task and print_sequent recompute a table every time they are called.
    Do we want that? *)
let print_task args ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] IST STRENG VERBOTEN *)
  (* forget_all (); *)
  let tables = match args.name_table with
    | None -> empty_names_table (* raise (Bad_name_table "Why3printer.print_task")*)
    | Some tables -> tables in
  print_prelude fmt args.prelude;
  fprintf fmt "theory Task@\n";
  print_th_prelude task fmt args.th_prelude;
  info := {
    info_syn = Discriminate.get_syntax_map task;
    itp = !info.itp};
  let rec print_decls = function
    | Some t ->
        print_decls t.Task.task_prev;
        begin match t.Task.task_decl.Theory.td_node with
        | Theory.Decl d ->
            begin try print_decl tables fmt d
            with Unsupported s -> raise (UnsupportedDecl (d,s)) end
        | _ -> () end
    | None -> () in
  print_decls task;
  fprintf fmt "end@."

let () = register_printer "why3" print_task
  ~desc:"Printer@ for@ the@ logical@ format@ of@ Why3.@ Used@ for@ debugging."

let rec print_term_intro tables fmt t =
  match t.t_node with
  | Tquant(Tforall,fq) ->
      let vl,_tl,f = t_open_quant fq in
      fprintf fmt "%a@\n@\n%a"
              (print_list newline (print_vsty tables)) vl
              (print_term_intro tables) f
  | Tbinop(Timplies,f1,f2) ->
      fprintf fmt "%a@\n@\n%a"
              (print_term tables) f1
              (print_term_intro tables) f2
  | _ -> print_term tables fmt t

(* do not forget these local names, they might be used by the itp *)
(*      List.iter (forget_var tables) vl*)

let print_goal tables fmt d =
   match d.d_node with
   | Dprop (Pgoal,_pr,f) -> fprintf fmt "@[%a@]" (print_term_intro tables) f
   | _ -> assert false

let print_sequent args ?old:_ fmt task =
  info := {info_syn = Discriminate.get_syntax_map task;
    itp = true};
  let tables = match args.name_table with
    | None -> empty_names_table (* raise (Bad_name_table "Why3printer.print_sequent") *)
    | Some tables -> tables in
  (* let tables = build_name_tables task in *)
  let ut = Task.used_symbols (Task.used_theories task) in
  let ld = Task.local_decls task ut in
  let rec aux fmt l =
    match l with
      | [] -> assert false
      | [g] ->
         fprintf fmt "______________________________________@\n@\n";
         print_goal tables fmt g
      | d :: r ->
         fprintf fmt "@[%a@]@\n" (print_decl tables) d;
         aux fmt r
  in
  fprintf fmt "@[<v 0>%a@]" aux ld

let () = register_printer "why3_itp" print_sequent
  ~desc:"Print@ the@ goal@ in@ a@ format@ dedicated@ to@ ITP."


(** *)
