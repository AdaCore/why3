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

(** Isabelle printer
    main author: Stefan Berghofer <stefan.berghofer@secunet.com>
*)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer

(** Utilities *)

let attrib s pr fmt v = fprintf fmt " %s=\"%a\"" s pr v

let attribs s pr pr' fmt (att, r) = fprintf fmt "%a%a" (attrib s pr) att pr' r

let empty_elem s pr fmt att = fprintf fmt "<%s%a/>" s pr att

let elem s pr pr' fmt (att, x) = fprintf fmt "<%s%a>%a</%s>" s pr att pr' x s

let elem' s pr fmt x = elem s nothing pr fmt ((), x)

let elems s pr pr' fmt ((att, xs) as p) = match xs with
  | [] -> empty_elem s pr fmt att
  | _ -> elem s pr (print_list nothing pr') fmt p

let elems' s pr fmt xs = elems s nothing pr fmt ((), xs)

let pair pr pr' fmt (x, y) = fprintf fmt "%a%a" pr x pr' y

let opt_string_of_bool b = if b then Some "true" else None

(* identifiers *)

let black_list =
  ["o"; "O"]

let isanitize = sanitizer' char_to_alpha char_to_alnumus char_to_alnum

let fresh_printer () =
  create_ident_printer black_list ~sanitizer:isanitize

let iprinter = fresh_printer ()

let forget_ids () = forget_all iprinter

let string_of_id id = isanitize id.id_string

(* type variables *)

let tvprinter = fresh_printer ()

let forget_tvs () = forget_all tvprinter

let print_tv fmt tv =
  let n = id_unique tvprinter tv.tv_name in
  fprintf fmt "%s" n

(* logic variables *)

let print_vs fmt vs =
  let n = id_unique iprinter vs.vs_name in
  fprintf fmt "%s" n

let forget_var vs = forget_id iprinter vs.vs_name

(* info *)

type info = {
  info_syn : syntax_map;
  symbol_printers : (string * ident_printer) Mid.t;
  realization : bool;
  theories : string Mid.t;
}

let print_id fmt id = string fmt (id_unique iprinter id)

let print_altname_path info fmt id =
  attribs "altname" html_string
    (print_option (attrib "path" string))
    fmt (id.id_string, Mid.find_opt id info.theories)

let print_id_attr info fmt id =
  attribs "name" print_id (print_altname_path info)
    fmt (id, id)

let print_ts info fmt ts = print_id_attr info fmt ts.ts_name

let print_ls info fmt ls = print_id_attr info fmt ls.ls_name

let print_pr info fmt pr = print_id_attr info fmt pr.pr_name

let print_id_real info fmt id =
  try
    let path, ipr = Mid.find id info.symbol_printers in
    attribs "name" string (attrib "path" string) fmt (id_unique ipr id, path)
  with Not_found ->
    attribs "name" print_id (attrib "local" string) fmt (id, "true")

let print_ts_real info fmt ts = print_id_real info fmt ts.ts_name

(** Types *)

let rec print_ty info fmt ty = match ty.ty_node with
  | Tyvar v -> empty_elem "tvar" (attrib "name" print_tv) fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      elems' "prodt" (print_ty info) fmt tl
  | Tyapp (ts, tl) ->
      begin match query_syntax info.info_syn ts.ts_name with
        | Some s -> syntax_arguments s (print_ty info) fmt tl
        | None -> elems "type" (print_ts_real info) (print_ty info) fmt (ts, tl)
      end

let print_fun_type info fmt (tys, opty) = match opty with
  | None -> elems' "pred" (print_ty info) fmt tys
  | Some ty -> (match tys with
    | [] -> print_ty info fmt ty
    | _ -> elems' "fun" (print_ty info) fmt (tys @ [ty]))

(** Patterns, terms, and formulas *)

let print_ls_type info fmt ls =
  print_fun_type info fmt (ls.ls_args, ls.ls_value)

let print_ls_real info defs fmt (ls, ty) =
  if Sls.mem ls defs
  then elem "var" (attrib "name" print_id)
    (print_fun_type info) fmt (ls.ls_name, ty)
  else elem "const" (print_id_real info)
    (print_fun_type info) fmt (ls.ls_name, ty)

let print_app pr pr' fmt ((h, xs) as p) = match xs with
  | [] -> pr fmt h
  | _ -> elem' "app" (pair pr (print_list nothing pr')) fmt p

let print_var info fmt v =
  elem "var" (attrib "name" print_vs) (print_ty info) fmt (v, v.vs_ty)

let print_const = empty_elem "const" (attrib "name" string)

let print_abs info pr fmt (v, t) =
  elem "abs" (attrib "name" print_vs) (pair (print_ty info) pr) fmt
    (v, (v.vs_ty, t));
  forget_var v

let p_type p = p.pat_ty

let rec split_por p = match p.pat_node with
  | Pwild -> [pat_wild p.pat_ty]
  | Pvar v -> [pat_var v]
  | Pas _ -> assert false
  | Por (p1, p2) -> split_por p1 @ split_por p2
  | Papp (cs, pl) ->
      List.map (fun zs -> pat_app cs zs p.pat_ty)
        (List.fold_right
           (fun xs xss -> List.concat
              (List.map (fun x -> List.map (fun ys -> x :: ys) xss) xs))
           (List.map split_por pl) [[]])

let rec print_pat info fmt p = match p.pat_node with
  | Pwild -> print_const fmt "Pure.dummy_pattern"
  | Pvar v -> print_var info fmt v
  | Pas _ ->
      assert false
  | Por _ ->
      assert false
  | Papp (cs, pl) when is_fs_tuple cs ->
      elems' "prod" (print_pat info) fmt pl
  | Papp (cs, pl) ->
      begin match query_syntax info.info_syn cs.ls_name with
        | Some s -> gen_syntax_arguments_typed p_type (fun _ -> [||])
            s (print_pat info) (print_ty info) p fmt pl
        | _ -> print_app (print_ls_real info Sls.empty) (print_pat info)
            fmt ((cs, (List.map p_type pl, Some (p.pat_ty))), pl)
      end

let binop_name = function
  | Tand -> "HOL.conj"
  | Tor -> "HOL.disj"
  | Timplies -> "HOL.implies"
  | Tiff -> "HOL.eq"

let rec print_term info defs fmt t = match t.t_node with
  | Tvar v ->
      print_var info fmt v
  | Tconst c ->
      let number_format = {
          Number.long_int_support = true;
          Number.extra_leading_zeros_support = true;
          Number.negative_int_support = Number.Number_unsupported;
          Number.dec_int_support = Number.Number_default;
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_unsupported;
          Number.negative_real_support = Number.Number_unsupported;
          Number.dec_real_support = Number.Number_unsupported;
          Number.hex_real_support = Number.Number_unsupported;
          Number.frac_real_support = Number.Number_custom
            (Number.PrintFracReal
               ("<num val=\"%s\"><type name=\"Real.real\"/></num>",
                "<app>\
                   <const name=\"Groups.times_class.times\"/>\
                   <num val=\"%s\"><type name=\"Real.real\"/></num>\
                   <num val=\"%s\"/>\
                 </app>",
                "<app>\
                   <const name=\"Why3_Real.why3_divide\"/>\
                   <num val=\"%s\"><type name=\"Real.real\"/></num>\
                   <num val=\"%s\"/>\
                 </app>"));
          Number.def_real_support = Number.Number_unsupported;
        } in
      begin match c with
        | Number.ConstInt _ ->
            fprintf fmt "<num val=\"%a\">%a</num>"
              (Number.print number_format) c (print_ty info) (t_type t)
        | _ -> Number.print number_format fmt c
      end
  | Tif (f, t1, t2) ->
      print_app print_const (print_term info defs) fmt ("HOL.If", [f; t1; t2])
  | Tlet (t1, tb) ->
      elem' "app"
        (pair print_const (pair (print_term info defs)
           (print_abs info (print_term info defs))))
        fmt ("HOL.Let", (t1, t_open_bound tb))
  | Tcase (t, bl) ->
      elem' "case"
        (pair (print_term info defs)
           (print_list nothing (print_branch info defs)))
        fmt (t, bl)
  | Teps fb ->
      elem' "app"
        (pair print_const
           (print_abs info (print_term info defs)))
        fmt ("Hilbert_Choice.Eps", t_open_bound fb)
  | Tapp (fs, pl) when is_fs_tuple fs ->
      elems' "prod" (print_term info defs) fmt pl
  | Tapp (fs, tl) ->
      begin match query_syntax info.info_syn fs.ls_name with
        | Some s -> syntax_arguments_typed s
            (print_term info defs) (print_ty info) t fmt tl
        | _ -> print_app (print_ls_real info defs) (print_term info defs)
            fmt ((fs, (List.map t_type tl, t.t_ty)), tl)
      end
  | Tquant (q, fq) ->
      let vl, _tl, f = t_open_quant fq in
      print_quant info defs
        (match q with Tforall -> "HOL.All" | Texists -> "HOL.Ex")
        fmt (vl, f)
  | Ttrue ->
      print_const fmt "HOL.True"
  | Tfalse ->
      print_const fmt "HOL.False"
  | Tbinop (b, f1, f2) ->
      print_app print_const (print_term info defs) fmt (binop_name b, [f1; f2])
  | Tnot f ->
      print_app print_const (print_term info defs) fmt ("HOL.Not", [f])

and print_quant info defs s fmt (vl, f) = match vl with
  | [] -> print_term info defs fmt f
  | v :: vl' -> elem' "app" (pair print_const
      (print_abs info (print_quant info defs s))) fmt (s, (v, (vl', f)))

and print_branch info defs fmt br =
  let p, t = t_open_branch br in
  print_list nothing (elem' "pat" (pair (print_pat info) (print_term info defs)))
    fmt (List.map (fun q -> (q, t)) (split_por p));
  Svs.iter forget_var p.pat_vars

let rec dest_conj t = match t.t_node with
  | Tbinop (Tand, f1, f2) -> dest_conj f1 @ dest_conj f2
  | _ -> [t]

let rec dest_rule vl fl t = match t.t_node with
  | Tquant (Tforall, fq) ->
      let vl', _tl, f = t_open_quant fq in
      dest_rule (vl @ vl') fl f
  | Tbinop (Timplies, f1, f2) ->
      dest_rule vl (fl @ dest_conj f1) f2
  | _ -> (vl, fl, t)

let rec dest_forall vl t = match t.t_node with
  | Tquant (Tforall, fq) ->
      let vl', _tl, f = t_open_quant fq in
      dest_forall (vl @ vl') f
  | _ -> (vl, t)

(** Declarations *)

let print_constr info fmt (cs, pjl) =
  elems "constr" (print_ls info)
    (elem "carg" (print_option (print_ls info)) (print_ty info)) fmt
    (cs, List.combine pjl cs.ls_args)

let print_tparams = elems' "params" (empty_elem "param" (attrib "name" print_tv))

let print_data_decl info fmt (ts, csl) =
  elem "datatype" (print_ts info)
    (pair print_tparams (elems' "constrs" (print_constr info)))
    fmt (ts, (ts.ts_args, csl));
  forget_tvs ()

let print_data_decls info fmt tl =
  let tl = List.filter (fun (ts, _) ->
    not (is_ts_tuple ts || Mid.mem ts.ts_name info.info_syn)) tl in
  if tl <> [] then begin
    elems' "datatypes" (print_data_decl info) fmt tl
  end

let print_statement s pr id info fmt f =
  let vl, prems, concl = dest_rule [] [] f in
  elem s pr
    (pair
       (elems' "prems" (print_term info Sls.empty))
       (elems' "concls" (print_term info Sls.empty)))
    fmt (id, (prems, dest_conj concl));
  List.iter forget_var vl;
  forget_tvs ()

let print_equivalence_lemma info fmt (ls, ld) =
  let name = Ident.string_unique iprinter
    ((id_unique iprinter ls.ls_name) ^ "_def") in
  print_statement "lemma" (attrib "name" string) name info fmt (ls_defn_axiom ld)

let print_fun_eqn s info defs fmt (ls, ld) =
  let vl, t = dest_forall [] (ls_defn_axiom ld) in
  elem s (print_altname_path info) (print_term info defs) fmt (ls.ls_name, t);
  List.iter forget_var vl

let print_logic_decl info fmt ((ls, _) as d) =
  print_fun_eqn "definition" info (Sls.add ls Sls.empty) fmt d;
  forget_tvs ()

let print_logic_decl info fmt d =
  (* During realization the definition of a "builtin" symbol is
     printed and an equivalence lemma with associated Isabelle function is
     requested *)
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    print_logic_decl info fmt d
  else if info.realization then
    print_equivalence_lemma info fmt d

let print_recursive_decl info fmt dl =
  let dl_syn, dl_no_syn =
    List.partition (fun (ls, _) ->
      info.realization && (Mid.mem ls.ls_name info.info_syn)) dl in
  let defs = List.fold_left (fun acc (ls, _) ->
    Sls.add ls acc) Sls.empty dl_no_syn in
  if dl_no_syn <> [] then begin
    elems' "function" (print_fun_eqn "eqn" info defs) fmt dl_no_syn;
    forget_tvs ()
  end;
  List.iter (print_equivalence_lemma info fmt) dl_syn

let print_ind info defs fmt (pr, f) =
  let vl, fl, g = dest_rule [] [] f in
  elem "rule" (print_pr info)
    (pair (elems' "prems" (print_term info defs)) (print_term info defs))
    fmt (pr, (fl, g));
  List.iter forget_var vl

let print_ind_decl info defs fmt (ps, bl) =
  elem "pred" (print_ls info)
    (pair (print_ls_type info) (print_list nothing (print_ind info defs)))
    fmt (ps, (ps, bl))

let print_coind fmt s = match s with
  | Ind -> ()
  | Coind -> attrib "coind" string fmt "true"

let print_ind_decls info s fmt tl =
  let tl_syn, tl_no_syn = List.partition (fun (ps, _) ->
    info.realization && (Mid.mem ps.ls_name info.info_syn)) tl in
  let defs = List.fold_left (fun acc (ps, _) ->
    Sls.add ps acc) Sls.empty tl_no_syn in
  if tl_no_syn <> [] then begin
    elems "inductive" print_coind (print_ind_decl info defs) fmt (s, tl_no_syn);
    forget_tvs ()
  end;
  List.iter (fun (_, rls) ->
    List.iter (fun (pr, f) ->
      print_statement "lemma" (print_pr info) pr info fmt f) rls) tl_syn

let print_type_decl info fmt ts =
  if not (Mid.mem ts.ts_name info.info_syn || is_ts_tuple ts) then
  let def = match ts.ts_def with Alias ty -> Some ty | _ -> None in
    (elem "typedecl" (print_ts info)
       (pair print_tparams (print_option (print_ty info)))
       fmt (ts, (ts.ts_args, def));
     forget_tvs ())

let print_param_decl info fmt ls =
  if not (Mid.mem ls.ls_name info.info_syn) then
    (elem "param" (print_ls info) (print_ls_type info) fmt (ls, ls);
     forget_tvs ())

let print_prop_decl info fmt (k, pr, f) =
  let stt = match k with
    | Paxiom when info.realization -> "lemma"
    | Paxiom -> "axiom"
    | Plemma -> "lemma"
    | Pgoal -> "lemma"
  in
  print_statement stt (print_pr info) pr info fmt f

let print_decl info fmt d =
  match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata tl -> print_data_decls info fmt tl
  | Dparam ls ->
      print_param_decl info fmt ls
  | Dlogic [s,_ as ld] when not (Sid.mem s.ls_name d.d_syms) ->
      print_logic_decl info fmt ld
  | Dlogic ll ->
      print_recursive_decl info fmt ll
  | Dind (s, il) ->
      print_ind_decls info s fmt il
  | Dprop (_, pr, _) when not info.realization && Mid.mem pr.pr_name info.info_syn ->
      ()
  | Dprop pr ->
      print_prop_decl info fmt pr

let print_decls info fmt dl =
  print_list nothing (print_decl info) fmt dl

let make_thname th = String.concat "." (th.Theory.th_path @
  [string_of_id th.Theory.th_name])

let print_task printer_args realize fmt task =
  forget_ids ();
  (* find theories that are both used and realized from metas *)
  let realized_theories =
    Task.on_meta meta_realized_theory (fun mid args ->
      match args with
      | [Theory.MAstr s1; Theory.MAstr _] ->
        let f,id =
          let l = Strings.rev_split '.' s1 in
          List.rev (List.tl l), List.hd l in
        let th = Env.read_theory printer_args.env f id in
        Mid.add th.Theory.th_name (th, s1) mid
      | _ -> assert false
    ) Mid.empty task in
  (* two cases: task is use T or task is a real goal *)
  let rec upd_realized_theories = function
    | Some { Task.task_decl = { Theory.td_node =
               Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, pr, _) }}} ->
        string_of_id pr.pr_name, realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Use th }} ->
        Sid.iter (fun id -> ignore (id_unique iprinter id)) th.Theory.th_local;
        let id = th.Theory.th_name in
        String.concat "." (th.Theory.th_path @ [string_of_id id]),
        Mid.remove id realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Meta _ };
             Task.task_prev = task } ->
        upd_realized_theories task
    | _ -> assert false in
  let thname, realized_theories = upd_realized_theories task in
  (* make names as stable as possible by first printing all identifiers *)
  let realized_theories' = Mid.map fst realized_theories in
  let realized_symbols = Task.used_symbols realized_theories' in
  let local_decls = Task.local_decls task realized_symbols in
  let symbol_printers =
    let printers =
      Mid.map (fun th ->
        let pr = fresh_printer () in
        Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
        pr)
        realized_theories' in
    Mid.map (fun th ->
        (snd (Mid.find th.Theory.th_name realized_theories),
         Mid.find th.Theory.th_name printers))
      realized_symbols in
  let info = {
    info_syn = get_syntax_map task;
    symbol_printers = symbol_printers;
    realization = realize;
    theories = Mid.map make_thname
      (Task.used_symbols (Task.used_theories task));
  }
  in
  elem "theory"
    (attribs "name" string (print_option (attrib "realize" string)))
    (pair
       (elems' "realized" (empty_elem "require"
          (attrib "name" (fun fmt (th, _) ->
             string fmt (make_thname th)))))
       (print_decls info))
    fmt
    ((thname, opt_string_of_bool realize),
     (Mid.values realized_theories, local_decls))

let print_task_full args ?old:_ fmt task =
  print_task args false fmt task

let print_task_real args ?old:_ fmt task =
  print_task args true fmt task

let () = register_printer "isabelle" print_task_full
  ~desc:"Printer@ for@ the@ Isabelle@ proof@ assistant@ \
         (without@ realization@ capabilities)."

let () = register_printer "isabelle-realize" print_task_real
  ~desc:"Printer@ for@ the@ Isabelle@ proof@ assistant@ \
         (with@ realization@ capabilities)."
