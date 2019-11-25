
(* This is a very light parsing/printing of tasks example for Ada. .adb files
   can be understood as whyml files. Then, in the ide, tasks are printed looking
   like Ada code and arguments of transformations are parsed using the same
   formalism.
*)

open Why3

let ada_format = "ada"

let () = Env.register_format Pmodule.mlw_language ada_format ["adb"]
    Lexer.read_channel ~desc:"WhyML@ for@ Ada"

open Pretty
open Term
open Format
open Pp

let get_name ls =
  Ident.(get_element_name ~attrs:ls.ls_name.id_attrs)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

(* ada print_binop *)
let print_binop ~asym fmt = function
  | Tand when asym -> fprintf fmt "and then"
  | Tor when asym  -> fprintf fmt "or else"
  | Tand           -> fprintf fmt "and"
  | Tor            -> fprintf fmt "or"
  | Timplies       -> fprintf fmt "->"
  | Tiff           -> fprintf fmt "<->"

let print_ty_arg print_any fmt ty =
  fprintf fmt "@ %a" print_any (Pp_ty (ty, 2, false))

let print_constr print_any fmt (cs,pjl) =
  let add_pj pj ty pjl = (pj,ty)::pjl in
  let print_pj fmt (pj,ty) = match pj with
    | Some ls ->
        fprintf fmt "@   %a:@ %a"
          print_any (Pp_ls ls)
          print_any (Pp_ty (ty, 2, false))
    | None -> print_ty_arg print_any fmt ty
  in
  fprintf fmt " -- %a%a@\n%a" print_any (Pp_cs cs)
    print_any (Pp_id cs.ls_name)
    (print_list Pp.newline print_pj)
    (List.fold_right2 add_pj pjl cs.ls_args [])

let print_quant fmt = function
  | Tforall -> fprintf fmt "for all"
  | Texists -> fprintf fmt "for some"

(* Check the "syntax" attribute of the lsymbol and returns true if it is a
   getter. *)
let is_getter fs =
  Ident.(match get_element_syntax ~attrs:fs.ls_name.id_attrs with
      | Is_getter name when name = fs.ls_name.id_string ->
          true
      | _ -> false
    )

(* Register the transformations functions *)
let rec ada_ext_printer is_field print_any fmt a =
  (* TODO complete this function *)
  match a with
  | Pp_term (t, pri) ->
      begin match t.t_node with
        | Tnot {t_node = Tapp (ls, [t1; t2]) } when ls_equal ls ps_equ ->
            (* /= *)
            fprintf fmt (protect_on (pri > 0) "@[%a /= %a@]")
              (ada_ext_printer is_field print_any) (Pp_term (t1, 0))
              (ada_ext_printer is_field print_any) (Pp_term (t2, 0))
        | Tbinop (b, f1, f2) ->
            (* and, or, and then, or else *)
            let asym = Ident.Sattr.mem asym_split f1.t_attrs in
            let p = prio_binop b in
            fprintf fmt (protect_on (pri > p) "@[%a %a@ %a@]")
              (ada_ext_printer is_field print_any) (Pp_term (f1, (p + 1)))
              (print_binop ~asym) b
              (ada_ext_printer is_field print_any) (Pp_term (f2, p))
        | Tapp (fs, [{t_node = Tapp (getter, [array]); _}; index])
          when ls_equal fs Term.fs_func_app && is_getter getter ->
            (* Array case: [|(get A) @ I|] to be printed as [|A (I)|] *)
            fprintf fmt (protect_on (pri > 0) "@[%a (%a)@]")
              (ada_ext_printer is_field print_any) (Pp_term (array, 0))
              (ada_ext_printer is_field print_any) (Pp_term (index, 0))
        | Tapp (getter, [array; index]) when is_getter getter ->
            (* Array case: [|get A I|] to be printed as [|A (I)|] *)
            fprintf fmt (protect_on (pri > 0) "@[%a (%a)@]")
              (ada_ext_printer is_field print_any) (Pp_term (array, 0))
              (ada_ext_printer is_field print_any) (Pp_term (index, 0))
        | Tapp (fs, [r]) when is_field fs ->
            (* Record field a.b.c *)
            fprintf fmt "@[%a.%a@]"
              (ada_ext_printer is_field print_any) (Pp_term (r, 7))
              print_any (Pp_ls fs)
        | Tapp (fs, [r])
          when let s = get_name fs in s = Some "First" || s = Some "Last" ->
            (* Printing of 'First and 'Last *)
            fprintf fmt "@[%a'%a@]"
              (ada_ext_printer is_field print_any) (Pp_term (r, 7))
              print_any (Pp_ls fs)
        | Tquant (q, fq) ->
            let vl,tl,f = t_open_quant fq in
            (* Specific case for : for all I in A .. B => P(I)
               TODO: We recognize <= with its ident name: this could be improved
            *)
            begin match f.t_node, vl with
              | Tbinop
                  (Timplies,
                   {t_node =
                      Tbinop (Tand,
                              {t_node =
                                 Tapp (le1, [t1; {t_node = Tvar v1; _}]); _},
                              {t_node = Tapp (le2, [{t_node = Tvar v2; _}; t2]); _}
                             ); _},
                   f2), [v3]
                when le1.ls_name.Ident.id_string = "infix <=" &&
                     le2.ls_name.Ident.id_string = "infix <=" &&
                     Term.vs_equal v1 v2 && Term.vs_equal v2 v3 ->
                  fprintf fmt (protect_on (pri > 0) "@[<hov 1>%a %a%a in %a .. %a =>@ %a@]")
                    print_quant q
                    (print_list comma (fun fmt v -> print_any fmt (Pp_vs v))) vl
                    print_any (Pp_trigger tl)
                    (ada_ext_printer is_field print_any) (Pp_term (t1, 1))
                    (ada_ext_printer is_field print_any) (Pp_term (t2, 1))
                    (ada_ext_printer is_field print_any) (Pp_term (f2, 0));
                  print_any fmt (Pp_forget vl)
              | _, _ ->
                  fprintf fmt (protect_on (pri > 0) "@[<hov 1>%a %a%a =>@ %a@]")
                    print_quant q
                    (print_list comma (fun fmt v -> print_any fmt (Pp_vs v))) vl
                    print_any (Pp_trigger tl)
                    (ada_ext_printer is_field print_any) (Pp_term (f, 0));
                  print_any fmt (Pp_forget vl)
            end
        | Tconst c ->
            begin
              match t.t_ty with
              | Some {Ty.ty_node = Ty.Tyapp (ts,[])}
                when Ty.ts_equal ts Ty.ts_int || Ty.ts_equal ts Ty.ts_real ->
                  Constant.print_def fmt c
              | Some ty ->
                  (* TODO find a better way to print those *)
                  fprintf fmt "(%a:%a)" Constant.print_def c
                    print_any (Pp_ty (ty, 0, false))
              | None -> assert false
            end
        | _ -> print_any fmt a
      end

  | Pp_decl (fst, ts, csl) ->
      begin match csl with
        | [_, pr_list] when List.for_all (fun x -> x <> None) pr_list &&
                            ts.Ty.ts_args = [] ->
            fprintf fmt "@[<hov 2>%s %a%a is @\n record %a@\n end record@]"
              (if fst then "type" else "with")
              print_any (Pp_ts ts)
              print_any (Pp_id ts.Ty.ts_name)
              (print_list newline (print_constr print_any)) csl;
            (print_any fmt) Pp_forget_tvs
        | _ -> print_any fmt a
      end
  | _ -> print_any fmt a

let ada_ext_printer task =
  (* First traverse the task to find fields of records, then use it during
     printing. *)
  let set_records =
    let records_fields = Sls.empty in
    let decls = Task.task_tdecls task in
    List.fold_left Theory.(fun acc decl ->
        match decl.td_node with
        | Decl d ->
          Decl.(begin match d.d_node with
                | Ddata [_tys, [_cs_name, fields]] ->
                    (* Non recursive with only one constructor *)
                    List.fold_left (fun acc ls ->
                        if ls <> None then
                          Sls.add (Opt.get ls) acc
                        else
                          acc) acc fields
                | _ -> acc
              end)
        | _ -> acc) records_fields decls
  in
  let is_record ls =
    Sls.mem ls set_records
  in
  ada_ext_printer is_record

let () = Itp_server.add_registered_lang ada_format ada_ext_printer

let () = Args_wrapper.set_argument_parsing_functions ada_format
    ~parse_term:(fun nt lb -> Ada_lexer.parse_term nt lb)
    ~parse_term_list:(fun nt lb -> Ada_lexer.parse_term_list nt lb)
    ~parse_list_ident:(fun lb -> Ada_lexer.parse_list_ident lb)
    ~parse_qualid:(fun lb -> Ada_lexer.parse_qualid lb)
    ~parse_list_qualid:(fun lb -> Ada_lexer.parse_list_qualid lb)
