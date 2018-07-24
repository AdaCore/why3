open Term
open Decl
open Theory
open Task

let debug = Debug.register_info_flag "fold_defs"
  ~desc:"Print@ debugging@ messages@ of@ the@ fold_defs@ transformation."

type def_elt = {
  name  : lsymbol;
  args  : vsymbol list;
  body  : Term.term;
  axiom : Term.term;
}

let rec unfold_foralls axiom =
  match axiom.t_node with
  | Tquant (Tforall,tq) ->
    let args,_,body = t_open_quant tq in begin
      try
        let more_args,less_body = unfold_foralls body in
        args@more_args,less_body
      with Not_found -> args,body
    end
  | _ -> raise Not_found

let get_def_elt axiom =
  match axiom.t_node with
  | Tquant (Tforall,tq) ->
    (* look for axioms defining (without recursion) a term with one of
       the following patterns *)
    (* let args,_,t = t_open_quant tq in *)
    let args,t = unfold_foralls axiom in
    let veq a b = match b with
      | { t_node = Tvar v } -> vs_equal a v
      | _ -> false in
    let check_args args' = List.for_all2 veq args args' in
    (* todo ! rewrite it à la Decl.ls_defn_of_axiom ! *)
    begin match t.t_node with
      (* forall args. name args = body *)
      | Tapp (lseq, [ { t_node = Tapp (name, args') }; body ] )
        when ls_equal lseq ps_equ && List.length args = List.length args' &&
             not (t_s_any (fun _ -> false) (fun t -> ls_equal name t) body) &&
             check_args args'
        ->
        {name; args; body; axiom}
      (* forall args. name args <-> body *)
      | Tbinop (Tiff, { t_node = Tapp (name, args') }, body)
        when List.length args = List.length args' &&
             not (t_s_any (fun _ -> false) (fun t -> ls_equal name t) body) &&
             check_args args'
        ->
        {name; args; body; axiom}
      (* forall args. name args = true <-> body *)
      | Tbinop (Tiff, { t_node = Tapp (lseq, [ { t_node = Tapp (name, args') }; ttrue ])}, body)
        when List.length args = List.length args' &&
             ls_equal lseq ps_equ &&
             t_equal ttrue t_bool_true &&
             not (t_s_any (fun _ -> false) (fun t -> ls_equal name t) body) &&
             check_args args'
        ->
        {name; args; body; axiom}
      | _ -> raise Not_found
    end
  | _ -> raise Not_found

let collect_defs ignore = Trans.fold (fun hd acc ->
  match hd.task_decl.td_node, acc with
  | Decl d, (ids, defs) -> begin match d.d_node with
      | Dparam l ->
        if Debug.test_flag debug then
          Format.printf "[fold_defs]@ add@ lsym@ %a@." Pretty.print_ls l;
        l :: ids, defs
      | Dprop (Paxiom,v,t) when not (Spr.exists (pr_equal v) ignore) ->
        begin try
            let elt = get_def_elt t in
            if List.exists (ls_equal elt.name) ids then begin
              if Debug.test_flag debug then
                Format.printf "[fold_defs]@ add@ ax@ %a@." Pretty.print_term t;
              ids, elt :: defs
            end else
              ids, defs
          with Not_found -> ids, defs
        end
      | _ -> ids, defs
    end
  | _ -> acc) ([],[])

let replace_defs (ids,defs) =
  Trans.decl (fun d -> match d.d_node with
      | Dparam l ->
        begin try
            let a = List.find (fun a -> ls_equal l a.name) defs in
            if Debug.test_flag debug then
              Format.printf "[fold_defs]@ found@ l@ :@ %a@; replacing@ it@ with@ %a." Pretty.print_ls l
                Pretty.print_term a.body;
            let a = match a.body.t_ty, a.name.ls_value with
              (* deal with predicate vs function returning boolean *)
              | None, Some v when Ty.ty_equal v Ty.ty_bool ->
                let body = t_if a.body t_bool_true t_bool_false in
                { a with body = body }
              | _ -> a
            in
            let ll = make_ls_defn a.name a.args a.body in
            [create_logic_decl [ll]]
          with Not_found -> [d]

        end
      | Dprop (Paxiom,v,t) when List.exists (fun def -> t_equal t def.axiom) defs ->
        if Debug.test_flag debug then
          Format.printf "[fold_defs]@ remove@ axiom@ %a@." Pretty.print_term t;
        []
      | _ -> [d]) None

let wrapper t =
  Trans.on_meta Printer.meta_remove_prop (fun metas ->
      let ignore = List.fold_left (fun acc meta_arg ->
          match meta_arg with
          | [Theory.MApr pr] -> Spr.add pr acc
          | _ -> assert false) Spr.empty metas
      in t ignore)

let wrap =
  Trans.store (fun task ->
      try
        Trans.apply (wrapper (fun ignore -> Trans.bind (collect_defs ignore) replace_defs)) task
      with Decl.UnknownIdent id ->
        if Debug.test_flag debug then
          Format.printf "[fold_defs]@ gave@ up@ because@ of@ %a@."
            Pretty.print_id_attrs id;
        task)

let () =
  Trans.register_transform "fold_defs" wrap ~desc:"fold@ definitions@."
