open Why3

let naming_table_ref: Trans.naming_table option ref = ref None

let get_naming_table () =
  match !naming_table_ref with
  | None -> raise Not_found
  | Some nt -> nt

let set_naming_table nt =
  naming_table_ref := Some nt

(* If the string is recognized in the naming table as of an array type
   (according to attribute "syntax" of said type) then returns the string
   corresponding to its getter as it was printed.
   For every other cases, raise [Not_found] *)
let convert_array (nt: Trans.naming_table) (a_str: string) =
  let ns = nt.Trans.namespace in
  let km = nt.Trans.known_map in
  let prls = nt.Trans.printer in
  let get_getter (ty: Ty.ty) =
    (* Returns Not found if it does not find *)
    let ty = match ty.Ty.ty_node with
      | Ty.Tyapp (ty, _) -> ty
      | _ -> raise Not_found in
    let id = ty.Ty.ts_name in
    let d = Ident.Mid.find id km in
    let elts_name = Ident.(match Pretty.get_element_syntax ~attrs:id.id_attrs with
        | Pretty.Is_array elts -> elts
        | _ -> raise Not_found) in
    let elts = match d.Decl.d_node with
      | Decl.Ddata [_tys, [_cs_name, proj_names]] ->
          (* Non recursive and only one constructor *)
          List.find (fun x ->
              match x with
              | None -> false
              | Some x -> x.Term.ls_name.Ident.id_string = elts_name) proj_names
      | _ -> raise Not_found in
    (Opt.get elts).Term.ls_name
  in
  let get_string (id: Ident.ident) =
    Ident.(if known_id prls id then
             id_unique prls id
           else
             raise Not_found)
  in
  match Theory.ns_find_ls ns [a_str] with (* No need to check ns_ns field *)
  | ls when ls.Term.ls_value <> None ->
      let ty = match ls.Term.ls_value with
        | None -> assert false (* Impossible: above "when" condition *)
        | Some ty -> ty in
      get_string (get_getter ty)
  | _ -> raise Not_found
