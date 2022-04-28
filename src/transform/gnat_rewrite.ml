open Decl
open Ident
open Term

let first_attr = Ident.create_attribute "rewrite:first"
let last_attr = Ident.create_attribute "rewrite:last"
let of_array_attr = Ident.create_attribute "rewrite:of_array"
let to_array_attr = Ident.create_attribute "rewrite:to_array"

let ls_has_attr attr ls = Sattr.mem attr (ls.ls_name.id_attrs)
let ls_has_outer_attr ls =
  ls_has_attr first_attr ls ||
  ls_has_attr last_attr ls ||
  ls_has_attr to_array_attr ls

let rewrite_term t =
  let rec aux env t =
  match t.t_node with
  | Tapp (outer, args) when ls_has_outer_attr outer ->
    assert (List.length args = 1);
    let arg = List.hd args in
    let arg =
      match arg.t_node with
      | Tvar v ->
        begin try Mvs.find v env with Not_found -> arg end
      | _ -> arg
    in
    begin match arg.t_node with
      | Tapp (inner, args) when ls_has_attr of_array_attr inner  ->
        assert (List.length args = 3);
        let r =
          if ls_has_attr to_array_attr outer then List.nth args 0
          else if ls_has_attr first_attr outer then List.nth args 1
          else List.nth args 2
        in
        t_attr_copy t r
      | _ -> t_map (aux env) t
    end
  | Tlet (tdef, tb) ->
    let tdef = aux env tdef in
    let v, t2 = t_open_bound tb in
    let env = Mvs.add v tdef env in
    let t2 = aux env t2 in
    t_attr_copy t (t_let tdef (t_close_bound v t2))
  | _ -> t_map (aux env) t
  in
  aux Mvs.empty t

let elim d =
  match d.d_node with
  | Dprop (kind, pr, term) ->
    [create_prop_decl kind pr (rewrite_term term)]
  | _ -> [d]


let elim_to_of_array = Trans.decl elim None
