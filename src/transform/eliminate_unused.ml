open Decl
open Task
open Term

let term_lsymbols =
  (* compute lsymbols of a term *)
  let rec aux acc (t: term) =
    match t.t_node with
    | Tapp (ls, _) -> Term.t_fold aux (Term.Sls.add ls acc) t
    | _ -> Term.t_fold aux acc t
  in
  aux Sls.empty

let defn_symbols defn =
  let _, def = open_ls_defn defn in
  term_lsymbols def

let compute_needed_td (tdl, needed_symbols) td =
  match td.Theory.td_node with
  | Theory.Decl d ->
    begin
      match d.d_node with
      | Dtype _ | Ddata _ | Dind _ -> td :: tdl, needed_symbols
      | Dparam ls ->
        if Sls.mem ls needed_symbols then
          td :: tdl, Sls.remove ls needed_symbols
        else
          tdl, needed_symbols
      | Dlogic lls ->
        if List.exists (fun (ls, _) -> Sls.mem ls needed_symbols) lls then
          let needed_symbols =
            List.fold_left (fun acc (_, defn) ->
              Sls.union acc (defn_symbols defn)) needed_symbols lls in
          let needed_symbols =
            List.fold_left (fun acc (ls, _) ->
              Sls.remove ls acc) needed_symbols lls in
          td :: tdl, needed_symbols
        else tdl, needed_symbols
      | Dprop (_, _, t) ->
        let needed_symbols = Sls.union needed_symbols (term_lsymbols t) in
        td :: tdl, needed_symbols
    end
  | _ -> td :: tdl, needed_symbols

let eliminate_unused = Trans.store (fun task ->
  let tdl, _ = task_fold compute_needed_td ([], Sls.empty) task in
  List.fold_left add_tdecl None tdl)

let () = Trans.register_transform "eliminate_unused" eliminate_unused
    ~desc:"eliminate unused symbols"


