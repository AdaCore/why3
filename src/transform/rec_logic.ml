open Ident
open Theory
open Ty
open Term
open Task
open Decl

let is_record_type kn ty =
  match ty.ty_node with
  | Tyapp (ts, _) -> List.length (find_constructors kn ts) = 1
  | _ -> false

let is_record_constant kn ls =
  ls.ls_args = [] && is_record_type kn (Opt.get ls.ls_value)

let record_constructor kn ty =
  match ty.ty_node with
  | Tyapp (ts, _) ->
      begin match find_constructors kn ts with
      | [c,_] -> c
      | _ -> assert false
      end
  | _ -> assert false

let lsubst env =
  (* given a map [ls |-> term], and assuming that all logic symbols in the map
     are symbols for constants, replace all occurrences of [ls] with the
     corresponding term *)
  let rec subst t =
    let t = t_map subst t in
    match t.t_node with
    | Tapp (ls,[]) ->
        begin try Mls.find ls env
        with Not_found -> t
        end
    | _ -> t
  in
  subst

let rec explode_fields kn orig_symbol ty =
  (* given an original symbol, and a type, return the "explosion" of the type
     in its record fields. Concretely, if ty is a record type
       { a : int; b : int},
     return a pair (t, l) where t is a term and l a logic_symbol list such that
       t = mk a b
       l = [a ; b]
     for some fresh ls symbols a and b.
   *)
  if is_record_type kn ty then
    let c = record_constructor kn ty in
    let s = ty_match Mtv.empty (Opt.get c.ls_value) ty in
    let args, lls =
      List.fold_right (fun ty (args, lls) ->
        let new_ty = ty_inst s ty in
        let t, lls' = explode_fields kn orig_symbol new_ty in
        t :: args, lls' @ lls) c.ls_args ([],[]) in
    t_app c args (Some ty), lls
  else
    let new_symb = create_lsymbol (id_clone orig_symbol.ls_name) [] (Some ty) in
    t_app new_symb [] (Some ty), [new_symb]

let explode_fields kn ls =
  (* given a logic symbol [ls], return the list of all its record fields as
     fresh logic symbols, and a term that has been built out of these symbols.
     *)
  explode_fields kn ls (Opt.get ls.ls_value)

let explode_record =
  Trans.fold_map (fun thd (env, task) ->
    let kn = thd.task_known in
    match thd.task_decl.td_node with
    | Decl { d_node = Dparam ls } when is_record_constant kn ls ->
        let t, lls = explode_fields kn ls in
        let env = Mls.add ls t env in
        env, List.fold_left (fun task ls ->
          Task.add_decl task (create_param_decl ls)) task lls
    | Decl { d_node = Dlogic ldl } ->
        let ldl = List.map (fun (fs, defn) ->
          let vls, t = open_ls_defn defn in
          let t = lsubst env t in
          make_ls_defn fs vls t) ldl in
        env, Task.add_decl task (create_logic_decl ldl)
    | Decl { d_node = Dprop (kind, ps, term) } ->
        let term = lsubst env term in
        env, Task.add_decl task (create_prop_decl kind ps term)
    | _ ->
        env, add_tdecl task thd.task_decl)
  Mls.empty None

let () =
  Trans.register_transform "explode_record_param" explode_record
    ~desc:"Explode global record params into their fields"
