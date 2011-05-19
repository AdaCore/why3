
open Format
open Ident
open Ty
open Term
open Decl
open Pretty

type inline = known_map -> lsymbol -> bool

let unfold def tl ty =
  let vl, e = open_ls_defn def in
  let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
  let (mt,mv) = List.fold_left2 add (Mtv.empty, Mvs.empty) vl tl in
  let mt = oty_match mt e.t_ty ty in
  t_ty_subst mt mv e

let is_constructor kn ls = match Mid.find ls.ls_name kn with
  | { d_node = Dtype _ } -> true
  | _ -> false

(* checks that all branches ``start'' with constructors *)
let rec update kn t = match t.t_node with
  | Tapp (ls, _) -> is_constructor kn ls
  | Tlet (_, t) -> let _, t = t_open_bound t in update kn t
  | _ -> false

let eval_match ~inline kn t =
  let rec find_var env t = match t.t_node with
    | Tvar x when Mvs.mem x env -> find_var env (Mvs.find x env)
    | _ -> t
  in
  let rec eval env t = match t.t_node with
    | Tapp (ls, tl) when inline kn ls ->
	begin match find_logic_definition kn ls with
	  | None ->
	      t_map (eval env) t
	  | Some def ->
	      t_label_copy t (eval env (unfold def tl t.t_ty))
	end
    | Tlet (t1, tb2) ->
	let t1 = eval env t1 in
	let x, t2, close = t_open_bound_cb tb2 in
	let t2 = eval (Mvs.add x t1 env) t2 in
	t_label_copy t (t_let_simp t1 (close x t2))
    | Tcase (t1, bl) ->
	let t1 = eval env t1 in
	let t1 = find_var env t1 in
	let mk_b (p,t) = ([p], t) in
	let bl = List.map (fun b -> mk_b (t_open_branch b)) bl in
	let r = Pattern.CompileTerm.compile (find_constructors kn) [t1] bl in
	let eval_branch b =
	  let p, t, close = t_open_branch_cb b in close p (eval env t)
	in
	let res = match r.t_node with
	  | Tcase ({ t_node = Tcase (t1, bl1) }, bl2) ->
	      let bl1 = List.map t_open_branch bl1 in
	      if List.for_all (fun (_, t) -> update kn t) bl1 then
		let branch (p, t) =
		  t_close_branch p (eval env (t_case t bl2))
		in
		t_case t1 (List.map branch bl1)
	      else
		let branch (p, t) = t_close_branch p (eval env t) in
		let bl2 = List.map eval_branch bl2 in
		t_case (t_case t1 (List.map branch bl1)) bl2
	  | Tcase (t1, bl) ->
	      t_case t1 (List.map eval_branch bl)
	  | _ ->
	      eval env r
	in
	t_label_copy t res
    | _ ->
	t_map (eval env) t
  in
  eval Mvs.empty t

let rec linear vars t = match t.t_node with
  | Tvar x when Svs.mem x vars ->
      raise Exit
  | Tvar x ->
      Svs.add x vars
  | _ ->
      t_fold linear vars t

let linear t =
  try ignore (linear Svs.empty t); true with Exit -> false

let inline_nonrec_linear kn ls =
  let d = Mid.find ls.ls_name kn in
  match d.d_node with
    | Dlogic dl ->
	let no_occ (ls', def) = match def with
	  | None ->
	      true
	  | Some def ->
	      let _, t = open_ls_defn def in
	      not (t_s_any Util.ffalse (ls_equal ls) t) &&
              (not (ls_equal ls ls') || linear t)
	in
	List.for_all no_occ dl
    | _ ->
	false
