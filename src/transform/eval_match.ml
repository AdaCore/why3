
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

let rec dive fn env t = match t.t_node with
  | Tvar x when Mvs.mem x env ->
      dive fn env (Mvs.find x env)
  | Tlet (t1, tb) ->
      let x, t2, close = t_open_bound_cb tb in
      let t2 = dive fn (Mvs.add x t1 env) t2 in
      t_label_copy t (t_let_simp t1 (close x t2))
  | _ -> fn t

let make_case kn fn t bl =
  let mk_b b = let p,t = t_open_branch b in [p], fn t in
  Pattern.CompileTerm.compile (find_constructors kn) [t] (List.map mk_b bl)

let eval_match ~inline kn t =
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
        let process t1 =
          let r = make_case kn (eval env) t1 bl in
          match r.t_node with
            | Tcase ({ t_node = Tcase (t1, bl1) }, bl2) ->
                let branch b =
                  let p,t,close = t_open_branch_cb b in
                  if not (update kn t) then raise Exit;
                  close p (make_case kn (fun x -> x) t bl2)
                in
                (try t_case t1 (List.map branch bl1) with Exit -> r)
            | _ -> r
        in
        t_label_copy t (dive process env t1)
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
