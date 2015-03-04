(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ty
open Term
open Decl
open Theory
open Task

let debug = Debug.register_info_flag "transform"
  ~desc:"Print@ debugging@ messages@ about@ application@ \
         of@ proof@ task@ transformations."

(** Task transformation *)

type 'a trans = task -> 'a
type 'a tlist = 'a list trans

let apply f x = f x

let identity   x =  x
let identity_l x = [x]

let return x = fun _ -> x

let conv_res c f x = c (f x)

let singleton f x = [f x]

let compose   f g x =             g (f x)
let compose_l f g x = Lists.apply g (f x)

let seq l x   = List.fold_left (fun x f -> f x) x l
let seq_l l x = List.fold_left (fun x f -> Lists.apply f x) [x] l

module Wtask = Weakhtbl.Make (struct
  type t = task_hd
  let tag t = t.task_tag
end)

let store fn = let tr = Wtask.memoize_option 63 fn in fun t -> match t with
  | Some {task_decl = {td_node = Decl {d_node = Dprop (Pgoal,_,_)}}} -> fn t
  | _ -> tr t

let bind f g = store (fun task -> g (f task) task)

let trace_goal msg tr =
  fun task ->
    begin match task with
    | Some { task_decl = {td_node = Decl {d_node = Dprop (Pgoal,_,t)}}} ->
      Debug.dprintf debug "[%s (before)] task goal is %a@." msg Pretty.print_term t
    | _ -> Debug.dprintf debug "[%s (before)] task has non goal@." msg
    end;
    let new_task = tr task in
    begin match new_task with
    | Some { task_decl = {td_node = Decl {d_node = Dprop (Pgoal,_,t)}}} ->
      Debug.dprintf debug "[%s (after)] task goal is %a@." msg Pretty.print_term t
    | _ -> Debug.dprintf debug "[%s (after)] task has non goal@." msg
    end;
    new_task

let fold fn v =
  let h = Wtask.create 63 in
  let rewind acc task =
(*
    Format.eprintf "%c%d." (match task.task_decl.td_node with
    | Decl _ -> 'D' | Clone _ -> 'C'
    | Use _  -> 'U' | Meta _  -> 'M') (task.task_decl.td_tag);
*)
    let acc = fn task acc in
    match task.task_decl.td_node with
    | Decl {d_node = Dprop (Pgoal,_,_)} -> acc
    | _ -> Wtask.set h task acc; acc
  in
  let current task =
    try Some (Wtask.find h task)
    with Not_found -> None
  in
  let rec accum todo = function
    | None -> List.fold_left rewind v todo
    | Some task -> begin match current task with
        | Some v -> List.fold_left rewind v todo
        | None   -> accum (task::todo) task.task_prev
      end
  in
  accum []

let fold_l fn v = fold (fun task -> Lists.apply (fn task)) [v]

let fold_map   fn v t = conv_res snd            (fold   fn (v, t))
let fold_map_l fn v t = conv_res (List.map snd) (fold_l fn (v, t))
(* we use List.map instead of List.map_rev to preserve the order *)

let store_decl fn = let tr = Wdecl.memoize 63 fn in function
  | {d_node = Dprop (Pgoal,_,_)} as d -> fn d
  | d -> tr d

let gen_decl add fn =
  let fn = store_decl fn in
  let fn task acc = match task.task_decl.td_node with
    | Decl d -> List.fold_left add acc (fn d)
    | _ -> add_tdecl acc task.task_decl
  in
  fold fn

let gen_decl_l add fn =
  let fn = store_decl fn in
  let fn task acc = match task.task_decl.td_node with
    | Decl d -> List.map (List.fold_left add acc) (fn d)
    | _ -> [add_tdecl acc task.task_decl]
  in
  fold_l fn

let decl    = gen_decl   Task.add_decl
let decl_l  = gen_decl_l Task.add_decl
let tdecl   = gen_decl   add_tdecl
let tdecl_l = gen_decl_l add_tdecl

let apply_to_goal fn d = match d.d_node with
  | Dprop (Pgoal,pr,f) -> fn pr f
  | _ -> assert false

let gen_goal add fn = function
  | Some { task_decl = { td_node = Decl d }; task_prev = prev } ->
      List.fold_left add prev (apply_to_goal fn d)
  | _ -> assert false

let gen_goal_l add fn = function
  | Some { task_decl = { td_node = Decl d }; task_prev = prev } ->
      List.map (List.fold_left add prev) (apply_to_goal fn d)
  | _ -> assert false

let goal    = gen_goal   Task.add_decl
let goal_l  = gen_goal_l Task.add_decl
let tgoal   = gen_goal   add_tdecl
let tgoal_l = gen_goal_l add_tdecl

let rewrite fn = decl (fun d -> [decl_map fn d])
let rewriteTF fnT fnF = rewrite (TermTF.t_select fnT fnF)

let gen_add_decl add decls = store (function
  | Some { task_decl = { td_node = Decl d }; task_prev = prev } ->
      Task.add_decl (List.fold_left add prev decls) d
  | _ -> assert false)

let add_decls  = gen_add_decl Task.add_decl
let add_tdecls = gen_add_decl add_tdecl

(** dependent transformations *)

module Wtds = Weakhtbl.Make (struct
  type t = tdecl_set
  let tag s = s.tds_tag
end)

let on_theory_tds th fn =
  let fn = Wtds.memoize 17 fn in
  fun task -> fn (find_clone_tds task th) task

let on_meta_tds t fn =
  let fn = Wtds.memoize 17 fn in
  fun task -> fn (find_meta_tds task t) task

let on_theory th fn =
  let add td acc = match td.td_node with
    | Clone (_,sm) -> sm::acc
    | _ -> assert false
  in
  on_theory_tds th (fun tds -> fn (Stdecl.fold add tds.tds_set []))

let on_meta t fn =
  let add td acc = match td.td_node with
    | Meta (_,ma) -> ma::acc
    | _ -> assert false
  in
  on_meta_tds t (fun tds -> fn (Stdecl.fold add tds.tds_set []))

let on_used_theory th fn =
  let td = create_null_clone th in
  on_theory_tds th (fun tds -> fn (Stdecl.mem td tds.tds_set))

let on_meta_excl t fn =
  if not t.meta_excl then raise (NotExclusiveMeta t);
  let add td _ = match td.td_node with
    | Meta (_,ma) -> Some ma
    | _ -> assert false
  in
  on_meta_tds t (fun tds -> fn (Stdecl.fold add tds.tds_set None))

let on_tagged_ty t fn =
  begin match t.meta_type with
    | MTty :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAty ty :: _) -> Sty.add ty acc
    | _ -> assert false
  in
  on_meta_tds t (fun tds -> fn (Stdecl.fold add tds.tds_set Sty.empty))

let on_tagged_ts t fn =
  begin match t.meta_type with
    | MTtysymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAts ts :: _) -> Sts.add ts acc
    | _ -> assert false
  in
  on_meta_tds t (fun tds -> fn (Stdecl.fold add tds.tds_set Sts.empty))

let on_tagged_ls t fn =
  begin match t.meta_type with
    | MTlsymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MAls ls :: _) -> Sls.add ls acc
    | _ -> assert false
  in
  on_meta_tds t (fun tds -> fn (Stdecl.fold add tds.tds_set Sls.empty))

let on_tagged_pr t fn =
  begin match t.meta_type with
    | MTprsymbol :: _ -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  let add td acc = match td.td_node with
    | Meta (_, MApr pr :: _) -> Spr.add pr acc
    | _ -> assert false
  in
  on_meta_tds t (fun tds -> fn (Stdecl.fold add tds.tds_set Spr.empty))

(** debug *)
let print_meta f m task =
  let print_tds fmt m =
    Pp.print_iter1 Stdecl.iter Pp.newline Pretty.print_tdecl fmt
      (find_meta_tds task m).tds_set
  in
  Debug.dprintf f "@[<hov 2>meta %s :@\n%a@]@." m.Theory.meta_name print_tds m;
  task

(** register transformations *)

open Env

module Wenv = Weakhtbl.Make (struct
  type t = env
  let tag = env_tag
end)

exception UnknownTrans of string
exception KnownTrans of string
exception TransFailure of string * exn

let named s f (x : task) =
  Debug.dprintf debug "Apply transformation %s@." s;
  if Debug.test_flag Debug.stack_trace then f x
  else try f x with e -> raise (TransFailure (s,e))

type 'a reg_trans = Pp.formatted * (env -> 'a trans)

let transforms   : (task reg_trans) Hstr.t = Hstr.create 17
let transforms_l : (task list reg_trans) Hstr.t = Hstr.create 17

let register_transform ~desc s p =
  if Hstr.mem transforms s then raise (KnownTrans s);
  Hstr.replace transforms s (desc, fun _ -> named s p)

let register_transform_l ~desc s p =
  if Hstr.mem transforms_l s then raise (KnownTrans s);
  Hstr.replace transforms_l s (desc, fun _ -> named s p)

let register_env_transform ~desc s p =
  if Hstr.mem transforms s then raise (KnownTrans s);
  Hstr.replace transforms s (desc, Wenv.memoize 3 (fun e -> named s (p e)))

let register_env_transform_l ~desc s p =
  if Hstr.mem transforms_l s then raise (KnownTrans s);
  Hstr.replace transforms_l s (desc, Wenv.memoize 3 (fun e -> named s (p e)))

let lookup_transform s =
  try snd (Hstr.find transforms s)
  with Not_found -> raise (UnknownTrans s)

let lookup_transform_l s =
  try snd (Hstr.find transforms_l s)
  with Not_found -> raise (UnknownTrans s)

let list_transforms () =
  Hstr.fold (fun k (desc,_) acc -> (k, desc)::acc) transforms []

let list_transforms_l () =
  Hstr.fold (fun k (desc,_) acc -> (k, desc)::acc) transforms_l []

(** fast transform *)
type gentrans =
  | Trans_one of Task.task trans
  | Trans_list of Task.task tlist

let lookup_trans env name =
  try
    let t = lookup_transform name env in
    Trans_one t
  with UnknownTrans _ ->
    let t = lookup_transform_l name env in
    Trans_list t

let apply_transform tr_name env task =
   match lookup_trans env tr_name with
    | Trans_one t -> [apply t task]
    | Trans_list t -> apply t task

(** Flag-dependent transformations *)

exception UnknownFlagTrans of meta * string * string list
exception IllegalFlagTrans of meta

type ('a,'b) flag_trans = ('a -> 'b trans) Hstr.t

let on_flag m ft def arg =
  on_meta_excl m (fun alo ->
    let s = match alo with
      | None -> def
      | Some [MAstr s] -> s
      | _ -> raise (IllegalFlagTrans m)
    in
    let t = try Hstr.find ft s with
      | Not_found ->
          let l = Hstr.fold (fun s _ l -> s :: l) ft [] in
          raise (UnknownFlagTrans (m,s,l))
    in
    let tr_name = Printf.sprintf "%s : %s" m.meta_name s in
    named tr_name (t arg))

let () = Exn_printer.register (fun fmt exn -> match exn with
  | KnownTrans s ->
      Format.fprintf fmt "Transformation '%s' is already registered" s
  | UnknownTrans s ->
      Format.fprintf fmt "Unknown transformation '%s'" s
  | UnknownFlagTrans (m,s,l) ->
      Format.fprintf fmt "Bad parameter %s for the meta %s@." s m.meta_name;
      Format.fprintf fmt "Known parameters: %a"
        (Pp.print_list Pp.space Pp.string) l
  | IllegalFlagTrans m ->
      Format.fprintf fmt "Meta %s must be exclusive string-valued" m.meta_name
  | TransFailure (s,e) ->
      Format.fprintf fmt "Failure in transformation %s@\n%a" s
        Exn_printer.exn_printer e
  | e -> raise e)
