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

open Why3
open Term

(*******************************)
(*          explanations       *)
(*******************************)

let expl_regexp = Str.regexp "expl:\\(.*\\)"

let check_expl lab acc =
  let lab = lab.Ident.lab_string in
  if Str.string_match expl_regexp lab 0
  then Some (Str.matched_group 1 lab)
  else acc

let check_expl lab = Ident.Slab.fold check_expl lab None

let rec get_expl_fmla acc f =
  if f.t_ty <> None then acc else
  if Ident.Slab.mem Split_goal.stop_split f.Term.t_label then acc else
  let res = check_expl f.Term.t_label in
  if res = None then match f.t_node with
    | Term.Ttrue | Term.Tfalse | Term.Tapp _ -> acc
    | Term.Tbinop (Term.Timplies,_,f) -> get_expl_fmla acc f
    | Term.Tlet _ | Term.Tcase _ | Term.Tquant (Term.Tforall, _) ->
        Term.t_fold get_expl_fmla acc f
    | _ -> raise Exit
  else if acc = None then res else raise Exit

let get_expl_fmla f = try get_expl_fmla None f with Exit -> None

let goal_expl_task ~root task =
  let gid = (Task.task_goal task).Decl.pr_name in
  let info =
    let fmla = Task.task_goal_fmla task in
    let res = get_expl_fmla fmla in
    if res <> None || not root then res else check_expl gid.Ident.id_label
  in
  gid, info, task

(* {2 ident dictionaries for shapes} *)

let dict_table = Hashtbl.create 17
let dict_count = ref 0
let reverse_ident_table = Hashtbl.create 17
let reverse_dict_count = ref 0

let reset_dict () =
  Hashtbl.clear dict_table;
  Hashtbl.clear reverse_ident_table;
  dict_count := 0;
  reverse_dict_count := 0

(* {3 direct table to read shapes from strings} *)


let get_name s b i =
  try while !i < String.length s do
    match String.get s !i with
      | ')' -> incr i; raise Exit
      | c -> incr i; Buffer.add_char b c
    done;
    invalid_arg "Termcode.get_name: missing closing parenthesis"
  with Exit ->
    let id = Buffer.contents b in
    Hashtbl.add dict_table !dict_count id;
(*
    Format.eprintf "%d -> %s@." !dict_count id;
*)
    incr dict_count;
    id

let get_num s n i =
  try while !i < String.length s do
    match String.get s !i with
      | ')' -> incr i; raise Exit
      | '0'..'9' as c ->
        incr i; n := !n * 10 + (Char.code c - Char.code '0')
      | _ ->
        invalid_arg "Termcode.get_num: decimal digit expected"
    done;
    invalid_arg "Termcode.get_num: missing closing parenthesis"
  with Exit ->
    try Hashtbl.find dict_table !n
    with Not_found ->
      invalid_arg
        ("Termcode.get_num: invalid ident number " ^ string_of_int !n)

let get_id s i =
  if !i >= String.length s then
    invalid_arg "Termcode.get_id: missing closing parenthesis";
  match String.get s !i with
    | '0'..'9' as c ->
      let n = ref (Char.code c - Char.code '0') in
      incr i;
      get_num s n i
    | ')' -> invalid_arg "Termcode.get_id: unexpected closing parenthesis"
    | c ->
      let b = Buffer.create 17 in
      Buffer.add_char b c;
      incr i;
      get_name s b i


(*
let store_id s i =
  let b = Buffer.create 17 in
  try while !i < String.length s do
    match String.get s !i with
      | ')' -> incr i; raise Exit
      | c -> incr i; Buffer.add_char b c
    done;
    invalid_arg "Termcode.store_id: missing closing parenthesis"
  with Exit ->
    let id = Buffer.contents b in
    try
      let n = Hashtbl.find reverse_ident_table id in
      string_of_int n
    with
        Not_found ->
          Hashtbl.add reverse_ident_table id !reverse_dict_count;
          incr reverse_dict_count;
          id
*)

(* {2 Shapes} *)

type shape = string

let string_of_shape s = s
(*
  try
  let l = String.length s in
  let r = Buffer.create l in
  let i = ref 0 in
  while !i < l do
  match String.get s !i with
    | '(' ->
      Buffer.add_char r '(';
      incr i;
      Buffer.add_string r (store_id s i);
      Buffer.add_char r ')'
    | c -> Buffer.add_char r c; incr i
  done;
  Buffer.contents r
  with e ->
    Format.eprintf "Error while reading shape [%s]@." s;
    raise e
*)

let shape_of_string s =
  try
  let l = String.length s in
  let r = Buffer.create l in
  let i = ref 0 in
  while !i < l do
  match String.get s !i with
    | '(' -> incr i; Buffer.add_string r (get_id s i)
    | c -> Buffer.add_char r c; incr i
  done;
  Buffer.contents r
  with e ->
    Format.eprintf "Error while reading shape [%s]@." s;
    raise e

(* tests
let _ = reset_dict () ; shape_of_string "a(b)cde(0)"
let _ = reset_dict () ; shape_of_string "a(bc)d(e)f(1)g(0)h"
let _ = reset_dict () ; shape_of_string "(abc)(def)(1)(0)(1)"
let _ = reset_dict () ; shape_of_string "(abcde)(fghij)(1)(0)(1)"
*)

let equal_shape (x:string) y = x = y
(* unused
let print_shape fmt s = Format.pp_print_string fmt (string_of_shape s)
*)

let debug = Debug.register_info_flag "session_pairing"
  ~desc:"Print@ debugging@ messages@ about@ reconstruction@ of@ \
         session@ trees@ after@ modification@ of@ source@ files."

let current_shape_version = 4

type shape_version = SV1 | SV2 | SV3

(* similarity code of terms, or of "shapes"

example:

  shape(forall x:int, x * x >= 0) =
         Forall(Int,App(infix_gteq,App(infix_st,Tvar 0,Tvar 0),Const(0)))
       i.e: de bruijn indexes, first-order term

*)

let vs_rename_alpha c h vs = incr c; Mvs.add vs !c h

let vl_rename_alpha c h vl = List.fold_left (vs_rename_alpha c) h vl

let rec pat_rename_alpha c h p = match p.pat_node with
  | Pvar v -> vs_rename_alpha c h v
  | Pas (p, v) -> pat_rename_alpha c (vs_rename_alpha c h v) p
  | Por (p, _) -> pat_rename_alpha c h p
  | _ -> Term.pat_fold (pat_rename_alpha c) h p


let tag_and = "A"
let tag_app = "a"
let tag_case = "C"
let tag_const = "c"
let tag_exists = "E"
let tag_eps = "e"
let tag_forall = "F"
let tag_false = "f"
let tag_impl = "I"
let tag_if = "i"
let tag_let = "L"
let tag_not = "N"
let tag_or = "O"
let tag_iff = "q"
let tag_true = "t"
let tag_var = "V"
let tag_wild = "w"
let tag_as = "z"


let id_string_shape ~push id acc = 
  push id acc
(*
  let l = String.length id in
  if l <= 4 then push id acc else
  (* sanity check *)
  if (match String.get id 0 with
      | '0'..'9' -> true
      | _ ->
        try
          let (_:int) = String.index id ')' in
          true
        with Not_found -> false)
    then push id acc
    else push ")" (push id (push "(" acc))
*)

let ident_shape ~push id acc =
  id_string_shape ~push id.Ident.id_string acc

let const_shape ~push acc c =
  let b = Buffer.create 17 in
  Format.bprintf b "%a" Pretty.print_const c;
  push (Buffer.contents b) acc

let rec pat_shape ~(push:string->'a->'a) c m (acc:'a) p : 'a =
  match p.pat_node with
    | Pwild -> push tag_wild acc
    | Pvar _ -> push tag_var acc
    | Papp (f, l) ->
        List.fold_left (pat_shape ~push c m)
          (ident_shape ~push f.ls_name (push tag_app acc))
          l
    | Pas (p, _) -> push tag_as (pat_shape ~push c m acc p)
    | Por (p, q) ->
        pat_shape ~push c m (push tag_or (pat_shape ~push c m acc q)) p

let rec t_shape ~version ~(push:string->'a->'a) c m (acc:'a) t : 'a =
  let fn = t_shape ~version ~push c m in
  match t.t_node with
    | Tconst c -> const_shape ~push (push tag_const acc) c
    | Tvar v ->
        let x =
          try string_of_int (Mvs.find v m)
          with Not_found -> v.vs_name.Ident.id_string
        in
        push x (push tag_var acc)
    | Tapp (s,l) ->
        List.fold_left fn
          (ident_shape ~push s.ls_name (push tag_app acc))
          l
    | Tif (f,t1,t2) ->
      begin match version with
      | SV1 | SV2 -> fn (fn (fn (push tag_if acc) f) t1) t2
      | SV3 -> fn (fn (fn (push tag_if acc) t2) t1) f
      end
    | Tcase (t1,bl) ->
        let br_shape acc b =
          let p,t2 = t_open_branch b in
          match version with
          | SV1 | SV2 ->
            let acc = pat_shape ~push c m acc p in
            let m = pat_rename_alpha c m p in
            t_shape ~version ~push c m acc t2
          | SV3 ->
            let m1 = pat_rename_alpha c m p in
            let acc = t_shape ~version ~push c m1 acc t2 in
            pat_shape ~push c m acc p
        in
        begin match version with
        | SV1 | SV2 ->
          List.fold_left br_shape (fn (push tag_case acc) t1) bl
        | SV3 ->
          let acc = push tag_case acc in
          let acc = List.fold_left br_shape acc bl in
          fn acc t1
        end
    | Teps b ->
        let u,f = t_open_bound b in
        let m = vs_rename_alpha c m u in
        t_shape ~version ~push c m (push tag_eps acc) f
    | Tquant (q,b) ->
        let vl,triggers,f1 = t_open_quant b in
        let m = vl_rename_alpha c m vl in
        let hq = match q with Tforall -> tag_forall | Texists -> tag_exists in
        (* argument first, intentionally, to give more weight on A in
           forall x,A *)
        let acc = push hq (t_shape ~version ~push c m acc f1) in
        List.fold_right
          (fun trigger acc ->
             List.fold_right
               (fun t acc ->
                  t_shape ~version ~push c m acc t)
               trigger acc)
          triggers acc
    | Tbinop (o,f,g) ->
        let tag = match o with
          | Tand -> tag_and
          | Tor -> tag_or
          | Timplies -> tag_impl
          | Tiff -> tag_iff
        in
        fn (push tag (fn acc g)) f
          (* g first, intentionally, to give more weight on B in A->B *)
    | Tlet (t1,b) ->
        let u,t2 = t_open_bound b in
        let m = vs_rename_alpha c m u in
        begin
          match version with
            | SV1 ->
              t_shape ~version ~push c m (fn (push tag_let acc) t1) t2
            | SV2 | SV3 ->
              (* t2 first, intentionally *)
              fn (push tag_let (t_shape ~version ~push c m acc t2)) t1
        end
    | Tnot f ->
      begin match version with
      | SV1 | SV2 -> push tag_not (fn acc f)
      | SV3 -> fn (push tag_not acc) f
      end
    | Ttrue -> push tag_true acc
    | Tfalse -> push tag_false acc

(* dead code
let t_shape_buf ?(version=current_shape_version) t =
  let b = Buffer.create 17 in
  let push t () = Buffer.add_string b t in
  let () = t_shape ~version ~push (ref (-1)) Mvs.empty () t in
  Buffer.contents b
*)

let t_shape_task ~version t =
  let b = Buffer.create 17 in
  let push t () = Buffer.add_string b t in
  begin match version with
  | SV1 | SV2 -> ()
  | SV3 ->
    let _, expl, _ = goal_expl_task ~root:false t in
    match expl with
      | None -> ()
      | Some expl -> id_string_shape ~push expl () 
  end;
  let f = Task.task_goal_fmla t in
  let () = t_shape ~version ~push (ref (-1)) Mvs.empty () f in
  Buffer.contents b

let t_shape_task ?(version=current_shape_version) t =
  let version = match version with
    | 1 -> SV1 | 2 -> SV2 | 3 | 4 -> SV3
    | _ -> assert false
  in
  t_shape_task ~version t

(* Checksums *)

type checksum = string
let print_checksum = Format.pp_print_string
let string_of_checksum x = x
let checksum_of_string x = x
let equal_checksum x y = (x : checksum) = y
let dumb_checksum = ""

type checksum_version = CV1 | CV2

module Checksum = struct

  let char (_,_,_,buf) c = Buffer.add_char buf c
  let int (_,_,_,buf as b) i =
    char b 'i'; Buffer.add_string buf (string_of_int i)
  let string (_,_,_,buf as b) s =
    char b '"'; Buffer.add_string buf (String.escaped s); char b '"'
  let option e b = function None -> char b 'n' | Some x -> char b 's'; e b x
  let list e b l = char b '['; List.iter (e b) l; char b ']'

  let ident_v1, clear_ident_v1 =
    let hident = Ident.Hid.create 17 in
    let c = ref 0 in
    (fun b id ->
      int b (try Ident.Hid.find hident id
        with Not_found -> incr c; Ident.Hid.add hident id !c; !c)),
    (fun () -> Ident.Hid.clear hident; c := 0)

  let ident_v2 (_,c,m,_ as b) id =
    let i = match Ident.Mid.find_opt id !m with
      | Some i -> i
      | None -> incr c; m := Ident.Mid.add id !c !m; !c
    in
    int b i

  let ident (v,_,_,_ as b) id = match v with
    | CV1 -> ident_v1 b id
    | CV2 -> ident_v2 b id

  let const b c =
    let buf = Buffer.create 17 in
    Format.bprintf buf "%a" Pretty.print_const c;
    string b (Buffer.contents buf)

  let tvsymbol b tv = ident b tv.Ty.tv_name

  let rec ty b t = match t.Ty.ty_node with
    | Ty.Tyvar tv -> char b 'v'; tvsymbol b tv
    | Ty.Tyapp (ts, tyl) -> char b 'a'; ident b ts.Ty.ts_name; list ty b tyl

  let vsymbol (v,_,_,_ as b) vs = match v with
    | CV1 -> ty b vs.vs_ty
    | CV2 -> ident b vs.vs_name; ty b vs.vs_ty

  (* start: _ V ident a o *)
  let rec pat b p = match p.pat_node with
    | Pwild -> char b '_'
    | Pvar vs -> char b 'v'; vsymbol b vs
    | Papp (f, l) -> char b 'a'; ident b f.ls_name; list pat b l
    | Pas (p, vs) -> char b 's'; pat b p; vsymbol b vs
    | Por (p, q) -> char b 'o'; pat b p; pat b q

  (* start: c V v i m e F E A O I q l n t f *)
  let rec term b t = match t.t_node with
    | Tconst c -> const b c
    | Tvar v -> char b 'v'; ident b v.vs_name
    | Tapp (s, l) -> char b 'a'; ident b s.ls_name; list term b l
    | Tif (f, t1, t2) -> char b 'i'; term b f; term b t1; term b t2
    | Tcase (t1, bl) ->
        let branch b br =
          let p, t2 = t_open_branch br in
          pat b p; term b t2
        in
        char b 'm'; term b t1; list branch b bl
    | Teps bf ->
        let vs, f = t_open_bound bf in
        char b 'e'; vsymbol b vs; term b f
    | Tquant (q, bf) ->
        let vl, triggers, f1 = t_open_quant bf in
        char b (match q with Tforall -> 'F' | Texists -> 'E');
        list vsymbol b vl;
        list (list term) b triggers;
        term b f1
    | Tbinop (o, f, g) ->
        let tag = match o with
          | Tand -> 'A'
          | Tor -> 'O'
          | Timplies -> 'I'
          | Tiff -> 'q'
        in
        char b tag; term b f; term b g
    | Tlet (t1, bt) ->
        let vs, t2 = t_open_bound bt in
        char b 'l'; vsymbol b vs; term b t1;
        term b t2
    | Tnot f -> char b 'n'; term b f
    | Ttrue -> char b 't'
    | Tfalse -> char b 'f'

  let tysymbol b ts =
    ident b ts.Ty.ts_name;
    list tvsymbol b ts.Ty.ts_args;
    option ty b ts.Ty.ts_def

  let lsymbol b ls =
    ident b ls.ls_name;
    list ty b ls.ls_args;
    option ty b ls.ls_value;
    list tvsymbol b (Ty.Stv.elements ls.ls_opaque);
    int b ls.ls_constr

  (* start: T D R L I P (C M) *)
  let decl b d = match d.Decl.d_node with
    | Decl.Dtype ts ->
        char b 'T'; tysymbol b ts
    | Decl.Ddata ddl ->
        let constructor b (ls, l) = lsymbol b ls; list (option lsymbol) b l in
        let data_decl b (ts, cl) = tysymbol b ts; list constructor b cl in
        char b 'D'; list data_decl b ddl
    | Decl.Dparam ls ->
        char b 'R'; lsymbol b ls
    | Decl.Dlogic ldl ->
        let logic_decl b (ls, defn) =
          lsymbol b ls;
          let vl, t = Decl.open_ls_defn defn in
          list vsymbol b vl;
          term b t
        in
        char b 'L'; list logic_decl b ldl
    | Decl.Dind (s, idl) ->
        let clause b (pr, f) =
          ident b pr.Decl.pr_name; term b f in
        let ind_decl b (ls, cl) = lsymbol b ls; list clause b cl in
        char b 'I'; char b (match s with Decl.Ind -> 'i' | Decl.Coind -> 'c');
        list ind_decl b idl
    | Decl.Dprop (k,n,t) ->
        let tag = match k with
          | Decl.Plemma -> "PL"
          | Decl.Paxiom -> "PA"
          | Decl.Pgoal  -> "PG"
          | Decl.Pskip  -> "PS"
        in
        string b tag;
        ident b n.Decl.pr_name;
        term b t

  let meta_arg_type b = function
    | Theory.MTty       -> char b 'y'
    | Theory.MTtysymbol -> char b 't'
    | Theory.MTlsymbol  -> char b 'l'
    | Theory.MTprsymbol -> char b 'p'
    | Theory.MTstring   -> char b 's'
    | Theory.MTint      -> char b 'i'

  let meta b m =
    string b m.Theory.meta_name;
    list meta_arg_type b m.Theory.meta_type;
    char b (if m.Theory.meta_excl then 't' else 'f')

  let meta_arg b = function
    | Theory.MAty t  -> char b 'y'; ty b t
    | Theory.MAts ts -> char b 't'; ident b ts.Ty.ts_name
    | Theory.MAls ls -> char b 'l'; ident b ls.ls_name
    | Theory.MApr pr -> char b 'p'; ident b pr.Decl.pr_name
    | Theory.MAstr s -> char b 's'; string b s
    | Theory.MAint i -> char b 'i'; int b i

  let tdecl b d = match d.Theory.td_node with
    | Theory.Decl d -> decl b d
    | Theory.Use _ -> assert false
    | Theory.Clone (th, _) ->
        char b 'C'; ident b th.Theory.th_name; list string b th.Theory.th_path
    | Theory.Meta (m, mal) -> char b 'M'; meta b m; list meta_arg b mal

  let task_v1 =
    let c = ref 0 in
    let m = ref Ident.Mid.empty in
    let b = Buffer.create 8192 in
    fun t ->
      Task.task_iter (tdecl (CV1,c,m,b)) t;
      clear_ident_v1 ();
      let dnew = Digest.string (Buffer.contents b) in
      Buffer.clear b;
      Digest.to_hex dnew

  let task_v2 =
    let c = ref 0 in
    let m = ref Ident.Mid.empty in
    let b = Buffer.create 8192 in
    let task_hd t (cold,mold,dold) =
      c := cold;
      m := mold;
      tdecl (CV2,c,m,b) t.Task.task_decl;
      Buffer.add_string b (Digest.to_hex dold);
      let dnew = Digest.string (Buffer.contents b) in
      Buffer.clear b;
      let mnew = match t.Task.task_decl.Theory.td_node with
        | Theory.Decl { Decl.d_news = s } ->
            Ident.Sid.fold (fun id a ->
              Ident.Mid.add id (Ident.Mid.find id !m) a) s mold
        | _ -> !m in
      !c, mnew, dnew
    in
    let tr = Trans.fold task_hd (0, Ident.Mid.empty, Digest.string "") in
    fun t ->
      let _,_,dnew = Trans.apply tr t in
      Digest.to_hex dnew

  let task ~version t = match version with
    | CV1 -> task_v1 t
    | CV2 -> task_v2 t
end

let task_checksum ?(version=current_shape_version) t =
  let version = match version with
    | 1 | 2 | 3 -> CV1
    | 4 -> CV2
    | _ -> assert false
  in
  Checksum.task ~version t

(*************************************************************)
(* Pairing of new and old subgoals                           *)
(*************************************************************)

(* we have an ordered list of new subgoals

     newgoals = [g1; g2; g3; ...]

   and a list of old subgoals

     oldgoals = [h1 ; h2 ; ... ]

   we build a list

     [g1, None; g2, Some (h3, false); g3, Some (h2, true); ...]

   where each new goal is mapped either to
   - None: no pairing at all
   - Some (h, false): exact matching (equal checksums)
   - Some (h, true): inexact matching (goal obsolete)
*)

module type S = sig
  type t
  val checksum : t -> string
  val shape    : t -> string
  val name     : t -> Ident.ident
end

module Pairing(Old: S)(New: S) = struct

  let rec lcp n s1 s2 =
    if String.length s1 <= n || String.length s2 <= n then n
    else if s1.[n] = s2.[n] then lcp (n+1) s1 s2 else n
  let lcp = lcp 0

  open Ident

  type any_goal = Old of Old.t | New of New.t

  (* doubly linked lists; left and right bounds point to themselves *)

  type node = {
    mutable  prev: node;
            shape: string;
              elt: any_goal;
    mutable valid: bool;
    mutable  next: node;
  }

  let mk_node g =
    let s = match g with Old g -> Old.shape g | New g -> New.shape g in
    let rec n = { prev = n; shape = s; elt = g; next = n; valid = true } in n

  let rec iter_pairs f = function
    | [] | [_] -> ()
    | x :: (y :: _ as l) -> f x y; iter_pairs f l

  let build_list = iter_pairs (fun x y -> x.next <- y; y.prev <- x)

  let remove x =
    x.valid <- false;
    let p = x.prev and n = x.next in
    if p == x then n.prev <- n (* left bound *)
    else if n == x then p.next <- p (* right bound *)
    else begin p.next <- n; n.prev <- p end

  (* priority queues for pairs of nodes *)

  module E = struct
    type t = int * (node * node)
    let compare (v1, _) (v2, _) = Pervasives.compare v2 v1
  end
  module PQ = Pqueue.Make(E)

  let dprintf = Debug.dprintf debug

  let associate oldgoals newgoals =
    (* set up an array [result] containing the solution
       [new_goal_index g] returns the index of goal [g] in that array *)
    let new_goal_index = Hid.create 17 in
    let result =
      let make i newg =
        Hid.add new_goal_index (New.name newg) i; (newg, None) in
      Array.mapi make (Array.of_list newgoals) in
    let new_goal_index newg =
      try Hid.find new_goal_index (New.name newg)
      with Not_found -> assert false in
    (* phase 1: pair goals with identical checksums *)
    let old_checksums = Hashtbl.create 17 in
    let add oldg = Hashtbl.add old_checksums (Old.checksum oldg) oldg in
    List.iter add oldgoals;
    let collect acc newg =
      let c = New.checksum newg in
      try
        let oldg = Hashtbl.find old_checksums c in
        Hashtbl.remove old_checksums c;
        result.(new_goal_index newg) <- (newg, Some (oldg, false));
        acc
      with Not_found ->
        mk_node (New newg) :: acc
    in
    let newgoals = List.fold_left collect [] newgoals in
    let add _ oldg acc = mk_node (Old oldg) :: acc in
    let allgoals = Hashtbl.fold add old_checksums newgoals in
    Hashtbl.clear old_checksums;
    (* phase 2: pair goals according to shapes *)
    let compare e1 e2 = Pervasives.compare e1.shape e2.shape in
    let allgoals = List.sort compare allgoals in
    build_list allgoals;
    if allgoals <> [] then begin
      let dummy = let n = List.hd allgoals (* safe *) in 0, (n, n) in
      let pq = PQ.create ~dummy in
      let add x y = match x.elt, y.elt with
        | Old _, New _ | New _, Old _ -> PQ.add pq (lcp x.shape y.shape, (x, y))
        | Old _, Old _ | New _, New _ -> () in
      iter_pairs add allgoals;
      (* FIXME: exit earlier, as soon as we get min(old,new) pairs *)
      while not (PQ.is_empty pq) do
        let _, (x, y) = PQ.extract_min pq in
        if x.valid && y.valid then begin
          let o, n = match x.elt, y.elt with
            | New n, Old o | Old o, New n -> o, n | _ -> assert false in
          dprintf "[assoc] new pairing@.";
          result.(new_goal_index n) <- n, Some (o, true);
          if x.prev != x && y.next != y then add x.prev y.next;
          remove x;
          remove y
        end
      done
    end;
    Array.to_list result

(*
  let associate oldgoals newgoals =
    try List.map2 (fun o n -> n, Some (o, true)) oldgoals newgoals
    with Invalid_argument _ -> associate oldgoals newgoals
*)
end
