(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term

type checksum = string
let print_checksum = Format.pp_print_string
let string_of_checksum x = x
let checksum_of_string x = x
let equal_checksum x y = (x : checksum) = y
let dumb_checksum = ""

type shape = string
let print_shape = Format.pp_print_string
let string_of_shape x = x
let shape_of_string x = x

let debug = Debug.register_info_flag "session_pairing"
  ~desc:"Print@ debugging@ messages@ about@ reconstruction@ of@ \
         session@ trees@ after@ modification@ of@ source@ files."

let current_shape_version = 2

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

let ident_shape ~push id acc = push id.Ident.id_string acc

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
    | Tif (f,t1,t2) -> fn (fn (fn (push tag_if acc) f) t1) t2
    | Tcase (t1,bl) ->
        let br_shape acc b =
          let p,t2 = t_open_branch b in
          let acc = pat_shape ~push c m acc p in
          let m = pat_rename_alpha c m p in
          t_shape ~version ~push c m acc t2
        in
        List.fold_left br_shape (fn (push tag_case acc) t1) bl
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
            | 1 ->
              t_shape ~version ~push c m (fn (push tag_let acc) t1) t2
            | 2 ->
              (* t2 first, intentionally *)
              fn (push tag_let (t_shape ~version ~push c m acc t2)) t1
            | _ -> assert false
        end
    | Tnot f -> push tag_not (fn acc f)
    | Ttrue -> push tag_true acc
    | Tfalse -> push tag_false acc

let t_shape_buf ?(version=current_shape_version) t =
  let b = Buffer.create 17 in
  let push t () = Buffer.add_string b t in
  let () = t_shape ~version ~push (ref (-1)) Mvs.empty () t in
  Buffer.contents b


module Checksum = struct

  let char = Buffer.add_char
  let int b i = char b 'i'; Buffer.add_string b (string_of_int i)
  let string b s =
    char b '"'; Buffer.add_string b (String.escaped s); char b '"'
  let option e b = function None -> char b 'n' | Some x -> char b 's'; e b x
  let list e b l = char b '['; List.iter (e b) l; char b ']'

  let ident_printer = Ident.create_ident_printer []
  let ident b id = string b (Ident.id_unique ident_printer id)

  let const b c =
    let buf = Buffer.create 17 in
    Format.bprintf buf "%a" Pretty.print_const c;
    string b (Buffer.contents buf)

  let tvsymbol b tv = ident b tv.Ty.tv_name

  let rec ty b t = match t.Ty.ty_node with
    | Ty.Tyvar tv -> char b 'v'; tvsymbol b tv
    | Ty.Tyapp (ts, tyl) -> char b 'a'; ident b ts.Ty.ts_name; list ty b tyl

  (* variable: the type, but not the name (we want alpha-equivalence) *)
  let vsymbol b vs = ty b vs.vs_ty

  (* start: _ V ident a o *)
  let rec pat b p = match p.pat_node with
    | Pwild -> char b '_'
    | Pvar vs -> char b 'v'; vsymbol b vs
    | Papp (f, l) -> char b 'a'; ident b f.ls_name; list pat b l
    | Pas (p, vs) -> char b 's'; pat b p; vsymbol b vs
    | Por (p, q) -> char b 'o'; pat b p; pat b q

  (* start: c V v i m e F E A O I q l n t f *)
  let rec term c m b t = match t.t_node with
    | Tconst c -> const b c
    | Tvar v ->
        begin try let x = Mvs.find v m in char b 'V'; int b x
        with Not_found -> char b 'v'; ident b v.vs_name end
    | Tapp (s, l) -> char b 'a'; ident b s.ls_name; list (term c m) b l
    | Tif (f, t1, t2) -> char b 'i'; term c m b f; term c m b t1; term c m b t2
    | Tcase (t1, bl) ->
        let branch b br =
          let p, t2 = t_open_branch br in
          pat b p;
          let m = pat_rename_alpha c m p in
          term c m b t2
        in
        char b 'm'; term c m b t1; list branch b bl
    | Teps bf ->
        let vs, f = t_open_bound bf in
        let m = vs_rename_alpha c m vs in
        char b 'e'; vsymbol b vs; term c m b f
    | Tquant (q, bf) ->
        let vl, triggers, f1 = t_open_quant bf in
        let m = vl_rename_alpha c m vl in
        char b (match q with Tforall -> 'F' | Texists -> 'E');
        list vsymbol b vl;
        list (list (term c m)) b triggers;
        term c m b f1
    | Tbinop (o, f, g) ->
        let tag = match o with
          | Tand -> 'A'
          | Tor -> 'O'
          | Timplies -> 'I'
          | Tiff -> 'q'
        in
        char b tag; term c m b f; term c m b g
    | Tlet (t1, bt) ->
        let vs, t2 = t_open_bound bt in
        char b 'l'; vsymbol b vs; term c m b t1;
        let m = vs_rename_alpha c m vs in
        term c m b t2
    | Tnot f -> char b 'n'; term c m b f
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

  (* start: T D R L I P *)
  let decl b d = match d.Decl.d_node with
    | Decl.Dtype ts ->
        (* FIXME: alpha-equivalence for type variables as well *)
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
          let c = ref (-1) in
          let m = vl_rename_alpha c Mvs.empty vl in
          list vsymbol b vl; (* FIXME: really needed? (we did lsymbol above) *)
          term c m b t
        in
        char b 'L'; list logic_decl b ldl
    | Decl.Dind (s, idl) ->
        let clause b (pr, f) =
          ident b pr.Decl.pr_name; term (ref (-1)) Mvs.empty b f in
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
        term (ref (-1)) Mvs.empty b t

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
    char b (if m.Theory.meta_excl then 't' else 'f');
    string b (string_of_format m.Theory.meta_desc) (* FIXME: necessary? *)

  let meta_arg b = function
    | Theory.MAty t  -> char b 'y'; ty b t
    | Theory.MAts ts -> char b 't'; ident b ts.Ty.ts_name
    | Theory.MAls ls -> char b 'l'; ident b ls.ls_name
    | Theory.MApr pr -> char b 'p'; ident b pr.Decl.pr_name
    | Theory.MAstr s -> char b 's'; string b s
    | Theory.MAint i -> char b 'i'; int b i

  let tdecl b d = match d.Theory.td_node with
    | Theory.Decl d -> decl b d
    | Theory.Use _ | Theory.Clone _ -> () (* FIXME: OK? *)
    | Theory.Meta (m, mal) -> char b 'M'; meta b m; list meta_arg b mal

  let task t =
    let b = Buffer.create 8192 in
    Ident.forget_all ident_printer;
    Task.task_iter (tdecl b) t;
    let s = Buffer.contents b in
    Digest.to_hex (Digest.string s)

end

let task_checksum ?(version=0) t = ignore version; Checksum.task t

(*************************)
(**       Pairing       **)

(** needed accessor *)
module type S = sig
  type t
  val checksum : t -> string
  val shape    : t -> string
  val name       : t -> Ident.ident
end

(*
module type Sold = sig
  type t
  val checksum : t -> string
  val shape    : t -> string
  val id       : t -> Ident.ident
(* .goal_name *)
end
*)

(*
module type Snew = sig
  type t
  val checksum : t -> string
  val shape    : t -> string
  (* Termcode.t_shape_buf ~version:!current_shape_version *)
  (*   (Task.task_goal_fmla g) *)

  val name     : t -> string (** for debugging *)
(* let id = (Task.task_goal g).Decl.pr_name in *)
(* let goal_name = gname.Ident.id_string ^ "." ^ (string_of_int (i+1)) in *)
(* let goal_name = Ident.id_register (Ident.id_derive goal_name id) in *)

  val id      : t -> Ident.ident
(* let id = (Task.task_goal g).Decl.pr_name in *)

(* let id = (Task.task_goal g).Decl.pr_name in *)
(* let goal_name = gname.Ident.id_string ^ "." ^ (string_of_int (i+1)) in *)
(* let goal_name = Ident.id_register (Ident.id_derive goal_name id) in *)


end
*)


(*************************************************************)
(* pairing of new and old subgoals of a given transformation *)
(*************************************************************)

(* we have an ordered list of new subgoals

           subgoals = [g1; g2; g3; ...]

   and a list of old subgoals

          old_subgoals = [h1 ; h2 ; ... ]

   we build a map from each new subgoal g to tuples
       (id,subgoal_name,subtask,sum,old_subgoal,obsolete)

   where
     id = name of the goal of g
     subgoal_name = name of parent goal with "dot n" added
     subtask = the corresponding task
     sum = the checksum of that task
     old_subgoal = ref to an optional old subgoal which is paired with g
     obsolete = true when paired to an old goal with different checksum

*)

module AssoMake (Old : S) (New : S) = struct

type 'a any_goal =
  | New_goal of int
  | Old_goal of Old.t

let array_map_list f l =
  let r = ref l in
  Array.init (List.length l)
    (fun i ->
       match !r with
         | [] -> assert false
         | x::rem -> r := rem; f i x)

let associate (old_goals : Old.t list) new_goals =
  (*
     we make a map of old goals indexed by their checksums
  *)
  let old_goals_map = Hashtbl.create 7 in
  List.iter
    (fun g -> Hashtbl.add old_goals_map (Old.checksum g) g)
    old_goals;
  (*
     we make an array of new goals with their numbers and checksums
  *)
  let new_goals_array =
    array_map_list
      (fun i g -> i,g)
      new_goals
  in
  let pairing_array =
    Array.make (Array.length new_goals_array) None
  in
  let obsolete_array =
    Array.make (Array.length new_goals_array) false
  in
  (*
     Phase 1: we first associate each new goal for which there is an
     old goal with the same checksum.
  *)
  let associate_goals ~obsolete i g =
    pairing_array.(i) <- Some g;
    obsolete_array.(i) <- obsolete;
    Hashtbl.remove old_goals_map (Old.checksum g)
  in
  Array.iter
    (fun (i,g) ->
       try
         let h = Hashtbl.find old_goals_map (New.checksum g) in
         (* an old goal has the same checksum *)
         Debug.dprintf debug
           "Merge phase 1: old goal '%s' -> new goal '%s'@."
           (Old.name h).Ident.id_string (New.name g).Ident.id_string;
         associate_goals ~obsolete:false i h
       with Not_found ->
         Debug.dprintf debug
           "Merge phase 1: no old goal -> new goal '%s'@."
           (New.name g).Ident.id_string;
         ())
    new_goals_array;
  (* Phase 2: we now build a list of all remaining new and old goals,
     ordered by shapes, then by name *)
  let old_goals_without_pairing =
    Hashtbl.fold
      (fun _ g acc ->
         let s = (Old.shape g) in
         if s = "" then
           (* We don't try to associate old goals without shapes:
              they will be paired in order in next phase *)
           acc
         else
           (s,Old_goal g)::acc)
      old_goals_map
      []
  in
  let all_goals_without_pairing =
    Array.fold_left
      (fun acc (i,g) ->
         match pairing_array.(i) with
           | Some _ -> acc
           | None ->
               let shape = New.shape g
                 (* Termcode.t_shape_buf ~version:!current_shape_version *)
                 (*   (Task.task_goal_fmla g) *)
               in
               (* shape_array.(i) <- shape; *)
               (shape,New_goal i)::acc)
      old_goals_without_pairing
      new_goals_array
  in
  let sort_by_shape =
    List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2)
      all_goals_without_pairing
  in
  if Debug.test_flag debug then begin
    Debug.dprintf debug "[Merge] pairing the following shapes:@.";
    List.iter
      (fun (s,g) ->
         match g with
           | New_goal _ ->
               Debug.dprintf debug "new: %s@." s
           | Old_goal _ ->
               Debug.dprintf debug "old: %s@." s)
      sort_by_shape;
  end;
  let rec similarity_shape n s1 s2 =
    if String.length s1 <= n || String.length s2 <= n then n else
      if s1.[n] = s2.[n] then similarity_shape (n+1) s1 s2
      else n
  in
(*  let rec match_shape (opt:int option) goals : bool =
    (* when [opt] is [Some n] then it means [goals] starts with a goal g
       which is already claimed to be associated by the former goal h.
       We return a boolean which is true when that first goal g was also
       claimed by the next goal, with a proximity measure larger than n,
       meaning that the former goal h cannot associate with g
    *)
    match goals with
      | [] -> false
      | (si,New_goal i)::rem ->
          begin match rem with
            | [] -> false
            | (_,New_goal _)::_ ->
                let (_:bool) = match_shape None rem in false
            | (sh,Old_goal h)::_ ->
                try_associate si i sh h opt rem
          end
      | (sh,Old_goal h)::rem ->
          begin match rem with
            | [] -> false
            | (_,Old_goal _)::_ ->
                let (_:bool) = match_shape None rem in false
            | (si,New_goal i)::_ ->
                try_associate si i sh h opt rem
          end
  and try_associate si i sh h opt rem =
    let n = similarity_shape 0 si sh in
    Debug.dprintf debug "[Merge] try_associate: claiming \
      similarity %d for new shape@\n%s@\nand old shape@\n%s@." n si sh;
    if (match opt with
      | None ->
          Debug.dprintf debug "[Merge] try_associate: \
            no previous claim@.";
          true
      | Some m ->
          Debug.dprintf debug "[Merge] try_associate: \
            previous claim was %d@." m;
          m < n)
    then
      (* try to associate i with h *)
      let b = match_shape (Some n) rem in
      if b then
        begin
          (* h or i was already paired in rem *)
          Debug.dprintf debug "[Merge] try_associate: \
            failed because claimed further@.";
          false
        end
      else
        begin
          Debug.dprintf debug "[Merge] try_associate: \
            succeeded to associate new goal@\n%s@\nwith \
            old goal@\n%s@." si sh;
          associate_goals ~obsolete:true i h;
          true
        end
    else
      (* no need to try to associate i with h *)
      begin
        Debug.dprintf debug "[Merge] try_associate: \
          no claim further attempted@.";
        let (_:bool) = match_shape None rem in
        false
      end
  in
  let (_:bool) = match_shape None sort_by_shape in
*)
  let rec match_shape (min:int) goals : bool * (string * 'a any_goal) list =
    (* try to associate in [goals] each pair of old and new goal whose
       similarity is at least [min]. Returns a pair [(b,rem)] where
       [rem] is the sublist of [goals] made of goals which have not
       been paired, and [b] is a boolean telling that the head of
       [rem] is the same has the head of [goals] *)
    match goals with
      | [] -> (true, goals)
      | ((si,New_goal i) as hd)::rem ->
          begin match rem with
            | [] -> (true, goals)
            | (_,New_goal _)::_ ->
                let (b,rem2) = match_shape min rem in
                if b then
                  (true, hd::rem2)
                else
                  match_shape min (hd::rem2)
            | (sh,Old_goal h)::_ ->
                try_associate min si i sh h hd rem
          end
      | ((sh,Old_goal h) as hd)::rem ->
          begin match rem with
            | [] -> (true, goals)
            | (_,Old_goal _)::_ ->
                let (b,rem2) = match_shape min rem in
                if b then
                  (true, hd::rem2)
                else
                  match_shape min (hd::rem2)
            | (si,New_goal i)::_ ->
                try_associate min si i sh h hd rem
          end
            (** si : shape of i
                i  : id of the new goal
                sh : shape of h
                h  : an old goal
                hd : the head
                rem : the tail of the list *)
  and try_associate min si i sh h hd rem =
    let n = similarity_shape 0 si sh in
    Debug.dprintf debug "[Merge] try_associate: claiming \
      similarity %d for new shape@\n%s@\nand old shape@\n%s@." n si sh;
    if n < min then
      begin
        Debug.dprintf debug "[Merge] try_associate: claiming \
          dropped because similarity lower than min = %d@." min;
        let (b,rem2) = match_shape min rem in
        if b then
          (true, hd::rem2)
        else
          match_shape min (hd::rem2)
      end
    else
      match match_shape n rem with
        | false, rem2 ->
            Debug.dprintf debug "[Merge] try_associate: claiming \
              dropped because head was consumed by larger similarity@.";
            match_shape min (hd::rem2)
        | true, [] -> assert false
        | true, _::rem2 ->
            Debug.dprintf debug "[Merge] try_associate: claiming \
              succeeded (similarity %d) for new shape@\n%s@\nand \
              old shape@\n%s@." n si sh;
            associate_goals ~obsolete:true i h;
            let (_,rem3) = match_shape min rem2 in
            (false, rem3)
  in
  let (_b,_rem) = match_shape 0 sort_by_shape in
  (*
     Phase 3: we now associate remaining new goals to the remaining
     old goals in the same order as original
  *)
  Debug.dprintf debug "[Merge] phase 3: associate remaining goals@.";
  let remaining_old_goals =
    Hashtbl.fold
      (fun _ g acc -> (Old.name g,g)::acc)
      old_goals_map
      []
  in
  let remaining_old_goals =
    ref (List.sort (fun (s1,_) (s2,_) ->
      String.compare s1.Ident.id_string s2.Ident.id_string)
           remaining_old_goals)
  in
  Array.iteri
    (fun i opt ->
       match opt with
         | Some _ -> ()
         | None ->
             match !remaining_old_goals with
               | [] -> ()
               | (_,h) :: rem ->
                   remaining_old_goals := rem;
                   associate_goals ~obsolete:true i h)
    pairing_array;

  Array.fold_right
    (fun (i,g) res -> (g, pairing_array.(i), obsolete_array.(i))::res)
    new_goals_array []

end

module AssoMake2 (Old : S) (New : S) = struct

  let rec lcp n s1 s2 =
    if String.length s1 <= n || String.length s2 <= n then n
    else if s1.[n] = s2.[n] then lcp (n+1) s1 s2 else n
  let lcp = lcp 0

  open Ident

  type any_goal = Old of Old.t | New of New.t

  (* doubly linked lists *)

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
        Hid.add new_goal_index (New.name newg) i; (newg, None, false) in
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
        result.(new_goal_index newg) <- (newg, Some oldg, false);
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
          x.valid <- false; y.valid <- false;
          let o, n = match x.elt, y.elt with
            | New n, Old o | Old o, New n -> o, n | _ -> assert false in
          dprintf "[assoc] new pairing@.";
          result.(new_goal_index n) <- n, Some o, true;
          if x.prev != x && y.next != y then add x.prev y.next;
          if x.prev != x then x.prev.next <- y.next else y.next.prev <- y.next;
          if y.next != y then y.next.prev <- x.prev else x.prev.next <- x.prev
        end
      done
    end;
    Array.to_list result

end
