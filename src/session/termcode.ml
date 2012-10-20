(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
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

type shape    = string
let print_shape = Format.pp_print_string
let string_of_shape x = x
let shape_of_string x = x

let debug = Debug.register_info_flag "session_pairing"
  ~desc:"About@ the@ way@ old@ goals@ recorded@ in@ sessions@ are@ paired@ \
         with@ new@ goals@ obtained@ after@ modifications@ of@ the@ source@ \
         file."

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
let tag_Dtype = "Dt"
let tag_Ddata = "Dd"
let tag_Dparam = "Dv"
let tag_Dlogic = "Dl"
let tag_Dind = "Di"
let tag_Dprop = "Dp"
let tag_exists = "E"
let tag_eps = "e"
let tag_forall = "F"
let tag_false = "f"
let tag_impl = "I"
let tag_if = "i"
let tag_let = "L"
let tag_not = "N"
let tag_or = "O"
let tag_Plemma = "Pl"
let tag_Paxiom = "Pa"
let tag_Pgoal = "Pg"
let tag_Pskip = "Ps"
let tag_iff = "q"
let tag_true = "t"
let tag_tDecl = "TD"
let tag_tClone = "TC"
let tag_tUse = "TU"
let tag_tMeta = "TM"
let tag_var = "V"
let tag_wild = "w"
let tag_as = "z"

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
          (push (f.ls_name.Ident.id_string) (push tag_app acc))
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
          (push (s.ls_name.Ident.id_string) (push tag_app acc))
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

(*
let t_shape_list t =
  let push t l = t::l in
  List.rev (t_shape ~push (ref (-1)) Mvs.empty [] t)

let pr_shape_list fmt t =
  List.iter (fun s -> Format.fprintf fmt "%s" s) (t_shape_list t)

*)

(* shape of a task *)

let param_decl_shape ~(push:string->'a->'a) (acc:'a) ls : 'a =
  push (ls.ls_name.Ident.id_string) acc

let logic_decl_shape ~version ~(push:string->'a->'a) (acc:'a) (ls,def) : 'a =
  let acc = push (ls.ls_name.Ident.id_string) acc in
  let vl,t = Decl.open_ls_defn def in
  let c = ref (-1) in
  let m = vl_rename_alpha c Mvs.empty vl in
  t_shape ~version ~push c m acc t

let logic_ind_decl_shape ~version ~(push:string->'a->'a) (acc:'a) (ls,cl) : 'a =
  let acc = push (ls.ls_name.Ident.id_string) acc in
  List.fold_right
    (fun (_,t) acc -> t_shape ~version ~push (ref (-1)) Mvs.empty acc t)
    cl acc

let propdecl_shape ~version ~(push:string->'a->'a) (acc:'a) (k,n,t) : 'a =
  let tag = match k with
    | Decl.Plemma -> tag_Plemma
    | Decl.Paxiom -> tag_Paxiom
    | Decl.Pgoal -> tag_Pgoal
    | Decl.Pskip -> tag_Pskip
  in
  let acc = push tag acc in
  let acc = push n.Decl.pr_name.Ident.id_string acc in
  t_shape ~version ~push (ref(-1)) Mvs.empty acc t

let decl_shape ~version ~(push:string->'a->'a) (acc:'a) d : 'a =
  match d.Decl.d_node with
    | Decl.Dtype _ts ->
        push tag_Dtype acc
    | Decl.Ddata tyl ->
        List.fold_right
          (fun _ty acc -> acc)
          tyl (push tag_Ddata acc)
    | Decl.Dparam ls ->
        param_decl_shape ~push (push tag_Dparam acc) ls
    | Decl.Dlogic ldl ->
        List.fold_right
          (fun d acc -> logic_decl_shape ~version ~push acc d)
          ldl (push tag_Dlogic acc)
    | Decl.Dind (_, idl) ->
        List.fold_right
          (fun d acc -> logic_ind_decl_shape ~version ~push acc d)
          idl (push tag_Dind acc)
    | Decl.Dprop pdecl ->
        propdecl_shape ~version ~push (push tag_Dprop acc) pdecl

let tdecl_shape ~version ~(push:string->'a->'a) (acc:'a) t : 'a =
  match t.Theory.td_node with
    | Theory.Decl d -> decl_shape ~version ~push (push tag_tDecl acc) d
    | Theory.Meta _ -> push tag_tMeta acc
    | Theory.Clone _ -> push tag_tClone acc
    | Theory.Use _ -> push tag_tUse acc

let rec task_shape ~version ~(push:string->'a->'a) (acc:'a) t : 'a =
  match t with
    | None -> acc
    | Some t ->
     task_shape ~version ~push (tdecl_shape ~version ~push acc t.Task.task_decl)
          t.Task.task_prev


(* checksum of a task
   it is the MD5 digest of the shape
*)

let task_checksum ?(version=current_shape_version) t =
  let b = Buffer.create 257 in
  let push t () = Buffer.add_string b t in
  let () = task_shape ~version ~push () t in
  let shape = Buffer.contents b in
  Digest.to_hex (Digest.string shape)



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
