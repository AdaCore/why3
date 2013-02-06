(* For an occurence of a float literal such as 12.3, replace it by
   from_int 12 + 0.3
 and add an axiom
   12.0 = from_int 12
*)

open Number
open Decl
open Theory
open Task
open Term

(*
let print_int_const fmt c =
  match c with
  | IConstDec s
  | IConstHex s
  | IConstOct s
  | IConstBin s -> Format.fprintf fmt "%s" s

let print_real_const fmt c =
  match c with
  | RConstDec (s1,s2,Some s3) ->
      Format.fprintf fmt "dec - %s - %s - %s" s1 s2 s3
  | RConstDec (s1,s2,None) ->
      Format.fprintf fmt "dec - %s - %s" s1 s2
  | RConstHex (s1,s2,Some s3) ->
      Format.fprintf fmt "hex - %s - %s - %s" s1 s2 s3
  | RConstHex (s1,s2,None) ->
      Format.fprintf fmt "hex - %s - %s" s1 s2

let print_num fmt c =
  match c with
  | ConstInt ic -> Format.fprintf fmt "int:(%a)" print_int_const ic
  | ConstReal rc -> Format.fprintf fmt "real:(%a)" print_real_const rc
*)

module Compare_Num =
  struct
    type t = Number.real_constant

    let opt_compare s1 s2 =
      match s1, s2 with
      | None, None -> 0
      | None, _ -> -1
      | _, None -> 1
      | Some s1, Some s2 -> Pervasives.compare s1 s2

    let compare a b =
      match a, b with
      | RConstDec (s11, s12, s13), RConstDec (s21, s22, s23)
      | RConstHex (s11, s12, s13), RConstHex (s21, s22, s23) ->
          let c = Pervasives.compare s11 s21 in
          if c = 0 then
            let c = Pervasives.compare s12 s22 in
            if c = 0 then opt_compare s13 s23
            else c
          else c
      | RConstDec _, _ -> -1
      | _, RConstDec _ -> 1
  end

module Mnum = Extmap.Map.Make (Compare_Num)

let const_replace repl =
  (* the function repl is expected to accept a real constant and return either
     [None], if this constant is not "interesting", or
     Some (trans, from_int, int_part), where
       [trans] is the sum from_int (int_part) + (fractional part),
       [from_int] is just the part "from_int (int_part)"
       [int_part] is the int_part as a float.
     For example, for 63.1, we obtain
       trans = from_int 63 + 0.1
       from_int = from_int 63
       int_part = 63.0

     const_replace now replaces every "interesting" real constant by [trans].
     In addition, it fills a map with [int_part] |-> [from_int] *)
  let rec const_replace (acc : term Mnum.t) t =
    let acc, t = t_map_fold const_replace acc t in
    match t.t_node with
    | Tconst (ConstReal rc) ->
        begin match repl rc with
        | Some (trans, from_int, int_part) ->
            Mnum.add int_part from_int acc, trans
        | None -> acc, t
        end
    | _ -> acc, t
  in
  const_replace

let extract_from_rc rc =
  (* given a real decimal constant that is different from 0 and 1, return a
     pair (i, frac) where [i] is the integer part and [frac] is the fractional
     part *)
  (* We special case 0.0 and 1.0 here, because a) these constants appear early
     in the Why standard library, before [from_int] is known, and also because
     Why already knows that 0.0 = 0 and 1.0 = 1. *)
  match rc with
  | RConstDec (int, frac, None) ->
      (* special case for 0 and 1 *)
      if (int = "0" || int = "1") && frac = "0" then None
      else Some (int, frac)
  | _ -> None

let add_axioms map task =
  (* given a map [int_part] |-> [from_int_term], generate axioms of the form
     int_part = from_int_term *)
  Mnum.fold (fun re fr task ->
    let sym = create_prsymbol (Ident.id_fresh "real const axiom") in
    let term = t_equ (t_const (ConstReal re)) fr in
    Task.add_decl task (create_prop_decl Paxiom sym term)) map task

let float_lift th_from_int th_real =
  let from_int_ls =
    (* the symbol [from_int] *)
    ns_find_ls th_from_int.th_export ["from_int"] in
  let real_plus =
    (* the symbol [(+)] for reals *)
    ns_find_ls th_real.th_export ["infix +"] in
  let t_add a b =
    (* function that builds "a + b" from a and b *)
    t_app real_plus [a;b] (Some Ty.ty_real) in
  let t_from_int t =
    (* function that builds "from_int a " from a *)
    t_app from_int_ls [t] (Some Ty.ty_real) in
  let rc_to_new_term rc =
    (* function that given a real constant x.y, builds the term
       from_int (x) + 0.y, and returns [from_int x] and [x], see also the
       documentation for [const_replace] *)
    match extract_from_rc rc with
    | Some (i, frac) ->
        let i_t = t_from_int (t_const (ConstInt (Number.int_const_dec i))) in
        let frac_t =
          t_const (ConstReal (Number.real_const_dec "0" frac None)) in
        let trans =
          if i = "0" then frac_t
          else if frac = "0" then i_t
          else t_add i_t frac_t
        in
        Some (trans, i_t, Number.real_const_dec i "0" None)
    | None -> None
  in
  let replace = const_replace rc_to_new_term in
  Trans.fold_map (fun thd ((acc : term Mnum.t), task) ->
    (* iterate over all declarations that contain terms, potentially replace
       constants, and collect associations *)
    match thd.task_decl.td_node with
    | Decl { d_node = Dlogic ld } ->
        let acc, ld = List.fold_left (fun (acc, ld) (fs, defn) ->
          let vls, t = open_ls_defn defn in
          let acc, t = replace acc t in
          acc, make_ls_defn fs vls t :: ld) (acc,[]) ld in
        let task = Task.add_decl task (create_logic_decl ld) in
        acc, task
    | Decl { d_node = Dprop (Paxiom, ps, term) } ->
        let acc, term = replace acc term in
        let task = Task.add_decl task (create_prop_decl Paxiom ps term) in
        acc, task
    | Decl { d_node = Dprop (Pgoal, ps, term) } ->
        (* We transform the goal term to get the constants in the goal; Then,
           we add axioms for all collected constants, including in previous
           axioms and definitions, and then we add the goal as well. *)
        let acc, term = replace acc term in
        let task = add_axioms acc task in
        Mnum.empty, Task.add_decl task (create_prop_decl Pgoal ps term)
    | _ -> acc, add_tdecl task thd.task_decl
  ) Mnum.empty None

let () =
  Trans.register_env_transform ~desc:"float literals" "float_literal"
    (fun env ->
      let th_from_int = Env.find_theory env ["real"] "FromInt" in
      let th_real = Env.find_theory env ["real"] "Real" in
      float_lift th_from_int th_real)
