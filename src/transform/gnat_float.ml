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

let const_replace repl =
  (* replace a real constant with the return value of function repl *)
  let rec const_replace t =
    let t = t_map const_replace t in
    match t.t_node with
    | Tconst (ConstReal rc) -> repl rc
    | _ -> t
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
       from_int (x) + 0.y *)
    match extract_from_rc rc with
    | Some (i, frac) ->
        let i_t = t_from_int (t_const (ConstInt (Number.int_const_dec i))) in
        let frac_t =
          t_const (ConstReal (Number.real_const_dec "0" frac None)) in
        if i = "0" then frac_t
        else if frac = "0" then i_t
        else t_add i_t frac_t
    | None -> t_const (ConstReal rc)
  in
  let replace = const_replace rc_to_new_term in
  Trans.fold_map (fun thd ((),( task : task)) ->
    match thd.task_decl.td_node with
    | Decl { d_node = Dlogic ld } ->
        let ld = List.map (fun (fs, defn) ->
          let vls, t = open_ls_defn defn in
          let t = replace t in
          make_ls_defn fs vls t) ld in
        let task = Task.add_decl task (create_logic_decl ld) in
        (), task
    | Decl { d_node = Dprop (Paxiom, ps, term) } ->
        let term = replace term in
        let task = Task.add_decl task (create_prop_decl Paxiom ps term) in
        (), task
    | Decl { d_node = Dprop (Pgoal, ps, term) } ->
        let term = replace term in
        (), Task.add_decl task (create_prop_decl Pgoal ps term)
    | _ -> (), add_tdecl task thd.task_decl
  ) () None

let () =
  Trans.register_env_transform ~desc:"float literals" "float_literal"
    (fun env ->
      let th_from_int = Env.find_theory env ["real"] "FromInt" in
      let th_real = Env.find_theory env ["real"] "Real" in
      float_lift th_from_int th_real)
