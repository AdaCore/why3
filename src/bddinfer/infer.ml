(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**

{1 The core abstract interpretation engine}

*)

(* open Why3 *)
(* to comment out when inside Why3 *)


open Ast

let checked_annotations_counter = ref 0
let checked_user_annotations = ref Wstdlib.Mstr.empty
let generated_loop_invariants = ref Wstdlib.Mstr.empty
let generated_entry_states = ref Wstdlib.Mstr.empty
let widening_count = ref 0

let add_checked_user_annotations tag is_inv orig cond is_valid =
  let n =
    match tag with
    | "" ->
       let n = "anonymous_stmt_" ^ string_of_int !checked_annotations_counter in
       incr checked_annotations_counter;
       n
    | n -> n
  in
  assert (not (Wstdlib.Mstr.mem n !checked_user_annotations));
  checked_user_annotations :=
    Wstdlib.Mstr.add n (is_inv,orig,cond,is_valid)
      !checked_user_annotations

(** [intro_local_var env conds x v e] returns a pair [newenv,newcond]
   where [newenv] is the environment [env] extend to contain the new
   program variable [x], associated to abstract variable
   [v]. [newconds] extends the conditions [cons] with a condition that
   expresses that [x] is equal to [e]. *)
let intro_local_var env conds x v e =
  let m = Abstract.VarMap.add x v env in
  let cond =
    match v with
    | Abstract.BoolValue _ ->
      c_eq_bool (e_var x Here) e
    | Abstract.IntValue _ ->
      c_eq_int (e_var x Here) e
    | _ -> assert false
  in
  m,and_cond conds (atomic_cond cond)


let rec interp_stmt (functions : func FuncMap.t) (state : Abstract.t) (stmt : statement) : (Abstract.t * Abstract.t) =
  begin match stmt.stmt_tag with
  | "" -> ()
  | a ->
     generated_entry_states := Wstdlib.Mstr.add a state !generated_entry_states
  end;
  (* if Abstract.is_bottom state then
     state
    else *) (* Correct, but not clearly useful. *)
  match stmt.stmt_node with

  | Swhile(cond, user_invariants, body) ->
      let invariant, exceptional_state = interp_loop functions 0 state cond body in
      generated_loop_invariants :=
        Wstdlib.Mstr.add stmt.stmt_tag invariant !generated_loop_invariants;
      (* check user invariants *)
      let _ =
        List.fold_left
          (fun c (n, i) ->
             (* Format.eprintf "user_invariant is: @[%a@]@." print_condition i; *)
             let complement = Interp_expression.meet_condition ~old:Abstract.VarMap.empty
                 invariant (neg_cond i)
             in
             let valid = Abstract.is_bottom complement in
             (* Format.eprintf "complement as abstract state: @[%a@]@." Abstract.print complement; *)
             let tag,orig =
               match n with
               | None -> stmt.stmt_tag ^ (string_of_int c), ""
               | Some n -> n,n
             in
             add_checked_user_annotations tag true orig i valid;
             c+1) 0 user_invariants
      in
      Abstract.join (Interp_expression.meet_condition ~old:Abstract.VarMap.empty invariant (neg_cond cond)) exceptional_state, Abstract.bottom state

  | Sfcall(opt_result, lets, f, args, memo_env, memo_res_env, memo_add_env, memo_havoc, memo_body) ->
     begin
       match FuncMap.find f functions with
       | exception Not_found -> assert false
       | { func_params ; func_def; _ } ->
          let env_with_params envcond =
            List.fold_left2
              (fun (env,cond) (x, v) e ->
                match v with
                | Param_ref _ ->
                   begin
                     match e with
                     | Evar (y, Here) ->
                        let m = Abstract.VarMap.add x (Abstract.RefValue y) env in
                        (m,cond)
                     | Evar (_, Old) -> assert false (* impossible *)
                     | _ ->
                        Format.eprintf "e = %a@." Ast.print_expression e;
                        assert false (* only vars should be passed by ref *)
                   end
                | Param_noref av ->
                   intro_local_var env cond x av e)
              envcond func_params args
          in
          let local_env () =
            List.fold_left
              (fun (env,c) (x,v,e) -> intro_local_var env c x v e)
              (Abstract.VarMap.empty,true_cond) lets
          in
          let get_env memo_env res_opt =
            match !memo_env with
            | None ->
              let lenv,lcond = local_env () in
              let lenv,lcond = env_with_params (lenv,lcond) in
              let lenv = match res_opt with
                | None -> lenv
                | Some(x,v) -> Abstract.VarMap.add x v lenv
              in
              let x = (lenv,lcond) in
              memo_env := Some x;
              x
            | Some x -> x
          in
          let get_body memo b =
            match !memo with
            | Some b -> b
            | None -> let b = copy_stmt b in memo := Some b; b
          in
          match func_def, opt_result with
          | Fun_let(body,None), None ->
            let lenv,lcond = get_env memo_env None in
            let s1 = Abstract.add_in_environment memo_add_env state lenv in
            (* Format.eprintf "@[[Sfcall,Fun_let] state with env:@ @[%a@]@]@." Abstract.print s1; *)
            let s1 =
              Interp_expression.meet_condition ~old:Abstract.VarMap.empty s1 lcond
            in
            (* Format.eprintf "@[[Sfcall,Fun_let] state after meet lcond:@ @[%a@]@]@." Abstract.print s1; *)
            let b = get_body memo_body body in
            let s2, s2' = interp_stmt functions s1 b in
            (* Format.eprintf "@[[Sfcall,Fun_let] state after body:@ @[%a@]@]@." Abstract.print s2; *)
            assert (Abstract.is_bottom s2');
            (* restoring the env as before the call *)
            let s_final = Abstract.restrict_environment s2 state in
            (* Format.eprintf "@[[Sfcall,Fun_let] state final:@ @[%a@]@]@." Abstract.print s_final; *)
            s_final, Abstract.bottom state
          | Fun_let(body,Some return_expr), Some(res,rem,av) ->
            let lenv,lcond = get_env memo_env None (* FIXME!!! should be Some ... *) in
            let s1 = Abstract.add_in_environment memo_add_env state lenv in
            let s1 =
              Interp_expression.meet_condition ~old:Abstract.VarMap.empty s1 lcond
            in
            let b = get_body memo_body body in
            let s2,s2' = interp_stmt functions s1 b in
            assert (Abstract.is_bottom s2');
            (* do as let res = return_expr in rem *)
            (* !!FIXME: remove the params from the env *before* interpreting rem ! *)
            let s3,s3' = interp_let_in functions s2 res av return_expr rem in
            Abstract.restrict_environment s3 state, Abstract.restrict_environment s3' state
          | Fun_val(writes, None, post), None ->
            let lenv,lcond = get_env memo_env None in
            let s1 = Abstract.add_in_environment memo_add_env state lenv in
            (* Format.eprintf "@[[Sfcall,Fun_val] state with env:@ @[%a@]@]@." Abstract.print s1; *)
            let s2 =
              Interp_expression.meet_condition ~old:Abstract.VarMap.empty s1 lcond
            in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after meet lcond:@ @[%a@]@]@." Abstract.print s2; *)
            let renamed, old = Abstract.prepare_havoc memo_havoc writes s2 in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after havoc:@ @[%a@]@]@." Abstract.print renamed; *)
            let state_meet = Interp_expression.meet_condition ~old renamed post in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after meet:@ @[%a@]@]@." Abstract.print state_meet; *)
            let s_final = Abstract.restrict_environment state_meet state in
            (* Format.eprintf "@[[Sfcall,Fun_val] state final:@ @[%a@]@]@." Abstract.print s_final; *)
            s_final, Abstract.bottom state

          | Fun_val(writes, Some(result,aresult), post), Some(res,rem,av) ->
            (* first adding the expected res var in the env *)
            (* Format.eprintf "@[[Sfcall,Fun_val] state before:@ @[%a@]@]@." Abstract.print state; *)
            let m = Abstract.VarMap.singleton res av in
            let s_with_res = Abstract.add_in_environment memo_res_env state m in
            (* Format.eprintf "@[[Sfcall,Fun_val] state with res:@ @[%a@]@]@." Abstract.print s_with_res; *)
            (* then adding the parameters and the result var *)
            let lenv,lcond = get_env memo_env (Some(result,aresult)) in
            let s1 = Abstract.add_in_environment memo_add_env s_with_res lenv in
            (* Format.eprintf "@[[Sfcall,Fun_val] state with env:@ @[%a@]@]@." Abstract.print s1; *)
            let s_with_params_and_result =
              Interp_expression.meet_condition ~old:Abstract.VarMap.empty s1 lcond
            in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after meet:@ @[%a@]@]@." Abstract.print s_with_params_and_result; *)
            let renamed, old = Abstract.prepare_havoc memo_havoc writes s_with_params_and_result in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after havoc:@ @[%a@]@]@." Abstract.print renamed; *)
            let state_meet = Interp_expression.meet_condition ~old renamed post in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after meet:@ @[%a@]@]@." Abstract.print state_meet; *)
            let after_havoc =
              Abstract.restrict_environment state_meet s_with_params_and_result
            in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after restrict:@ @[%a@]@]@." Abstract.print after_havoc; *)
            (* we then identify res with result *)
            (* FIXME: do not compute the same cond all the time! *)
            let eq_result_res =
              match aresult with
              | Abstract.UnitValue -> assert false
              | Abstract.BoolValue _ -> c_eq_bool (e_var result Here) (e_var res Here)
              | Abstract.IntValue _ ->  c_eq_int (e_var result Here) (e_var res Here)
              | Abstract.RefValue _ -> assert false
            in
            let cond = atomic_cond eq_result_res in
            let state_eq = Interp_expression.meet_condition ~old:Abstract.VarMap.empty after_havoc cond in
            (* Format.eprintf "@[[Sfcall,Fun_val] state after eq_res:@ @[%a@]@]@." Abstract.print state_eq; *)
            (* we then remove result and params from state *)
            let state_no_result_no_params =
              Abstract.restrict_environment state_eq s_with_res
            in
            (* Format.eprintf "@[[Sfcall,Fun_val] state without params:@ @[%a@]@]@." Abstract.print state_no_result_no_params; *)
            let s,s' = interp_stmt functions state_no_result_no_params rem in
            (* finally removing the res variable from the state *)
            Abstract.restrict_environment s state, Abstract.restrict_environment s' state
          | _, None ->
             Format.eprintf
               "[interp fun call] impossible case, call to %a with no result var@."
               Ast.print_fun_id f;
             assert false (* impossible case *)
          | _, Some(res,_rem,_av) ->
             Format.eprintf
               "[interp fun call] impossible case, call to %a with result var %a@."
               Ast.print_fun_id f Abstract.print_var res;
             assert false (* impossible case *)
     end

  | Site (cond, then_stmt, else_stmt) ->
      let abs_cond = Interp_expression.meet_condition ~old:Abstract.VarMap.empty state cond in
      let abs_neg_cond = Interp_expression.meet_condition ~old:Abstract.VarMap.empty state (neg_cond cond) in
      let s1,s1' = interp_stmt functions abs_cond then_stmt in
      let s2,s2' = interp_stmt functions abs_neg_cond else_stmt in
      (* Format.eprintf "@[[Site] s1:@ @[%a@]@]@." Abstract.print s1; *)
      (* Format.eprintf "@[[Site] s2:@ @[%a@]@]@." Abstract.print s2; *)
      let result = Abstract.join s1 s2 in
      (* Format.eprintf "@[[Site] result:@ @[%a@]@]@." Abstract.print result; *)
      (* Format.eprintf "@[[Site] s1':@ @[%a@]@]@." Abstract.print s1'; *)
      (* Format.eprintf "@[[Site] s2':@ @[%a@]@]@." Abstract.print s2'; *)
      let result' = Abstract.join s1' s2' in
      (* Format.eprintf "@[[Site] result':@ @[%a@]@]@." Abstract.print result'; *)
      result, result'

  | Sblock stmts ->
      List.fold_left
        (fun (s,s') stmts ->
           let s1,s1' = interp_stmt functions s stmts in
           (* Format.eprintf "@[[Sblock] s1:@ @[%a@]@]@." Abstract.print s1; *)
           (* Format.eprintf "@[[Sblock] s1':@ @[%a@]@]@." Abstract.print s1'; *)
           (* Format.eprintf "@[[Sblock] s':@ @[%a@]@]@." Abstract.print s'; *)
           let r = Abstract.join s' s1' in
           (* Format.eprintf "@[[Sblock] r:@ @[%a@]@]@." Abstract.print r; *)
           s1, r) (state, Abstract.bottom state) stmts

  | Sassert cond ->
    let abs_neg_cond = Interp_expression.meet_condition ~old:Abstract.VarMap.empty
        state (neg_cond cond)
    in
    let valid = Abstract.is_bottom abs_neg_cond in
    if stmt.stmt_tag <> "" || not valid then
      begin
(*
        if not valid then
          Format.eprintf "abs_neg_cond as abstract state: @[%a@]@." Abstract.print abs_neg_cond;
*)
        checked_user_annotations :=
          Wstdlib.Mstr.add stmt.stmt_tag (false,stmt.stmt_tag,cond,valid)
            !checked_user_annotations
      end;
    let abs_cond = Interp_expression.meet_condition ~old:Abstract.VarMap.empty
        state cond
    in
    abs_cond, Abstract.bottom state

  | Sassume cond ->
    (* Format.eprintf "@[Sassume before [abs_cond]:@ @[%a@]@]@." Abstract.print state; *)
    let abs_cond = Interp_expression.meet_condition ~old:Abstract.VarMap.empty
        state cond
    in
    (* Format.eprintf "@[Sassume abs_cond:@ @[%a@]@]@." Abstract.print abs_cond; *)
    abs_cond, Abstract.bottom state

  | Shavoc(vars, cond, memo_havoc) ->
     (* Format.eprintf "@[State before [havoc]:@ @[%a@]@]@." Abstract.print state; *)
     let renamed, old = Abstract.prepare_havoc memo_havoc vars state in
     (* Format.eprintf "@[State after prepare_havoc:@ @[%a@]@]@." Abstract.print renamed; *)
     (* Format.eprintf "@[old after prepare_havoc:@ @[%a@]@]@." Abstract.print_env old; *)
     let state_meet = Interp_expression.meet_condition ~old renamed cond in
     (* Format.eprintf "@[State after meet:@ @[%a@]@]@." Abstract.print state_meet; *)
     let result = Abstract.restrict_environment state_meet state in
     (* Format.eprintf "@[State after restrict:@ @[%a@]@]@." Abstract.print result; *)
     result, Abstract.bottom state

  | Sletin(x, v, e, stmt) ->
    interp_let_in functions state x v e stmt
  | Sbreak ->
     Abstract.bottom state, state


and interp_let_in functions state x v e stmt =
  (* Format.eprintf "@[State before [let in]:@ @[%a@]@]@." Abstract.print state; *)
  let m,cond = intro_local_var Abstract.VarMap.empty true_cond x v e in
  let state1 = Abstract.add_in_environment (ref None) state m in
  let state2 = Interp_expression.meet_condition ~old:Abstract.VarMap.empty state1 cond in
  (* Format.eprintf "@[State before [in]:@ @[%a@]@]@." Abstract.print state2; *)
  let state3,state3' = interp_stmt functions state2 stmt in
  (* Format.eprintf "@[State after [let in]:@ @[%a@]@]@." Abstract.print state3; *)
  (* Format.eprintf "@[State after [break]:@ @[%a@]@]@." Abstract.print state3'; *)
  Abstract.restrict_environment state3 state, Abstract.restrict_environment state3' state


and interp_loop (functions: func FuncMap.t) (counter: int)
      (s: Abstract.t) (cond: condition) (body: statement) : (Abstract.t * Abstract.t) =
    (* Format.eprintf "@[interp_loop s:@ @[%a@]@]@." Abstract.print s; *)
    let s1 = Interp_expression.meet_condition ~old:Abstract.VarMap.empty s cond in
    (* Format.eprintf "@[interp_loop s1:@ @[%a@]@]@." Abstract.print s1; *)
    let s2, s2' = interp_stmt functions s1 body in
    (* Format.eprintf "@[interp_loop s2:@ @[%a@]@]@." Abstract.print s2; *)
    let s3 = Abstract.join s s2 in
    (* Format.eprintf "@[interp_loop s3:@ @[%a@]@]@." Abstract.print s3; *)
    if counter < 3 then
      if Abstract.is_eq s3 s then
        s, s2'
      else
        interp_loop functions (counter + 1) s3 cond body
    else
      begin
        (* Format.eprintf "@[interp_loop, before widening:@ @[%a@]@]@." Abstract.print s3; *)
        let s4 = Abstract.widening s s3 in
        incr widening_count;
        (* Format.eprintf "@[interp_loop, after widening:@ @[%a@]@]@." Abstract.print s4; *)
        let s5 = Interp_expression.meet_condition ~old:Abstract.VarMap.empty s4 cond in
        (* Format.eprintf "@[interp_loop, after meet:@ @[%a@]@]@." Abstract.print s5; *)
        let s6,_ = interp_stmt functions s5 body in
        (* Format.eprintf "@[interp_loop, after loop iteration:@ @[%a@]@]@." Abstract.print s6; *)
        let s7 = Abstract.join s s6 in
        (* Format.eprintf "@[interp_loop, after loop join:@ @[%a@]@]@." Abstract.print s7; *)
        interp_loop functions 0 s7 cond body
      end

type interp_report = {
    final_state : Abstract.t;
    invariants : Abstract.t Wstdlib.Mstr.t;
    entry_states : Abstract.t Wstdlib.Mstr.t;
    checks : (bool * string * Ast.condition * bool) Wstdlib.Mstr.t;
    widenings : int;
  }

let interp_prog (p : why1program) : interp_report =
  checked_annotations_counter := 0;
  checked_user_annotations := Wstdlib.Mstr.empty;
  generated_loop_invariants := Wstdlib.Mstr.empty;
  generated_entry_states := Wstdlib.Mstr.empty;
  widening_count := 0;
  let initial_state = Abstract.top_new_ctx p.vars in
  let final_state, sbreak = interp_stmt p.functions initial_state p.statements in
  assert (Abstract.is_bottom sbreak);
  { final_state ;
    invariants = !generated_loop_invariants;
    entry_states = !generated_entry_states;
    checks = !checked_user_annotations;
    widenings = !widening_count;
  }





let report ~verbosity report =
  if verbosity >= 2 then
    begin
      (* display generated loop invariants with domains, final
         states of annotated statements, and the final state of
         the program *)
      let print_state msg domains_msg st =
        let cs = Interp_expression.abstract_state_to_conditions st in
        Format.printf "@[%s:@ @[<hov 2>{ %a }@]@]@\n@." msg
          (Pp.print_list Pp.semi Ast.print_condition) cs;
        (if domains_msg <> "" then
          let doms = Abstract.get_domains st in
          Format.printf "@[Domains %s:@ @[<hov 2>{ %a}@]@]@\n@."
            domains_msg Abstract.print_domains doms);
        (if verbosity >= 3 then
          Format.printf "@[%s as abstract state is@ @[%a@]@]@." msg
            Abstract.print st)
      in
      Wstdlib.Mstr.iter
        (fun tag st ->
          let msg = if tag = "" then
                      "Generated loop invariants"
                    else
                      "Generated loop invariants for [" ^ tag ^ "]"
          in
          print_state msg ("for loop ["^tag^"]") st)
        report.invariants;
      Wstdlib.Mstr.iter
        (fun tag st ->
          let msg = "state before [" ^ tag ^ "]" in
          let dmsg = if tag <> "" then "before statement ["^tag^"]" else "" in
          print_state msg dmsg st)
        report.entry_states;
      print_state "Final state as set of formulas is" "" report.final_state;
    end;
  Wstdlib.Mstr.iter
    (fun _tag (is_inv,n,c,valid) ->
      if is_inv then
        begin
          Format.printf "The generated invariant ";
          if valid then
            Format.printf "implies "
          else
            Format.printf "does not imply ";
          begin
            match n with
            | "" -> Format.printf "{ %a }" print_condition c
            | n -> Format.printf "the invariant [%s]" n
          end;
          Format.printf "@\n@."
        end
      else
        begin
          if valid then
            Format.printf "Check: assertion [%s] is valid@\n@." n
          else
            Format.printf "Check: assertion [%s] is NOT valid@\n@." n
        end)
    report.checks
