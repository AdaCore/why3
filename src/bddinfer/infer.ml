
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

let cond_to_abs env cond =
    Interp_expression.meet_condition ~old:Abstract.VarMap.empty (Abstract.top env) cond

let rec deref_var env v =
  let open Abstract in
  match VarMap.find v env with
  | RefValue r -> deref_var env r
  | (IntValue _ | BoolValue _ as x) -> x

let interp_let_noin state x v e =
  let open Abstract in
  match v with
    | BoolValue vb ->
       let b =
         Interp_expression.interp_bool_expr ~old:Abstract.VarMap.empty (Abstract.why_env state) e
       in
       Abstract.interp_bool_var_intro state x vb b
    | IntValue vi ->
       let old = Abstract.VarMap.empty in
       let env = Abstract.why_env state in
       let aenv = Abstract.apron_env state in
       let te = Interp_expression.to_expr ~old env aenv e in
       let m = Abstract.VarMap.singleton x v in
       let state1 = Abstract.add_in_environment state m in
       Abstract.assign_texpr state1 vi te
    | _ -> assert false

let rec interp_stmt (functions : func list) (state : Abstract.t) (stmt : statement) : (Abstract.t * Abstract.t) =
  begin match stmt.stmt_tag with
  | "" -> ()
  | a ->
     generated_entry_states := Wstdlib.Mstr.add a state !generated_entry_states
  end;
  (* if Abstract.is_bottom state then
     state
    else *) (* Correct, but not clearly useful. *)
  match stmt.stmt_node with
  | Sassign(x, e) ->
     let env = Abstract.why_env state in
     Abstract.(begin
       match deref_var env x with
       | RefValue _ | BoolValue _ -> assert false
       | IntValue(v) ->
          let old = VarMap.empty in
          let aenv = apron_env state in
          let te = Interp_expression.to_expr ~old env aenv e in
          (assign_texpr state v te, Abstract.bottom env)
     end)
  | Sassign_bool(x, extrav, e) ->
     let env = Abstract.why_env state in
     Abstract.(begin
       match deref_var env x with
       | IntValue _ | RefValue _ -> assert false
       | BoolValue v ->
          (* Format.printf "@[State before assign bool =@ %a@]@." Abstract.print state; *)
           (* we have in state x -> v, we evaluate expression e as a BDD, which may use v *)
          let b = Interp_expression.interp_bool_expr ~old:VarMap.empty env e in
          let state1 = interp_bool_assign state v extrav b in
          (* Format.printf "@[State after assign bool =@ %a@]@." Abstract.print state1; *)
          (state1, Abstract.bottom env)
     end)

  | Swhile(cond, user_invariants, body) ->
      let invariant, exceptionnal_state = interp_loop functions 0 state cond body in
      generated_loop_invariants :=
        Wstdlib.Mstr.add stmt.stmt_tag invariant !generated_loop_invariants;
      (* check user invariants *)
      let _ = List.fold_left
                (fun c (n, i) ->
                  let user_invariant = cond_to_abs (Abstract.why_env state) i in
                  let valid = Abstract.is_leq invariant user_invariant in
                  let tag,orig =
                    match n with
                    | None -> stmt.stmt_tag ^ (string_of_int c), ""
                    | Some n -> n,n
                  in
                  add_checked_user_annotations tag true orig i valid;
                  c+1) 0 user_invariants
      in
      let env = Abstract.why_env state in
      Abstract.join (Interp_expression.meet_condition ~old:Abstract.VarMap.empty invariant (neg_cond cond)) exceptionnal_state, Abstract.bottom env

  | Sfcall(opt_result, f, args) ->
     begin
       let old_env = Abstract.why_env state in
       match List.find (fun g -> g.func_name = f) functions with
       | exception Not_found -> assert false
       | { func_params ; func_def; _ } ->
          let state_with_params state =
            List.fold_left2
              (fun s (x, v) e ->
                match v with
                | Param_ref _ ->
                   begin
                     match e with
                     | Evar (y, Here) ->
                        let m = Abstract.VarMap.singleton x (Abstract.RefValue y) in
                        Abstract.add_in_environment s m
                     | Evar (_, Old) -> assert false (* impossible *)
                     | _ ->
                        Format.eprintf "e = %a@." Ast.print_expression e;
                        assert false (* only vars should be passed by ref *)
                   end
                | Param_noref av ->
                   interp_let_noin s x av e)
              state func_params args
          in
          match func_def, opt_result with
          | Fun_let(body,None), None ->
             let s1 = state_with_params state in
             let s2, s2' = interp_stmt functions s1 body in
             assert (Abstract.is_bottom s2');
             (* restoring the env as before the call *)
             Abstract.restrict_environment s2 old_env, Abstract.bottom old_env
          | Fun_let(body,Some return_expr), Some(res,rem,av) ->
             let s1 = state_with_params state in
             let s2,s2' = interp_stmt functions s1 body in
             assert (Abstract.is_bottom s2');
             (* do as let res = return_expr in rem *)
             (* !!FIXME: remove the params from the env *before* interpreting rem ! *)
             let s3,s3' = interp_let_in functions s2 res av return_expr rem in
             Abstract.restrict_environment s3 old_env, Abstract.restrict_environment s3' old_env
          | Fun_val(writes, None, post), None ->
             let s_with_params = state_with_params state in
             let renamed, old, data = Abstract.prepare_havoc writes s_with_params in
             let state_meet = Interp_expression.meet_condition ~old renamed post in
             let result =
               Abstract.restrict_environment state_meet (Abstract.why_env s_with_params)
             in
             let s = Abstract.finalize_havoc result data in
             let s_final = Abstract.restrict_environment s old_env in
             s_final, Abstract.bottom old_env

          | Fun_val(writes, Some(result,aresult), post), Some(res,rem,av) ->
             (* first adding the expected res var in the env *)
             let m = Abstract.VarMap.singleton res av in
             let s_with_res = Abstract.add_in_environment state m in
             let s_with_params = state_with_params s_with_res in
             (* we do as an havoc statement, first adding result in the env *)
             let m = Abstract.VarMap.singleton result aresult in
             let s_with_result = Abstract.add_in_environment s_with_params m in
             let renamed, old, data = Abstract.prepare_havoc writes s_with_result in
             let state_meet = Interp_expression.meet_condition ~old renamed post in
             let result =
               Abstract.restrict_environment state_meet (Abstract.why_env s_with_result)
             in
             let after_havoc = Abstract.finalize_havoc result data in
             (* we then identify res with result *)
             let state_eq = Interp_expression.meet_with_variable_equality after_havoc aresult av in
             (* we then remove result and params from state *)
             let state_no_result_no_params =
               Abstract.restrict_environment state_eq (Abstract.why_env s_with_res)
             in
             let s,s' = interp_stmt functions state_no_result_no_params rem in
             (* finally removing the res variable from the state *)
             Abstract.restrict_environment s old_env, Abstract.restrict_environment s' old_env

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
      let result = Abstract.join s1 s2 in
      result, Abstract.join s1' s2'

  | Sblock stmts ->
      let env = Abstract.why_env state in
      List.fold_left
        (fun (s,s') stmts ->
           let s1,s1' = interp_stmt functions s stmts in
           s1, Abstract.join s' s1') (state, Abstract.bottom env) stmts

  | Sassert cond ->
     let abs_cond = cond_to_abs (Abstract.why_env state) cond in
     let valid = Abstract.is_leq state abs_cond in
     if stmt.stmt_tag <> "" || not valid then
       begin
         checked_user_annotations :=
           Wstdlib.Mstr.add stmt.stmt_tag (false,stmt.stmt_tag,cond,valid)
             !checked_user_annotations
       end;
    let env = Abstract.why_env state in
    state, Abstract.bottom env

  | Sassume cond ->
      let abs_cond = cond_to_abs (Abstract.why_env state) cond in
      let result = Abstract.meet state abs_cond in
      let env = Abstract.why_env state in
      result, Abstract.bottom env

  | Shavoc(vars, cond) ->
     (* Format.eprintf "@[State before [havoc]:@ @[%a@]@]@." Abstract.print state; *)
     let renamed, old, data = Abstract.prepare_havoc vars state in
     (* Format.eprintf "@[State after prepare_havoc:@ @[%a@]@]@." Abstract.print renamed; *)
    (* Format.eprintf "@[old after prepare_havoc:@ @[%a@]@]@." Abstract.print_env old; *)
     let state_meet = Interp_expression.meet_condition ~old renamed cond in
     (* Format.eprintf "@[State after meet:@ @[%a@]@]@." Abstract.print state_meet; *)
     let result = Abstract.restrict_environment state_meet (Abstract.why_env state) in
     let result = Abstract.finalize_havoc result data in
     let env = Abstract.why_env state in
     result, Abstract.bottom env

  | Sletin(x, v, e, stmt) ->
    interp_let_in functions state x v e stmt
  | Sdrop(v,stmt) ->
    let map = Abstract.why_env state in
    let map = Abstract.VarMap.remove v map in
    let s = Abstract.restrict_environment state map in
    interp_stmt functions s stmt
  | Sbreak ->
     let env = Abstract.why_env state in
     Abstract.bottom env, state


and interp_let_in functions state x v e stmt =
  let old_map = Abstract.why_env state in
  let state2 = interp_let_noin state x v e in
  let state3,state3' = interp_stmt functions state2 stmt in
  Abstract.restrict_environment state3 old_map, Abstract.restrict_environment state3' old_map


and interp_loop (functions: func list) (counter: int)
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
        (* Format.eprintf "@[interp_loop, before widening:@ @[%a@]@]@." Abstract.print s2; *)
        let s4 = Abstract.widening s s3 in
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
  }

let interp_prog (p : why1program) : interp_report =
  checked_annotations_counter := 0;
  checked_user_annotations := Wstdlib.Mstr.empty;
  generated_loop_invariants := Wstdlib.Mstr.empty;
  generated_entry_states := Wstdlib.Mstr.empty;
  let initial_state = Abstract.top p.vars in
  let final_state, sbreak = interp_stmt p.functions initial_state p.statements in
  assert (Abstract.is_bottom sbreak);
  { final_state ;
    invariants = !generated_loop_invariants;
    entry_states = !generated_entry_states;
    checks = !checked_user_annotations
  }





let report ~verbosity report =
  if verbosity >= 2 then
    begin
      (* display generated loop invariants with domains, final
         states of annotated statements, and the final state of
         the program *)
      let print_state msg domains_msg st =
        let cs = Interp_expression.abstract_state_to_conditions st in
        Format.printf "@[<hov 2>%s:@ @[<hov 2>{ " msg;
        List.iter (fun c -> Format.printf "@[%a@] ;@ " Ast.print_condition c) cs;
        Format.printf "}@]@]@\n@.";
        if verbosity >= 3 then
          Format.printf "@[%s as abstract state is@ %a@]@\n@." msg
            Abstract.print st;
        if domains_msg <> "" then
          let doms = Abstract.get_domains st in
          Format.printf "@[Domains %s:@ @[<hov 2>{ %a}@]@]@\n@."
            domains_msg Abstract.print_domains doms
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
