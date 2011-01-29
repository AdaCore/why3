(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Thread
open Why
open Env
open Theory
open Task
open Trans
open Driver
open Call_provers
open Scheduler

type 'a tool = {
  tval     : 'a;
  ttrans   : task trans;
  tdriver  : driver;
  tcommand : string;
  tenv     : env;
  tuse     : task;
  ttime    : int;
  tmem     : int;
}

type 'a prob = {
  ptask  : env -> task -> ('a * task) list; (** needed for tenv *)
  ptrans : env -> task list trans;
}


type why_result =
  | InternalFailure of exn
  | Done of prover_result

type ('a,'b) result = {tool   : 'a;
                       prob   : 'b;
                       task   : Decl.prsymbol;
                       idtask : int;
                       result : why_result}

type ('a,'b) callback = 'a -> 'b -> task -> int -> proof_attempt_status -> unit

let debug_call = Debug.register_flag "call"
let debug = Debug.register_flag "bench_core"

open Worker

let call s callback tool prob =
  (** Prove goal *)
  let call q cb task =
    Queue.add (create_proof_attempt ~debug:(Debug.test_flag debug_call)
      ~timelimit:(tool.ttime) ~memlimit:(tool.tmem)
      ~command:(tool.tcommand) ~driver:(tool.tdriver)
      ~callback:cb task) q in
  let iter q pval i task =
    MainWorker.start_work s;
    let cb res = callback pval i task res;
      match res with Scheduler.Done _
        | Scheduler.InternalFailure _ -> MainWorker.stop_work s | _ -> () in
    call q cb task; succ i in
  let trans_cb pval tl =
    let q = Queue.create () in
    ignore (List.fold_left (iter q pval) 0 (List.rev tl));
    transfer_proof_attempts q;
    MainWorker.stop_work s in
  (** Apply trans *)
  let iter_task (pval,task) =
    MainWorker.start_work s;
    let trans = Trans.compose_l (prob.ptrans tool.tenv)
      (Trans.singleton tool.ttrans) in
    apply_transformation_l ~callback:(trans_cb pval) trans task in
  (** Split *)
  let ths = do_why_sync (prob.ptask tool.tenv) tool.tuse in
  MainWorker.start_work s;
  List.iter iter_task ths;
  MainWorker.stop_work s

let general ?(callback=fun _ _ _ _ _ -> ()) iter add =
  Debug.dprintf debug "Start one general@.";
  (** Main worker *)
  let t = MainWorker.create () in
  (** Start all *)
  MainWorker.start_work t;
  let _ = Thread.create (fun () ->
    iter (fun v tool prob ->
    let cb pval i task res =
      MainWorker.add_work t (fun () ->
        callback tool.tval pval task i res;
        match res with
          | Scheduler.InternalFailure _ | Scheduler.Done _ ->
            add v {tool = tool.tval; prob = pval;
                   task = Task.task_goal task;
                   idtask = i;
                   result = match res with
                     | Scheduler.InternalFailure exn -> InternalFailure exn
                     | Scheduler.Done r -> Done r
                     | _ -> assert false
                  }
          | _ -> ()) in
    call t cb tool prob);
    MainWorker.stop_work t;
  ) () in
  (** Treat the work done and wait *)
  MainWorker.treat t (fun () f -> f ()) ()

let any ?callback toolprob =
  let l = ref [] in
  general ?callback (fun f -> List.iter (fun (t,p) -> f () t p) toolprob)
    (fun () r -> l:=r::!l);
  !l


let all_list_tp ?callback tools probs =
  let l = ref [] in
  general ?callback (fun f ->
    List.iter (fun t -> List.iter (fun p -> f () t p) probs) tools)
    (fun () r -> l:=r::!l);
  !l

let all_list_pt ?callback tools probs =
  let l = ref [] in
  general ?callback (fun f ->
    List.iter (fun p -> List.iter (fun t -> f () t p) tools) probs)
    (fun () r -> l:=r::!l);
  !l

let all_array ?callback tools probs =
  let m = Array.make_matrix (Array.length tools) (Array.length probs)
    [] in
  general ?callback (fun f ->
    Array.iteri (fun i t -> Array.iteri (fun j p -> f (i,j) t p) probs) tools)
    (fun (i,j) r -> m.(i).(j) <- r::m.(i).(j));
  m


let all_list_tools ?callback tools probs =
  let tools = List.map (fun t -> (t, ref [])) tools in
  general ?callback (fun f ->
    List.iter (fun (t,l) -> List.iter (fun p -> f l t p) probs) tools)
    (fun l r -> l:=r::!l);
  List.map (fun (t,l) -> (t.tval,!l)) tools

type output =
  (** on stdout *)
  |Average of string
  |Timeline of string
  (** In a file *)
  |Csv of string

type ('a,'b) bench =
    {
      bname  : string;
      btools : 'a tool list;
      bprobs : 'b prob list;
      boutputs : output list;
    }

let run_bench ?callback bench =
  all_list_pt ?callback bench.btools bench.bprobs

let run_benchs ?callback benchs =
  let benchs = List.map (fun b -> (b,ref [])) benchs in
  general ?callback (fun f ->
    List.iter (fun (b,l) ->
    List.iter (fun t -> List.iter (fun p -> f l t p) b.bprobs)
      b.btools) benchs)
    (fun l r -> l:=r::!l);
  List.map (fun (b,l) -> (b,!l)) benchs

let run_benchs_tools ?callback benchs =
  let benchs = List.map (fun b ->
    b, List.map (fun t -> t,ref []) b.btools) benchs in
  general ?callback (fun f ->
    List.iter (fun (b,l) ->
    List.iter (fun p -> List.iter (fun (t,l) -> f l t p) l)
      b.bprobs) benchs)
    (fun l r -> l:=r::!l);
  List.map (fun (b,l) -> b,List.map (fun (t,l) -> t.tval,!l) l) benchs



(** average *)

(** valid * timeout * unknown * invalid  *)
type nb_avg = int * float

let add_nb_avg (nb,avg) time =
  (succ nb, ((float nb) *. avg +. time) /. (float (succ nb)))
let empty_nb_avg = (0,0.)

let print_nb_avg fmt (nb,avg) = Format.fprintf fmt "%i : %.2f" nb avg

type tool_res =
    { valid : nb_avg;
      timeout : nb_avg;
      unknown : nb_avg;
      invalid : nb_avg;
      failure : nb_avg}

let empty_tool_res =
  { valid   = empty_nb_avg;
    timeout = empty_nb_avg;
    unknown = empty_nb_avg;
    invalid = empty_nb_avg;
    failure = empty_nb_avg;
  }

  let print_tool_res fmt tool_res =
    Format.fprintf fmt "(%a, %a, %a, %a, %a)"
      print_nb_avg tool_res.valid
      print_nb_avg tool_res.unknown
      print_nb_avg tool_res.timeout
      print_nb_avg tool_res.invalid
      print_nb_avg tool_res.failure

  let compute_average l =
  let fold tr res =
    let r = res.result in
    match r with
      | Done r ->
        begin match r.pr_answer with
          | Valid -> {tr with valid = add_nb_avg tr.valid r.pr_time}
          | Timeout -> {tr with timeout = add_nb_avg tr.timeout r.pr_time}
          | Invalid -> {tr with invalid = add_nb_avg tr.invalid r.pr_time}
          | Unknown _ -> {tr with unknown = add_nb_avg tr.unknown r.pr_time}
          | Failure _ | HighFailure ->
            {tr with failure = add_nb_avg tr.failure r.pr_time}
        end
      | InternalFailure _ ->
        {tr with failure = add_nb_avg tr.failure 0.} in
    List.fold_left fold empty_tool_res l

  let extract_done = function Done r -> r | InternalFailure _ -> assert false

  let filter_timeline l =
    let l = List.filter (function {result = Done r} -> r.pr_answer = Valid
      | _ -> false) l in
    let compare_valid x y =
      let c = compare (extract_done x.result).pr_time
        (extract_done y.result).pr_time in
      if c <> 0 then c else compare x y in
    let l = List.fast_sort compare_valid l in
    l

  let compute_timeline min max step =
    let rec aux acc cur next = function
      | _ when next > max -> List.rev acc
      | [] -> aux (cur::acc) cur (next+.step) []
      | {result= InternalFailure _}::l -> aux acc cur next l
      | {result= Done {pr_time = t}}::_ as l when t >= next ->
        aux (cur::acc) cur (next+.step) l
      | _::l -> aux acc (cur+1) next l in
    aux [] 0 min

  let max_time l =
    List.fold_left (fun acc {result=r} ->
      match r with
        | Done {pr_time = t} -> max acc t
        | InternalFailure _ -> acc ) 0. l
  open Format
(**
answer output time

*)


  let print_prover_answer fmt = function
    | Valid -> fprintf fmt "Valid"
    | Invalid -> fprintf fmt "Invalid"
    | Timeout -> fprintf fmt "Timeout"
    | Unknown s -> fprintf fmt "Unknown: %S" s
    | Failure s -> fprintf fmt "Failure: %S" s
    | HighFailure -> fprintf fmt "HighFailure"

  let print_newline fmt () = fprintf fmt "\n"

  let transpose_sorted = function
    | [] -> []
    | (_,lres)::_ as l ->
    let lref = List.map (fun r -> (r.prob,r.task,r.idtask),ref []) lres in
    let l = List.rev l in
    let add (_,lr) res = lr := res :: !lr in
    List.iter (fun (_,lres) -> List.iter2 add lref lres) l;
    List.map (fun (b,lr) -> b,!lr) lref

  let print_csv cmp print_tool print_prob fmt l =
    let cmp x y =
      let c = cmp x.prob y.prob in
      if c <> 0 then c else
        let id x = x.task.Decl.pr_name.Ident.id_string in
        let c = String.compare (id x) (id y) in
        if c <> 0 then c else compare x.idtask y.idtask in
    let l = List.map (fun (p,l) -> p,List.fast_sort cmp l) l in
    fprintf fmt " ,";
    let print_header fmt (p,_) = fprintf fmt "%a, " print_tool p in
    Pp.print_list Pp.comma print_header fmt l;
    print_newline fmt ();
    let l = transpose_sorted l in
    let print_cell fmt {result= r} =
      match r with
        | Done r ->
          fprintf fmt "%a, %.3f" (*"%a, %S, %.3f"*)
            print_prover_answer r.pr_answer (*r.result.pr_output*)
            r.pr_time
        | InternalFailure _ -> fprintf fmt "InternalFailure, \"\""
in
    let print_line fmt ((b,t,id),l) =
      (* No printer for task since we want the same name evenif its
         the same file with different environnement (loaded two times) *)
      fprintf fmt "%a|%s|%i ," print_prob b
        t.Decl.pr_name.Ident.id_string
        id;
      Pp.print_list Pp.comma print_cell fmt l in
    Pp.print_list print_newline print_line fmt l

  let print_timeline print_tool fmt l =
    let l = List.map (fun (t,l) -> t,filter_timeline l) l in
    let max = List.fold_left (fun acc (_,l) -> max acc (max_time l)) 0. l in
    let max = max +. 0.1 in
    let step = max /. 10. in
    let tl = List.map (fun (t,l) -> t,compute_timeline 0. max step l) l in
    let print_timeline (tool_val,timeline) =
      fprintf fmt "%a - %a\n"
        (Pp.print_list Pp.comma (fun fmt -> fprintf fmt "%4i"))
        timeline print_tool tool_val in
    fprintf fmt "%a\n"
      (Pp.print_iter1 (fun f -> Util.iterf f 0. max)
         Pp.comma (fun fmt -> fprintf fmt "%3.2f"))
      step;
    List.iter print_timeline tl


  let print_average print_tool fmt l =
    let tool_res = List.map (fun (t,l) -> t,compute_average l) l in
    let print_tool_res (tool_val,tool_res) =
      fprintf fmt "%a - %a\n" print_tool_res tool_res print_tool tool_val in
    fprintf fmt "(v,u,t,i,f) - valid, unknown, timeout, invalid, failure\n";
    List.iter print_tool_res tool_res


  let print_output cmp print_tool print_probs (b,l) =
    let open_std f s =
      if s = "-"
      then begin f std_formatter;pp_print_flush std_formatter () end
      else
        let cout = (open_out s) in
        let fmt = (formatter_of_out_channel cout) in
        f fmt;
        pp_print_flush fmt ();
        close_out cout in
    List.iter (function
      | Average s -> open_std (fun fmt ->
        Pp.wnl fmt;
        print_average print_tool fmt l) s
      | Timeline s -> open_std (fun fmt ->
        Pp.wnl fmt;
        print_timeline print_tool fmt l) s
      | Csv s ->
        open_std (fun fmt -> Pp.wnl fmt;
          print_csv cmp print_tool print_probs fmt l) s
    ) b.boutputs


