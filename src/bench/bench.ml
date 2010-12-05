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
  ptrans : task list trans;
}

type ('a,'b) result = {tool   : 'a;
                       prob   : 'b;
                       task   : task;
                       idtask : int;
                       result : prover_result}

type ('a,'b) callback = 'a -> 'b -> task -> int -> proof_attempt_status -> unit

let debug = Debug.register_flag "call"

module MTask :
sig
  type shared
  val create : unit -> shared
  val start : shared -> unit
  val stop : shared -> unit
  val lock : shared -> unit
  val unlock : shared -> unit
  val wait : shared -> unit
end
=
struct
  type shared =
      { m : Mutex.t; c : Condition.t;
        mutable nb_task : int;
      }

  let create () =
    { m = Mutex.create ();
      c = Condition.create ();
      nb_task = 0}

  let start s = Mutex.lock s.m; s.nb_task <- s.nb_task + 1; Mutex.unlock s.m
  let stop s = Mutex.lock s.m; s.nb_task <- s.nb_task - 1;
    Mutex.unlock s.m; if s.nb_task = 0 then Condition.signal s.c
  let wait s = Mutex.lock s.m; Condition.wait s.c s.m
  let lock s = Mutex.lock s.m
  let unlock s = Mutex.unlock s.m
end

let call s callback tool prob =
  (** Prove goal *)
  let call cb task =
    schedule_proof_attempt ~debug:(Debug.test_flag debug)
      ~timelimit:(tool.ttime) ~memlimit:(tool.tmem)
      ~command:(tool.tcommand) ~driver:(tool.tdriver)
      ~callback:cb task in
  let iter pval i task =
    MTask.start s;
    let cb res = callback pval i task res;
      match res with Done _ | InternalFailure _ -> MTask.stop s | _ -> () in
    call cb task; succ i in
  let trans_cb pval tl =
    ignore (List.fold_left (iter pval) 0 (List.rev tl)); MTask.stop s in
  (** Apply trans *)
  let iter_task (pval,task) =
    MTask.start s;
    let trans = Trans.compose_l prob.ptrans (Trans.singleton tool.ttrans) in
    apply_transformation_l ~callback:(trans_cb pval) trans task in
  (** Split *)
  let ths = prob.ptask tool.tenv tool.tuse in
  MTask.start s;
  List.iter iter_task ths;
  MTask.stop s

let general ?(callback=fun _ _ _ _ _ -> ()) iter add =
  let s = MTask.create () in
  iter (fun v tool prob ->
    let cb pval i task res =
      callback tool.tval pval task i res;
      match res with
        | Done r -> MTask.lock s;
          add v {tool = tool.tval; prob = pval; task = task;
                 idtask = i; result = r};
          MTask.unlock s
        | _ -> () in
    call s cb tool prob);
  MTask.wait s

let any ?callback toolprob =
  let l = ref [] in
  general ?callback (fun f -> List.iter (fun (t,p) -> f () t p) toolprob)
    (fun () r -> l:=r::!l);
  !l


let all_list ?callback tools probs =
  let l = ref [] in
  general ?callback (fun f ->
    List.iter (fun t -> List.iter (fun p -> f () t p) probs) tools)
    (fun () r -> l:=r::!l);
  !l

let all_array ?callback tools probs =
  let m = Array.make_matrix (Array.length tools) (Array.length probs)
    [] in
  general ?callback (fun f ->
    Array.iteri (fun i t -> Array.iteri (fun j p -> f (i,j) t p) probs) tools)
    (fun (i,j) r -> m.(i).(j) <- r::m.(i).(j));
  m
