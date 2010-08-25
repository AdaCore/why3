

(* queue of pending proof attempts 
   protected by a lock
*)

let queue_lock = Mutex.create ()
let attempts = Queue.create ()
let running_proofs = ref 0
let maximum_running_proofs = ref 2

let schedule_proof_attempt ~async ~debug ~timelimit ~memlimit ~prover 
    ~command ~driver ~callback
    goal =
  let prepare_goal = 
    try
      Db.try_prover ~async ~debug ~timelimit ~memlimit ~prover ~command ~driver goal;
    with Db.AlreadyAttempted ->
      raise Exit
  in
  let _thread_id =
    Thread.create
      begin 
        fun () ->
          try
            (* BEGIN LOCKED SECTION *)
            (* lock and store the attempt into the queue *)
            Mutex.lock queue_lock;
            Queue.push (prepare_goal,callback) attempts;
            callback Db.Scheduled;
            (* try to run attempt if resource available *)
            while !running_proofs < !maximum_running_proofs do
              let call,callback = Queue.pop attempts in
              incr running_proofs;
              callback Db.Running;
              Mutex.unlock queue_lock;
              (* END LOCKED SECTION *)       
              let res = call () in
              (* BEGIN LOCKED SECTION *)
              Mutex.lock queue_lock;
              callback res;
              decr running_proofs;
            done;
            Mutex.unlock queue_lock
              (* END LOCKED SECTION *)       
          with
            | Queue.Empty ->
                (* Queue was Empty *)
                Mutex.unlock queue_lock
                  (* END LOCKED SECTION *)       
            | e ->
                (* any other exception should be propagated 
                   after unlocking the lock *)
                Mutex.unlock queue_lock;
                (* END LOCKED SECTION *)       
                raise e
      end
      ()
  in ()
        

  


(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/gwhy.byte"
End: 
*)
