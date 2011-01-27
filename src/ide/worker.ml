(** Create and manage one main worker which wait for the remaining
    works *)
module MainWorker :
sig
  type 'a t
  val create : unit -> 'a t
  val treat : 'a t -> ('b -> 'a -> 'b) -> 'b -> 'b
  val start_work : 'a t -> unit
  val stop_work : 'a t -> unit
  val add_work : 'a t -> 'a -> unit
  val add_works : 'a t -> 'a Queue.t -> unit
end
  =
struct
  type 'a t = { queue : 'a Queue.t;
                mutex : Mutex.t;
                condition : Condition.t;
                mutable remaining : int;
              }

  let create () =
    { queue = Queue.create ();
      mutex = Mutex.create ();
      condition = Condition.create ();
      remaining = 0;
    }

  let treat t f acc =
    let rec main acc =
      Mutex.lock t.mutex;
      while Queue.is_empty t.queue && t.remaining > 0 do
        Condition.wait t.condition t.mutex
      done;
      if Queue.is_empty t.queue
      then begin (* t.remaining < 0 *) Mutex.unlock t.mutex;acc end
      else
        begin
          let v = Queue.pop t.queue in
          Mutex.unlock t.mutex;
          let acc = f acc v in
          Thread.yield ();
          main acc
        end in
    main acc

  let start_work t =
    Mutex.lock t.mutex;
    t.remaining <- t.remaining + 1;
    Mutex.unlock t.mutex

  let stop_work t =
    Mutex.lock t.mutex;
    t.remaining <- t.remaining - 1;
    if t.remaining = 0 then Condition.signal t.condition;
    Mutex.unlock t.mutex

  let add_work t x =
    Mutex.lock t.mutex;
    Queue.push x t.queue;
    Condition.signal t.condition;
    Mutex.unlock t.mutex

  let add_works t q =
    Mutex.lock t.mutex;
    Queue.transfer q t.queue;
    Condition.signal t.condition;
    Mutex.unlock t.mutex


end

(** Manage a pool of worker *)
module ManyWorkers :
sig
  type 'a t
  val create : int ref -> ('a -> unit) -> 'a t
    (** [create n f] create a pool of [n] worker doing [f] *)
  val add_work : 'a t -> 'a -> unit
  val add_works : 'a t -> 'a Queue.t -> unit
end
  =
struct
  type 'a t = { queue : 'a Queue.t;
                mutex : Mutex.t;
                f : 'a -> unit;
                max : int ref;
                mutable current : int;
              }

  let create n f =
    { queue = Queue.create ();
      mutex = Mutex.create ();
      f = f;
      max = n;
      current = 0;
    }

  let rec run t x =
    t.f x;
    Mutex.lock t.mutex;
    if not (Queue.is_empty t.queue) then
      let x = Queue.pop t.queue in
      Mutex.unlock t.mutex;
      run t x
    else begin
      t.current <- t.current - 1;
      Mutex.unlock t.mutex
    end

  (** In the next functions, we never call [start] inside the
      mutex in order to release it as soon as possible *)
  let start t x = ignore (Thread.create (run t) x)

  let add_work t x =
    Mutex.lock t.mutex;
    if t.current < !(t.max)
    then begin
      t.current <- t.current + 1;
      Mutex.unlock t.mutex;
      start t x
    end
    else begin
      Queue.push x t.queue;
      Mutex.unlock t.mutex
    end


  let add_works t q =
    let rec extract acc =
      if t.current < !(t.max) && not (Queue.is_empty q)
      then
        let x = Queue.pop q in
        t.current <- t.current + 1;
        extract (x::acc)
      else acc in
    Mutex.lock t.mutex;
    let now = extract [] in
    Queue.transfer q t.queue;
    Mutex.unlock t.mutex;
    List.iter (start t) now


end
