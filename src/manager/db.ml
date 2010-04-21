
open Sqlite3

type transaction_mode = | Deferred | Immediate | Exclusive
  
type handle = {
  raw_db : Sqlite3.db;
  mutable in_transaction: int;
  busyfn: Sqlite3.db -> unit;
  mode: transaction_mode;
}

let current_db = ref None
 
let current () = 
  match !current_db with
    | None -> failwith "Db.current: database not yet initialized"
    | Some x -> x

	      

let default_busyfn (_db:Sqlite3.db) =
  print_endline "WARNING: busy";
  (* Thread.delay (Random.float 1.) *)
  ignore (Unix.select [] [] [] (Random.float 1.))
  
let raise_sql_error x = raise (Sqlite3.Error (Rc.to_string x))
  
let try_finally fn finalfn =
  try
    let r = fn () in
    finalfn ();
    r
  with e -> begin
    Format.eprintf "WARNING: exception: %s@." (Printexc.to_string e);
    finalfn ();
    raise e
  end
  
(* retry until a non-BUSY error code is returned *)
let rec db_busy_retry db fn =
  match fn () with
    | Rc.BUSY -> db.busyfn db.raw_db; db_busy_retry db fn
    | x -> x
       
(* make sure an OK is returned from the database *)
let db_must_ok db fn =
  match db_busy_retry db fn with
    | Rc.OK -> ()
    | x -> raise_sql_error x
       
(* make sure a DONE is returned from the database *)
let db_must_done db fn = 
  match db_busy_retry db fn with
    | Rc.DONE -> ()
    | x -> raise_sql_error x
       
(* request a transaction *)
let transaction db fn =
  let m = match db.mode with
    | Deferred -> "DEFERRED" 
    | Immediate -> "IMMEDIATE" 
    | Exclusive -> "EXCLUSIVE" 
  in
  try_finally 
    (fun () ->
       if db.in_transaction = 0 then 
         db_must_ok db 
           (fun () -> exec db.raw_db ("BEGIN " ^ m ^ " TRANSACTION"));
       db.in_transaction <- db.in_transaction + 1;
       fn ();
    ) 
    (fun () ->
       if db.in_transaction = 1 then 
         db_must_ok db (fun () -> exec db.raw_db "END TRANSACTION");
       db.in_transaction <- db.in_transaction - 1
    )
  
(* iterate over a result set *)
let step_fold db stmt iterfn =
  let stepfn () = Sqlite3.step stmt in
  let rec fn a = match db_busy_retry db stepfn with
    | Sqlite3.Rc.ROW -> fn (iterfn stmt :: a)
    | Sqlite3.Rc.DONE -> a
    | x -> raise_sql_error x
  in
  fn []


(** Data *)

type db_ident = int64 

type loc_record = 
    { mutable loc_id : db_ident option;
      (** when None, the record has never been stored in database yet *)
      mutable file : string;
      mutable line : int;
      mutable start : int;
      mutable stop : int;
    }


type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | HighFailure (** external prover call failed *)

let string_of_status = function
  | Scheduled -> "Scheduled"
  | Running -> "Running"
  | Success -> "Success"
  | Timeout -> "Timeout"
  | Unknown -> "Unknown"
  | HighFailure -> "HighFailure"

let print_status fmt s = Format.fprintf fmt "%s" (string_of_status s)

type prover =
    { prover_id : int64;
      prover_name : string;
    }

let prover_name p = p.prover_name

type external_proof = {
    mutable external_proof_id : db_ident;
    mutable prover : db_ident;
    mutable timelimit : int;
    mutable memlimit : int;
    mutable status : proof_attempt_status;
    mutable result_time : float;
    mutable trace : string;
    mutable proof_obsolete : bool;
}

let timelimit e = e.timelimit
let memlimit e = e.memlimit
let status e = e.status
let result_time e = e.result_time
let trace e = e.trace
let proof_obsolete e = e.proof_obsolete

type goal_origin =
  | Goal of Why.Decl.prsymbol
(*
  | VCfun of loc * explain * ...
  | Subgoal of goal
*)

type transf_data =
    { transf_name : string;
      transf_action : Why.Task.task Why.Register.tlist_reg
    }


type goal = {
  mutable goal_id : db_ident;
  mutable goal_origin : goal_origin;
  mutable task : Why.Task.task;
  mutable task_checksum: string;
  mutable proved : bool;
  (** invariant: g.proved == true iff
      exists attempts a in g.attempts, a.obsolete == false and
      (a = External e and e.result == Valid or
      a = Transf(gl) and forall g in gl, g.proved)
  *)
  mutable observers: (bool -> unit) list;
  (** observers that wants to be notified by any changes of the proved status *)
  mutable external_proofs : external_proof list;
  mutable transformations : transf list;
}

and transf = {
    mutable transf_id : db_ident;
    mutable transf_data : transf_data;
    mutable transf_obsolete : bool;
    mutable subgoals : goal list;
}


let goal_task g = g.task
let goal_task_checksum g = g.task_checksum
let external_proofs g = g.external_proofs
let transformations g = g.transformations
let goal_proved g = g.proved

let transf_data t = t.transf_data
let transf_obsolete t = t.transf_obsolete
let subgoals t = t.subgoals

let rec string_from_origin o =
  match o with
    | Goal p -> p.Why.Decl.pr_name.Why.Ident.id_long
    
let goal_name g = string_from_origin g.goal_origin
  

module Prover = struct

  let init db =
    let sql = 
      "CREATE TABLE IF NOT EXISTS prover (prover_id INTEGER PRIMARY KEY AUTOINCREMENT,prover_name TEXT);" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    let sql = 
      "CREATE UNIQUE INDEX IF NOT EXISTS prover_name_idx ON prover (prover_name)" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

(*
  let delete db pr =
    let id =  pr.prover_id in
    let sql = "DELETE FROM prover WHERE id=?" in
    let stmt = Sqlite3.prepare db.raw_db sql in
    db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
    ignore (step_fold db stmt (fun _ -> ()));
    pr.prover_id <- 0L
*)

  let add db name = 
    transaction db 
      (fun () ->
         let sql = "INSERT INTO prover VALUES(NULL,?)" in
         let stmt = Sqlite3.prepare db.raw_db sql in
         db_must_ok db 
           (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.TEXT name));
         db_must_done db (fun () -> Sqlite3.step stmt);
         let new_id = Sqlite3.last_insert_rowid db.raw_db in
         { prover_id = new_id ; prover_name = name })

  let get db name =
    let sql =
      "SELECT prover.prover_id, prover.prover_name FROM prover WHERE prover.prover_name=?" 
    in
    let stmt=Sqlite3.prepare db.raw_db sql in
    (* bind the position variables to the statement *)
    db_must_ok db 
      (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.TEXT name));
    (* convert statement into record *)
    let of_stmt stmt =
      { prover_id =
	  (match Sqlite3.column stmt 0 with
            | Sqlite3.Data.INT i -> i 
	    | x -> 
		try Int64.of_string (Sqlite3.Data.to_string x)
		with _ -> failwith "Db.Prover.get") ;
	prover_name =
	  (match Sqlite3.column stmt 1 with
	    | x -> Sqlite3.Data.to_string x)
      }
    in 
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

  let from_id db id =
    let sql =
      "SELECT prover.prover_id, prover.prover_name FROM prover WHERE prover.prover_id=?" 
    in
    let stmt=Sqlite3.prepare db.raw_db sql in
    (* bind the position variables to the statement *)
    db_must_ok db 
      (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
    (* convert statement into record *)
    let of_stmt stmt =
      { prover_id = id ;
	prover_name =
	  (match Sqlite3.column stmt 1 with
	    | Sqlite3.Data.TEXT t -> t
            | _ -> failwith "Prover.from_id: bad prover_name");
      }
    in 
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

end

let prover_memo = Hashtbl.create 7

let get_prover_from_id id =
  try
    Hashtbl.find prover_memo id
  with Not_found ->
    let p =
      let db = current () in
      try Prover.from_id db id
      with Not_found -> assert false
    in
    Hashtbl.add prover_memo id p;
    p

let prover e = get_prover_from_id e.prover

let get_prover n =
  let db = current () in
  try Prover.get db n
  with Not_found -> 
    Prover.add db n
 
	


module Loc = struct

  let init db =
    let sql = "create table if not exists loc (id integer primary key autoincrement,file text,line integer,start integer,stop integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  (* object definition *)
(*
  let create (* ?id *) ~file ~line ~start ~stop : loc_record = 
    { 
      loc_id = None (* id *);
      file = file;
      line = line;
      start = start;
      stop = stop;
    }
*)

  (* admin functions *)
  let delete db loc =
    match loc.loc_id with
      | None -> ()
      | Some id ->
          let sql = "DELETE FROM loc WHERE id=?" in
          let stmt = Sqlite3.prepare db.raw_db sql in
          db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
          ignore (step_fold db stmt (fun _ -> ()));
          loc.loc_id <- None

  let save db (loc : loc_record) = 
    transaction db 
      (fun () ->
         (* insert any foreign-one fields into their table and get id *)
         let curobj_id = match loc.loc_id with
           | None -> 
               (* insert new record *)
               let sql = "INSERT INTO loc VALUES(NULL,?,?,?,?)" in
               let stmt = Sqlite3.prepare db.raw_db sql in
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 1 
                    (let v = loc.file in Sqlite3.Data.TEXT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 2 
                    (let v = Int64.of_int loc.line in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 3 
                    (let v = Int64.of_int loc.start in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 4 
                    (let v = Int64.of_int loc.stop in Sqlite3.Data.INT v));
               db_must_done db (fun () -> Sqlite3.step stmt);
               let new_id = Sqlite3.last_insert_rowid db.raw_db in
               loc.loc_id <- Some new_id;
               new_id
           | Some id -> 
               (* update *)
               let sql = 
                 "UPDATE loc SET file=?,line=?,start=?,stop=? WHERE id=?" 
               in
               let stmt = Sqlite3.prepare db.raw_db sql in
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 1 
                    (let v = loc.file in Sqlite3.Data.TEXT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 2 
                    (let v = Int64.of_int loc.line in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 3 
                    (let v = Int64.of_int loc.start in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 4 
                    (let v = Int64.of_int loc.stop in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 5 (Sqlite3.Data.INT id));
               db_must_done db (fun () -> Sqlite3.step stmt);
               id
         in
         curobj_id)

      
  (* General get function for any of the columns *)
  let get ?id ?file ?line ?start ?stop ?(custom_where=("",[])) db =
    (* assemble the SQL query string *)
    let q = "" in
    let first = ref true in
    let f () = if !first then (first := false; " WHERE ") else " AND " 
    in
    let q = match id with 
      | None -> q | Some _b -> q ^ (f()) ^ "loc.id=?" in
    let q = match file with 
      | None -> q | Some _b -> q ^ (f()) ^ "loc.file=?" in
    let q = match line with 
      | None -> q | Some _b -> q ^ (f()) ^ "loc.line=?" in
    let q = match start with 
      | None -> q | Some _b -> q ^ (f()) ^ "loc.start=?" in
    let q = match stop with 
      | None -> q | Some _b -> q ^ (f()) ^ "loc.stop=?" in
    let q = match custom_where with 
      | "",_ -> q | w,_ -> q ^ (f()) ^ "(" ^ w ^ ")" in
    let sql =
      "SELECT loc.id, loc.file, loc.line, loc.start, loc.stop FROM loc " ^ q 
    in
    let stmt=Sqlite3.prepare db.raw_db sql in
    (* bind the position variables to the statement *)
    let bindpos = ref 1 in
    begin
      match id with 
        | None -> () 
        | Some v ->
            db_must_ok db 
              (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
            incr bindpos          
    end;
    begin 
      match file with 
        | None -> () 
        | Some v ->
            db_must_ok db 
              (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.TEXT v));
            incr bindpos
    end;
    begin
      match line with 
        | None -> () 
        | Some v -> 
            db_must_ok db 
              (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
            incr bindpos
    end;
    begin 
      match start with 
        | None -> () 
        | Some v ->
            db_must_ok db 
              (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
            incr bindpos
    end;
    begin
      match stop with 
        | None -> () 
        | Some v ->
            db_must_ok db 
              (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
            incr bindpos
    end;
    begin
      match custom_where with 
        | _,[] -> () 
        | _,eb -> 
            List.iter 
              (fun b ->
                 db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos b);
                 incr bindpos) eb
    end;
  (* convert statement into an ocaml object *)
    let of_stmt stmt =
      { (* native fields *)
	loc_id = (match Sqlite3.column stmt 0 with
               | Sqlite3.Data.NULL -> None
               | Sqlite3.Data.INT i -> Some i 
	       | x -> 
		   try Some (Int64.of_string (Sqlite3.Data.to_string x))
		   with _ -> failwith "error: loc id") ;
	file = (match Sqlite3.column stmt 1 with
		 | Sqlite3.Data.NULL -> failwith "null of_stmt"
		 | x -> Sqlite3.Data.to_string x) ;
	line = (match Sqlite3.column stmt 2 with
		 | Sqlite3.Data.NULL -> failwith "null of_stmt"
		 | Sqlite3.Data.INT i -> Int64.to_int i 
		 | x -> 
		     try int_of_string (Sqlite3.Data.to_string x) 
		     with _ -> failwith "error: loc line") ;
	start = (match Sqlite3.column stmt 3 with
		  | Sqlite3.Data.NULL -> failwith "null of_stmt"
		  | Sqlite3.Data.INT i -> Int64.to_int i 
		  | x -> 
		      try int_of_string (Sqlite3.Data.to_string x) 
		      with _ -> failwith "error: loc start") ;
	stop = (match Sqlite3.column stmt 4 with
		 | Sqlite3.Data.NULL -> failwith "null of_stmt"
		 | Sqlite3.Data.INT i -> Int64.to_int i 
		 | x -> 
		     try int_of_string (Sqlite3.Data.to_string x) 
		     with _ -> failwith "error: loc stop")
	(* foreign fields *)
      }
    in 
    (* execute the SQL query *)
    step_fold db stmt of_stmt

end

let int64_from_bool b =
  if b then 1L else 0L

let bool_from_int64 i =
  if i=0L then false else
    if i=1L then true else
      failwith "Db.bool_from_int64"

let int64_from_status = function
  | Scheduled -> 1L
  | Running -> 2L
  | Success -> 3L
  | Timeout -> 4L
  | Unknown -> 5L
  | HighFailure -> 6L

let status_from_int64 i = 
  if i=1L then Scheduled else
    if i=2L then Running else
      if i=3L then Success else
        if i=4L then Timeout else
          if i=5L then Unknown else
            if i=6L then HighFailure else
              failwith "Db.status_from_int64"

module External_proof = struct

  let init db =
    let sql = "CREATE TABLE IF NOT EXISTS external_proof (id INTEGER PRIMARY KEY AUTOINCREMENT,prover INTEGER,timelimit INTEGER,memlimit INTEGER,status INTEGER,result_time REAL,trace TEXT,obsolete INTEGER);" in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  let delete db e =
    let id = e.external_proof_id in
    assert (id <> 0L);
    let sql = "DELETE FROM external_proof WHERE id=?" in
    let stmt = Sqlite3.prepare db.raw_db sql in
    db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
    ignore(step_fold db stmt (fun _ -> ()));
    e.external_proof_id <- 0L

  let add db (e : external_proof) = 
    transaction db 
      (fun () ->
	 assert (e.external_proof_id = 0L);
	 let sql = 
	   "INSERT INTO external_proof VALUES(NULL,?,?,?,?,?,?,?)" 
	 in
	 let stmt = Sqlite3.prepare db.raw_db sql in
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 1 
	      (let v = e.prover in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 2 
	      (let v = Int64.of_int e.timelimit in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 3 
	      (let v = Int64.of_int e.memlimit in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 4 
	      (let v = int64_from_status e.status in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 5 
	      (let v = e.result_time in Sqlite3.Data.FLOAT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 6 
	      (let v = e.trace in Sqlite3.Data.TEXT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 7 
	      (let v = int64_from_bool e.proof_obsolete in Sqlite3.Data.INT v));
	 db_must_done db 
	   (fun () -> Sqlite3.step stmt);
	 let new_id = Sqlite3.last_insert_rowid db.raw_db in
	 e.external_proof_id <- new_id)


  let set_status db e stat =
      transaction db 
        (fun () ->
	   let id = e.external_proof_id in
	   let sql = 
	     "UPDATE external_proof SET status=? WHERE id=?" 
	   in
	   let stmt = Sqlite3.prepare db.raw_db sql in
	   db_must_ok db 
	     (fun () -> Sqlite3.bind stmt 1
		(let v = int64_from_status stat in Sqlite3.Data.INT v));
	   db_must_ok db 
	     (fun () -> Sqlite3.bind stmt 2 (Sqlite3.Data.INT id));
	   db_must_done db (fun () -> Sqlite3.step stmt))
    
  let from_id db id =
      let sql="SELECT external_proof.prover, external_proof.timelimit, external_proof.memlimit, external_proof.status, external_proof.result_time, external_proof.trace, external_proof.obsolete FROM external_proof WHERE external_proof.id=?"
      in
      let stmt=Sqlite3.prepare db.raw_db sql in
      db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
      let l = step_fold db stmt 
        (fun stmt ->
           { external_proof_id = id;
	     prover = 
	       (match Sqlite3.column stmt 0 with
                  | Sqlite3.Data.INT i -> i
                  | _ -> failwith "External_Proof.fromid: bad prover id");
             timelimit =
	       (match Sqlite3.column stmt 1 with
                  | Sqlite3.Data.INT i -> Int64.to_int i 
                  | _ -> failwith "External_Proof.fromid: bad timelimit");
	     memlimit = 
	       (match Sqlite3.column stmt 2 with
                  | Sqlite3.Data.INT i -> Int64.to_int i 
                  | _ -> failwith "External_Proof.fromid: bad memlimit");
	     status =
	       (match Sqlite3.column stmt 3 with
                  | Sqlite3.Data.INT i -> status_from_int64 i
                  | _ -> failwith "External_Proof.fromid: bad status");
	     result_time =
	       (match Sqlite3.column stmt 4 with
                  | Sqlite3.Data.FLOAT f -> f
                  | _ -> failwith "External_Proof.fromid: bad result_time");
	     trace =
	       (match Sqlite3.column stmt 5 with
                  | Sqlite3.Data.TEXT t -> t
                  | _ -> failwith "External_Proof.fromid: bad trace");
	     proof_obsolete =
	       (match Sqlite3.column stmt 6 with
                  | Sqlite3.Data.INT i -> bool_from_int64 i
                  | _ -> failwith "External_Proof.fromid: bad proof_obsolete");
	   })
    in
    match l with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false   

    
(* TODO: update functions for each field
    let update db (e : external_proof) = 
      transaction db 
        (fun () ->
	 | Some id -> (* update *)
		 let sql = 
		   "UPDATE external_proof SET prover=?,timelimit=?,memlimit=?,status=?,result_time=?,trace=?,obsolete=? WHERE id=?" 
		 in
		 let stmt = Sqlite3.prepare db.raw_db sql in
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 1 
		      (let v = e.prover.prover_name in Sqlite3.Data.TEXT v));
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 2 
		      (let v = Int64.of_int e.timelimit in Sqlite3.Data.INT v));
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 3 
		      (let v = Int64.of_int e.memlimit in Sqlite3.Data.INT v));
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 4 
		      (let v = int64_from_pas e.status in Sqlite3.Data.INT v));
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 5 
		      (let v = e.result_time in Sqlite3.Data.FLOAT v));
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 6 
		      (let v = e.trace in Sqlite3.Data.TEXT v));
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 7 
		      (let v = int64_from_bool e.proof_obsolete in Sqlite3.Data.INT v));
		 db_must_ok db 
		   (fun () -> Sqlite3.bind stmt 8 (Sqlite3.Data.INT id));
		 db_must_done db (fun () -> Sqlite3.step stmt);
		 id
	   in
	   curobj_id)
*)

    (* General get function for any of the columns *)
(*
    let get ?(id=None) ?(prover=None) ?(timelimit=None) ?(memlimit=None) ?(status=None) ?(result_time=None) ?(trace=None) ?(obsolete=None) ?(custom_where=("",[])) db =
      (* assemble the SQL query string *)
      let q = "" in
      let _first = ref true in
      let f () = match !_first with |true -> _first := false; " WHERE " |false -> " AND " in
      let q = match id with |None -> q |Some b -> q ^ (f()) ^ "external_proof.id=?" in
      let q = match prover with |None -> q |Some b -> q ^ (f()) ^ "external_proof.prover=?" in
      let q = match timelimit with |None -> q |Some b -> q ^ (f()) ^ "external_proof.timelimit=?" in
      let q = match memlimit with |None -> q |Some b -> q ^ (f()) ^ "external_proof.memlimit=?" in
      let q = match status with |None -> q |Some b -> q ^ (f()) ^ "external_proof.status=?" in
      let q = match result_time with |None -> q |Some b -> q ^ (f()) ^ "external_proof.result_time=?" in
      let q = match trace with |None -> q |Some b -> q ^ (f()) ^ "external_proof.trace=?" in
      let q = match obsolete with |None -> q |Some b -> q ^ (f()) ^ "external_proof.obsolete=?" in
      let q = match custom_where with |"",_ -> q |w,_ -> q ^ (f()) ^ "(" ^ w ^ ")" in
      let sql="SELECT external_proof.id, external_proof.prover, external_proof.timelimit, external_proof.memlimit, external_proof.status, external_proof.result_time, external_proof.trace, external_proof.obsolete FROM external_proof " ^ q in
      let stmt=Sqlite3.prepare db.db sql in
      (* bind the position variables to the statement *)
      let bindpos = ref 1 in
      ignore(match id with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
	       incr bindpos
	    );
      ignore(match prover with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.TEXT v));
	       incr bindpos
	    );
      ignore(match timelimit with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
	       incr bindpos
	    );
      ignore(match memlimit with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
	       incr bindpos
	    );
      ignore(match status with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
	       incr bindpos
	    );
      ignore(match result_time with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.FLOAT v));
	       incr bindpos
	    );
      ignore(match trace with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.TEXT v));
	       incr bindpos
	    );
      ignore(match obsolete with |None -> () |Some v ->
	       db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
	       incr bindpos
	    );
      ignore(match custom_where with |_,[] -> () |_,eb ->
	       List.iter (fun b ->
			    db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos b);
			    incr bindpos
			 ) eb);
      (* convert statement into an ocaml object *)
      let of_stmt stmt =
	t
	  (* native fields *)
	  ~id:(
	    (match Sqlite3.column stmt 0 with
               |Sqlite3.Data.NULL -> None
               |x -> Some (match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: external_proof id")))
	  )
	  ~prover:(
	    (match Sqlite3.column stmt 1 with
               |Sqlite3.Data.NULL -> failwith "null of_stmt"
               |x -> Sqlite3.Data.to_string x)
	  )
	  ~timelimit:(
	    (match Sqlite3.column stmt 2 with
               |Sqlite3.Data.NULL -> failwith "null of_stmt"
               |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: external_proof timelimit"))
	  )
	  ~memlimit:(
	    (match Sqlite3.column stmt 3 with
               |Sqlite3.Data.NULL -> failwith "null of_stmt"
               |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: external_proof memlimit"))
	  )
	  ~status:(
	    (match Sqlite3.column stmt 4 with
               |Sqlite3.Data.NULL -> failwith "null of_stmt"
               |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: external_proof status"))
	  )
	  ~result_time:(
	    (match Sqlite3.column stmt 5 with
               |Sqlite3.Data.NULL -> failwith "null of_stmt"
               |x -> match x with |Sqlite3.Data.FLOAT i -> i|x -> (try float_of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: external_proof result_time"))
	  )
	  ~trace:(
	    (match Sqlite3.column stmt 6 with
               |Sqlite3.Data.NULL -> failwith "null of_stmt"
               |x -> Sqlite3.Data.to_string x)
	  )
	  ~obsolete:(
	    (match Sqlite3.column stmt 7 with
               |Sqlite3.Data.NULL -> failwith "null of_stmt"
               |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: external_proof obsolete"))
	  )
	  (* foreign fields *)
	  db
      in 
      (* execute the SQL query *)
      step_fold db stmt of_stmt
	
*)
end


module Goal = struct
  
  type t = goal
      
  let hash g = Hashtbl.hash g.goal_id 

  let equal g1 g2 = g1.goal_id = g2.goal_id

  let compare g1 g2 = Pervasives.compare g1.goal_id g2.goal_id

  let init db =
    (* TODO: store the goal origin too *)
(*
  mutable goal_id : db_ident;
  mutable task : Why.Task.task;
  mutable task_checksum: string;
  mutable proved : bool;
  (** invariant: g.proved == true iff
      exists attempts a in g.attempts, a.obsolete == false and
      (a = External e and e.result == Valid or
      a = Transf(gl) and forall g in gl, g.proved)
  *)
  mutable observers: (bool -> unit) list;
  (** observers that wants to be notified by any changes of the proved status *)
  mutable external_proofs : external_proof list;
  mutable transformations : transf list;
*)
    let sql = "create table if not exists goal (goal_id integer primary key autoincrement,task_checksum text,proved integer);" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    let sql = "create table if not exists map_goal_prover_external_proof (goal_id integer, prover_id integer, external_proof_id integer, primary key(goal_id, prover_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)


(*
  let init db =
    let sql = "create table if not exists goal (id integer primary key autoincrement,task_checksum text,parent_id integer,name text,pos_id integer,proved integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_external_proofs_goal_external_proof (goal_id integer, external_proof_id integer, primary key(goal_id, external_proof_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_transformations_goal_transf (goal_id integer, transf_id integer, primary key(goal_id, transf_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    ()
*)

  let add db (g : goal) = 
    transaction db 
      (fun () ->
	 assert (g.goal_id = 0L);
         assert (g.external_proofs = []);
         assert (g.transformations = []);
	 let sql = 
	   "INSERT INTO goal VALUES(NULL,?,?)" 
	 in
	 let stmt = Sqlite3.prepare db.raw_db sql in
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 1 
	      (let v = g.task_checksum in Sqlite3.Data.TEXT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 2 
	      (let v = int64_from_bool g.proved in Sqlite3.Data.INT v));
	 db_must_done db 
	   (fun () -> Sqlite3.step stmt);
	 let new_id = Sqlite3.last_insert_rowid db.raw_db in         
         Format.eprintf "Db.Goal.add: add a new goal with id=%Ld@." new_id;
	 g.goal_id <- new_id)


  let get_external_proof db ~prover g =
    let sql="SELECT map_goal_prover_external_proof.external_proof_id FROM map_goal_prover_external_proof WHERE goal_id=? AND prover_id=?" in
    let stmt = Sqlite3.prepare db.raw_db sql in
    db_must_ok db 
      (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT g.goal_id));
    db_must_ok db 
      (fun () -> Sqlite3.bind stmt 2 (Sqlite3.Data.INT prover.prover_id));
    let l = step_fold db stmt 
      (fun stmt ->  
         match Sqlite3.column stmt 0 with
           | Sqlite3.Data.INT i -> i 
              | x -> (try Int64.of_string (Sqlite3.Data.to_string x) 
                      with _ -> failwith "Db.get_external_proof"))
    in
    match l with
      | [] -> raise Not_found
      | [x] -> External_proof.from_id db x
      | _ -> assert false   

    let add_external_proof db ~prover g =
      let e = {
        external_proof_id = 0L;
        prover = prover.prover_id;
        timelimit = 0;
        memlimit = 0;
        status = Scheduled;
        result_time = 0.0;
        trace = "";
        proof_obsolete = false;
      }
      in
      External_proof.add db e;
      let id = e.external_proof_id in
      transaction db 
        (fun () ->
	   let sql = 
	     "INSERT INTO map_goal_prover_external_proof VALUES(?,?,?)" 
	   in
	   let stmt = Sqlite3.prepare db.raw_db sql in
	   db_must_ok db 
	     (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT g.goal_id));
	   db_must_ok db 
	     (fun () -> Sqlite3.bind stmt 2 (Sqlite3.Data.INT prover.prover_id));
	   db_must_ok db 
	     (fun () -> Sqlite3.bind stmt 3 (Sqlite3.Data.INT id));
	   db_must_done db 
	     (fun () -> Sqlite3.step stmt);
        );
      e


(* TODO make specific update functions for each field ! *)
(*
  let update db (g : goal) =
    transaction db 
      (fun () ->
	 assert (g.goal_id <> 0L);
	 let sql = 
	   "UPDATE goal SET task_checksum=?,timelimit=?,memlimit=?,status=?,result_time=?,trace=?,obsolete=? WHERE id=?" 
	 in
	 let stmt = Sqlite3.prepare db.raw_db sql in
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 1 
	      (let v = e.prover.prover_name in Sqlite3.Data.TEXT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 2 
	      (let v = Int64.of_int e.timelimit in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 3 
	      (let v = Int64.of_int e.memlimit in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 4 
	      (let v = int64_from_pas e.status in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 5 
	      (let v = e.result_time in Sqlite3.Data.FLOAT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 6 
	      (let v = e.trace in Sqlite3.Data.TEXT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 7 
	      (let v = int64_from_bool e.proof_obsolete in Sqlite3.Data.INT v));
	 db_must_ok db 
	   (fun () -> Sqlite3.bind stmt 8 (Sqlite3.Data.INT id));
	 db_must_done db (fun () -> Sqlite3.step stmt);
	 id)
*)


(*
  let init db =
    let sql = "create table if not exists goal (id integer primary key autoincrement,task_checksum text,parent_id integer,name text,pos_id integer,proved integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_external_proofs_goal_external_proof (goal_id integer, external_proof_id integer, primary key(goal_id, external_proof_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_transformations_goal_transf (goal_id integer, transf_id integer, primary key(goal_id, transf_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    ()
*)

  (* object definition *)
(*
  let t ?(id=None) ~task_checksum ~parent ~name ~pos ~external_proofs ~transformations ~proved db : t = object
    (* get functions *)
    val mutable _id = id
    method id : int64 option = _id
    val mutable _task_checksum = task_checksum
    method task_checksum : string = _task_checksum
    val mutable _parent = parent
    method parent : Transf.t = _parent
    val mutable _name = name
    method name : string = _name
    val mutable _pos = pos
    method pos : Loc.t = _pos
    val mutable _external_proofs = external_proofs
    method external_proofs : External_proof.t list = _external_proofs
    val mutable _transformations = transformations
    method transformations : Transf.t list = _transformations
    val mutable _proved = proved
    method proved : int64 = _proved

    (* set functions *)
    method set_id v =
      _id <- v
    method set_task_checksum v =
      _task_checksum <- v
    method set_parent v =
      _parent <- v
    method set_name v =
      _name <- v
    method set_pos v =
      _pos <- v
    method set_external_proofs v =
      _external_proofs <- v
    method set_transformations v =
      _transformations <- v
    method set_proved v =
      _proved <- v

    (* admin functions *)
    method delete =
      match _id with
      |None -> ()
      |Some id ->
        let sql = "DELETE FROM goal WHERE id=?" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
        ignore(step_fold db stmt (fun _ -> ()));
        _id <- None

    method save = transaction db (fun () ->
      (* insert any foreign-one fields into their table and get id *)
      let _parent_id = parent#save in
      let _pos_id = pos#save in
      let _curobj_id = match _id with
      |None -> (* insert new record *)
        let sql = "INSERT INTO goal VALUES(NULL,?,?,?,?,?)" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (let v = _task_checksum in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (let v = _parent_id in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 3 (let v = _name in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 4 (let v = _pos_id in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 5 (let v = _proved in Sqlite3.Data.INT v));
        db_must_done db (fun () -> Sqlite3.step stmt);
        let __id = Sqlite3.last_insert_rowid db.db in
        _id <- Some __id;
        __id
      |Some id -> (* update *)
        let sql = "UPDATE goal SET task_checksum=?,parent_id=?,name=?,pos_id=?,proved=? WHERE id=?" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (let v = _task_checksum in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (let v = _parent_id in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 3 (let v = _name in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 4 (let v = _pos_id in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 5 (let v = _proved in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 6 (Sqlite3.Data.INT id));
        db_must_done db (fun () -> Sqlite3.step stmt);
        id
      in
      List.iter (fun f ->
        let _refobj_id = f#save in
        let sql = "INSERT OR IGNORE INTO map_external_proofs_goal_external_proof VALUES(?,?)" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT _curobj_id));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (Sqlite3.Data.INT _refobj_id));
        ignore(step_fold db stmt (fun _ -> ()));
      ) _external_proofs;
      let ids = String.concat "," (List.map (fun x -> match x#id with |None -> assert false |Some x -> Int64.to_string x) _external_proofs) in
      let sql = "DELETE FROM map_external_proofs_goal_external_proof WHERE goal_id=? AND (external_proof_id NOT IN (" ^ ids ^ "))" in
      let stmt = Sqlite3.prepare db.db sql in
      db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT _curobj_id));
      ignore(step_fold db stmt (fun _ -> ()));
      List.iter (fun f ->
        let _refobj_id = f#save in
        let sql = "INSERT OR IGNORE INTO map_transformations_goal_transf VALUES(?,?)" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT _curobj_id));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (Sqlite3.Data.INT _refobj_id));
        ignore(step_fold db stmt (fun _ -> ()));
      ) _transformations;
      let ids = String.concat "," (List.map (fun x -> match x#id with |None -> assert false |Some x -> Int64.to_string x) _transformations) in
      let sql = "DELETE FROM map_transformations_goal_transf WHERE goal_id=? AND (transf_id NOT IN (" ^ ids ^ "))" in
      let stmt = Sqlite3.prepare db.db sql in
      db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT _curobj_id));
      ignore(step_fold db stmt (fun _ -> ()));
      _curobj_id
    )
  end
*)

  let from_id _db _id : goal =
    assert false
      (*
	let sql="SELECT goal.id, goal.task_checksum, goal.parent_id, goal.name, goal.pos_id, goal.proved, goal_pos.id, goal_pos.file, goal_pos.line, goal_pos.start, goal_pos.stop, goal_parent.id, goal_parent.name, goal_parent.obsolete FROM goal LEFT JOIN transf AS goal_parent ON (goal_parent.id = goal.parent_id) LEFT JOIN loc AS goal_pos ON (goal_pos.id = goal.pos_id) " ^ q in
	let stmt=Sqlite3.prepare db.db sql in
      *)

  (* General get function for any of the columns *)
(*
  let get ?(id=None) ?(task_checksum=None) ?(name=None) ?(proved=None) ?(custom_where=("",[])) db =
    (* assemble the SQL query string *)
    let q = "" in
    let _first = ref true in
    let f () = match !_first with |true -> _first := false; " WHERE " |false -> " AND " in
    let q = match id with |None -> q |Some b -> q ^ (f()) ^ "goal.id=?" in
    let q = match task_checksum with |None -> q |Some b -> q ^ (f()) ^ "goal.task_checksum=?" in
    let q = match name with |None -> q |Some b -> q ^ (f()) ^ "goal.name=?" in
    let q = match proved with |None -> q |Some b -> q ^ (f()) ^ "goal.proved=?" in
    let q = match custom_where with |"",_ -> q |w,_ -> q ^ (f()) ^ "(" ^ w ^ ")" in
    let sql="SELECT goal.id, goal.task_checksum, goal.parent_id, goal.name, goal.pos_id, goal.proved, goal_pos.id, goal_pos.file, goal_pos.line, goal_pos.start, goal_pos.stop, goal_parent.id, goal_parent.name, goal_parent.obsolete FROM goal LEFT JOIN transf AS goal_parent ON (goal_parent.id = goal.parent_id) LEFT JOIN loc AS goal_pos ON (goal_pos.id = goal.pos_id) " ^ q in
    let stmt=Sqlite3.prepare db.db sql in
    (* bind the position variables to the statement *)
    let bindpos = ref 1 in
    ignore(match id with |None -> () |Some v ->
      db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
      incr bindpos
    );
    ignore(match task_checksum with |None -> () |Some v ->
      db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.TEXT v));
      incr bindpos
    );
    ignore(match name with |None -> () |Some v ->
      db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.TEXT v));
      incr bindpos
    );
    ignore(match proved with |None -> () |Some v ->
      db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
      incr bindpos
    );
    ignore(match custom_where with |_,[] -> () |_,eb ->
      List.iter (fun b ->
        db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos b);
        incr bindpos
      ) eb);
    (* convert statement into an ocaml object *)
    let of_stmt stmt =
    t
      (* native fields *)
      ~id:(
      (match Sqlite3.column stmt 0 with
        |Sqlite3.Data.NULL -> None
        |x -> Some (match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal id")))
      )
      ~task_checksum:(
      (match Sqlite3.column stmt 1 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> Sqlite3.Data.to_string x)
      )
      ~name:(
      (match Sqlite3.column stmt 3 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> Sqlite3.Data.to_string x)
      )
      ~proved:(
      (match Sqlite3.column stmt 5 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal proved"))
      )
      (* foreign fields *)
      ~parent:(
        Transf.t
          (* native fields *)
          ~id:(
          (match Sqlite3.column stmt 11 with
            |Sqlite3.Data.NULL -> None
            |x -> Some (match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal_parent id")))
          )
          ~name:(
          (match Sqlite3.column stmt 12 with
            |Sqlite3.Data.NULL -> failwith "null of_stmt"
            |x -> Sqlite3.Data.to_string x)
          )
          ~obsolete:(
          (match Sqlite3.column stmt 13 with
            |Sqlite3.Data.NULL -> failwith "null of_stmt"
            |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal_parent obsolete"))
          )
          (* foreign fields *)
          ~subgoals:(
            (* foreign many-many mapping field *)
            let sql' = "select goal_id from map_subgoals_transf_goal where transf_id=?" in
            let stmt' = Sqlite3.prepare db.db sql' in
            let transf__id = Sqlite3.column stmt 11 in
            db_must_ok db (fun () -> Sqlite3.bind stmt' 1 transf__id);
            List.flatten (step_fold db stmt' (fun s ->
              let i = match Sqlite3.column s 0 with |Sqlite3.Data.INT i -> i |_ -> assert false in
              Goal.get ~id:(Some i) db)
            ))
        db
        )
      ~pos:(
        Loc.t
          (* native fields *)
          ~id:(
          (match Sqlite3.column stmt 6 with
            |Sqlite3.Data.NULL -> None
            |x -> Some (match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal_pos id")))
          )
          ~file:(
          (match Sqlite3.column stmt 7 with
            |Sqlite3.Data.NULL -> failwith "null of_stmt"
            |x -> Sqlite3.Data.to_string x)
          )
          ~line:(
          (match Sqlite3.column stmt 8 with
            |Sqlite3.Data.NULL -> failwith "null of_stmt"
            |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal_pos line"))
          )
          ~start:(
          (match Sqlite3.column stmt 9 with
            |Sqlite3.Data.NULL -> failwith "null of_stmt"
            |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal_pos start"))
          )
          ~stop:(
          (match Sqlite3.column stmt 10 with
            |Sqlite3.Data.NULL -> failwith "null of_stmt"
            |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: goal_pos stop"))
          )
          (* foreign fields *)
        db
        )
      ~external_proofs:(
        (* foreign many-many mapping field *)
        let sql' = "select external_proof_id from map_external_proofs_goal_external_proof where goal_id=?" in
        let stmt' = Sqlite3.prepare db.db sql' in
        let goal__id = Sqlite3.column stmt 0 in
        db_must_ok db (fun () -> Sqlite3.bind stmt' 1 goal__id);
        List.flatten (step_fold db stmt' (fun s ->
          let i = match Sqlite3.column s 0 with |Sqlite3.Data.INT i -> i |_ -> assert false in
          External_proof.get ~id:(Some i) db)
        ))
      ~transformations:(
        (* foreign many-many mapping field *)
        let sql' = "select transf_id from map_transformations_goal_transf where goal_id=?" in
        let stmt' = Sqlite3.prepare db.db sql' in
        let goal__id = Sqlite3.column stmt 0 in
        db_must_ok db (fun () -> Sqlite3.bind stmt' 1 goal__id);
        List.flatten (step_fold db stmt' (fun s ->
          let i = match Sqlite3.column s 0 with |Sqlite3.Data.INT i -> i |_ -> assert false in
          Transf.get ~id:(Some i) db)
        ))
    db
    in 
    (* execute the SQL query *)
    step_fold db stmt of_stmt
*)

end

module Transf = struct


(*
  let init db =
    let sql = "create table if not exists transf (id integer primary key autoincrement,name text,obsolete integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_subgoals_transf_goal (transf_id integer, goal_id integer, primary key(transf_id, goal_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    ()

  (* object definition *)
  let t ?(id=None) ~name ~obsolete ~subgoals db : t = object
    (* get functions *)
    val mutable _id = id
    method id : int64 option = _id
    val mutable _name = name
    method name : string = _name
    val mutable _obsolete = obsolete
    method obsolete : int64 = _obsolete
    val mutable _subgoals = subgoals
    method subgoals : Goal.t list = _subgoals

    (* set functions *)
    method set_id v =
      _id <- v
    method set_name v =
      _name <- v
    method set_obsolete v =
      _obsolete <- v
    method set_subgoals v =
      _subgoals <- v

    (* admin functions *)
    method delete =
      match _id with
      |None -> ()
      |Some id ->
        let sql = "DELETE FROM transf WHERE id=?" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
        ignore(step_fold db stmt (fun _ -> ()));
        _id <- None

    method save = transaction db (fun () ->
      (* insert any foreign-one fields into their table and get id *)
      let _curobj_id = match _id with
      |None -> (* insert new record *)
        let sql = "INSERT INTO transf VALUES(NULL,?,?)" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (let v = _name in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (let v = _obsolete in Sqlite3.Data.INT v));
        db_must_done db (fun () -> Sqlite3.step stmt);
        let __id = Sqlite3.last_insert_rowid db.db in
        _id <- Some __id;
        __id
      |Some id -> (* update *)
        let sql = "UPDATE transf SET name=?,obsolete=? WHERE id=?" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (let v = _name in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (let v = _obsolete in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 3 (Sqlite3.Data.INT id));
        db_must_done db (fun () -> Sqlite3.step stmt);
        id
      in
      List.iter (fun f ->
        let _refobj_id = f#save in
        let sql = "INSERT OR IGNORE INTO map_subgoals_transf_goal VALUES(?,?)" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT _curobj_id));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (Sqlite3.Data.INT _refobj_id));
        ignore(step_fold db stmt (fun _ -> ()));
      ) _subgoals;
      let ids = String.concat "," (List.map (fun x -> match x#id with |None -> assert false |Some x -> Int64.to_string x) _subgoals) in
      let sql = "DELETE FROM map_subgoals_transf_goal WHERE transf_id=? AND (goal_id NOT IN (" ^ ids ^ "))" in
      let stmt = Sqlite3.prepare db.db sql in
      db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT _curobj_id));
      ignore(step_fold db stmt (fun _ -> ()));
      _curobj_id
    )
  end

  (* General get function for any of the columns *)
  let get ?(id=None) ?(name=None) ?(obsolete=None) ?(custom_where=("",[])) db =
    (* assemble the SQL query string *)
    let q = "" in
    let _first = ref true in
    let f () = match !_first with |true -> _first := false; " WHERE " |false -> " AND " in
    let q = match id with |None -> q |Some b -> q ^ (f()) ^ "transf.id=?" in
    let q = match name with |None -> q |Some b -> q ^ (f()) ^ "transf.name=?" in
    let q = match obsolete with |None -> q |Some b -> q ^ (f()) ^ "transf.obsolete=?" in
    let q = match custom_where with |"",_ -> q |w,_ -> q ^ (f()) ^ "(" ^ w ^ ")" in
    let sql="SELECT transf.id, transf.name, transf.obsolete FROM transf " ^ q in
    let stmt=Sqlite3.prepare db.db sql in
    (* bind the position variables to the statement *)
    let bindpos = ref 1 in
    ignore(match id with |None -> () |Some v ->
      db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
      incr bindpos
    );
    ignore(match name with |None -> () |Some v ->
      db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.TEXT v));
      incr bindpos
    );
    ignore(match obsolete with |None -> () |Some v ->
      db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos (Sqlite3.Data.INT v));
      incr bindpos
    );
    ignore(match custom_where with |_,[] -> () |_,eb ->
      List.iter (fun b ->
        db_must_ok db (fun () -> Sqlite3.bind stmt !bindpos b);
        incr bindpos
      ) eb);
    (* convert statement into an ocaml object *)
    let of_stmt stmt =
    t
      (* native fields *)
      ~id:(
      (match Sqlite3.column stmt 0 with
        |Sqlite3.Data.NULL -> None
        |x -> Some (match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: transf id")))
      )
      ~name:(
      (match Sqlite3.column stmt 1 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> Sqlite3.Data.to_string x)
      )
      ~obsolete:(
      (match Sqlite3.column stmt 2 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: transf obsolete"))
      )
      (* foreign fields *)
      ~subgoals:(
        (* foreign many-many mapping field *)
        let sql' = "select goal_id from map_subgoals_transf_goal where transf_id=?" in
        let stmt' = Sqlite3.prepare db.db sql' in
        let transf__id = Sqlite3.column stmt 0 in
        db_must_ok db (fun () -> Sqlite3.bind stmt' 1 transf__id);
        List.flatten (step_fold db stmt' (fun s ->
          let i = match Sqlite3.column s 0 with |Sqlite3.Data.INT i -> i |_ -> assert false in
          Goal.get ~id:(Some i) db)
        ))
    db
    in 
    (* execute the SQL query *)
    step_fold db stmt of_stmt

*)

end

module Main = struct

  let init db =
    let sql = "create table if not exists rootgoals (goal_id integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    ()

  let all_root_goals db =
    let sql="SELECT goal_id FROM rootgoals" in
    let stmt=Sqlite3.prepare db.raw_db sql in
    let of_stmt stmt =
      match Sqlite3.column stmt 0 with
        | Sqlite3.Data.INT i -> i 
	| x -> (try Int64.of_string (Sqlite3.Data.to_string x) 
		with _ -> failwith "Db.all_root_goals")
    in
    let goals_ids = step_fold db stmt of_stmt in
    goals_ids

end

let init_db ?(busyfn=default_busyfn) ?(mode=Immediate) db_name =
  match !current_db with
    | None ->
        let db = {
	  raw_db = Sqlite3.db_open db_name; 
	  in_transaction = 0; 
	  mode = mode; 
	  busyfn = busyfn;
        } 
	in
	current_db := Some db;
	Prover.init db;
	Loc.init db;
	External_proof.init db;
	Goal.init db;
	(*
          Transf.init db;
	*)
	Main.init db

    | Some _ -> failwith "database already opened"

let init_base f = init_db f

let root_goals () = 
  let db = current () in
  let l = Main.all_root_goals db in
  List.rev_map (Goal.from_id db) l
    
  


(*
let string_from_result = function
  | Why.Driver.Valid -> "Valid"
  | Why.Driver.Invalid -> "Invalid"
  | Why.Driver.Unknown s -> "Unknown " ^ s
  | Why.Driver.Failure s -> "Failure " ^ s
  | Why.Driver.Timeout -> "Timeout"
  | Why.Driver.HighFailure -> "HighFailure"
*)


exception AlreadyAttempted

let try_prover ~debug ~timelimit ~memlimit ~prover ~command ~driver 
    (g : goal) : unit -> unit =
  let db = current () in
  let attempt =
    try
      if debug then Format.printf "looking for an attempt with same prover@.";
      let a = Goal.get_external_proof db ~prover g in
      if debug then Format.printf "attempt found, status=%a@." print_status a.status;
      match a.status with
          (* if already in progress, do not try again *)
        | Scheduled | Running -> raise AlreadyAttempted
          (* if already non-obsolete result within the timelimit, do not try again *)
        | Success | Unknown | HighFailure ->
            if a.proof_obsolete then a else raise AlreadyAttempted
          (* if already non-obsolete timeout with a higher or equal timelimit,
             do not try again *)
        | Timeout -> 
            if a.proof_obsolete then a else
              if a.timelimit < timelimit then a 
              else raise AlreadyAttempted
    with Not_found ->
      if debug then Format.printf "no attempt found, adding one@.";
      Goal.add_external_proof db ~prover g
  in
  if debug then Format.printf "setting attempt status to Scheduled@.";
  External_proof.set_status db attempt Scheduled;
  if debug then Format.eprintf "Task : %a@." Why.Pretty.print_task g.task;
  if debug then Format.eprintf "Task for prover: %a@." (Why.Driver.print_task driver) g.task;
  let callback = 
    try 
      Why.Driver.prove_task ~debug ~command ~timelimit ~memlimit driver g.task
    with 
    | Why.Driver.Error e ->
        Format.eprintf "Db.try_prover: prove_task reports %a@." 
          Why.Driver.report e;
        raise Exit
    | e ->
        try
          Printexc.print (fun () -> raise e) ()
        with _ -> raise Exit
  in
  fun () ->
    if debug then Format.printf "setting attempt status to Running@.";
    External_proof.set_status db attempt Running;
    let r = callback () in
    if debug then Format.eprintf "prover result: %a@." Why.Call_provers.print_prover_result r;
    match r.Why.Call_provers.pr_answer with
      | Why.Call_provers.Valid ->
          External_proof.set_status db attempt Success;
          (* TODO: update "proved" status of goal and its parents *)
          ()         
      | Why.Call_provers.Timeout ->
          External_proof.set_status db attempt Timeout
      | Why.Call_provers.Invalid | Why.Call_provers.Unknown _ ->
          External_proof.set_status db attempt Unknown
      | Why.Call_provers.Failure _ | Why.Call_provers.HighFailure ->
          External_proof.set_status db attempt HighFailure
      

let add_transformation (_g : goal) (_t : transf) :  unit =
  assert false (* TODO *)

let add_or_replace_task (name : Why.Decl.prsymbol) (t : Why.Task.task) : goal =
  (* TODO: replace if already exists *)
  let g = {
    goal_id = 0L;
    goal_origin = Goal name;
    task = t;
    task_checksum = ""; (* TODO: md5sum (marshall ?) *)
    proved = false;
    observers = [];
    external_proofs = [];
    transformations = [];
  }
  in
  Goal.add (current()) g;
  g



let read_db_from_file (_file : string) : goal list =
  assert false (* TODO *)

