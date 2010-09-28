(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

open Why
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
  prerr_endline "Db.default_busyfn WARNING: busy";
  (* Thread.delay (Random.float 1.) *)
  ignore (Unix.select [] [] [] (Random.float 1.))
  
let raise_sql_error x = raise (Sqlite3.Error (Rc.to_string x))
  
 
(* retry until a non-BUSY error code is returned *)
let rec db_busy_retry db fn =
  match fn () with
    | Rc.BUSY -> 
        db.busyfn db.raw_db; db_busy_retry db fn
    | x -> 
        x
       
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
  try 
    db_must_ok db 
      (fun () -> exec db.raw_db ("BEGIN " ^ m ^ " TRANSACTION"));
    assert (db.in_transaction = 0);
    db.in_transaction <- 1;
    let res = fn () in
    db_must_ok db (fun () -> exec db.raw_db "END TRANSACTION");
    assert (db.in_transaction = 1);
    db.in_transaction <- 0;
    res
  with
      e ->
        prerr_string "Db.transaction WARNING: exception: ";
        prerr_endline (Printexc.to_string e);
        prerr_endline "== exception backtrace ==";
        Printexc.print_backtrace stderr;
        prerr_endline "== end of backtrace ==";
        db_must_ok db (fun () -> exec db.raw_db "END TRANSACTION");
        assert (db.in_transaction = 1);
        db.in_transaction <- 0;
        raise e
    
  
(* iterate over a result set *)
let step_fold db stmt iterfn =
  let stepfn () = Sqlite3.step stmt in
  let rec fn a = match db_busy_retry db stepfn with
    | Sqlite3.Rc.ROW -> fn (iterfn stmt :: a)
    | Sqlite3.Rc.DONE -> a
    | x -> raise_sql_error x
  in
  fn []

(* DB/SQL helpers *)

let bind db sql l =
  let stmt = Sqlite3.prepare db.raw_db sql in
  let _ =
    List.fold_left
      (fun i v -> db_must_ok db (fun () -> Sqlite3.bind stmt i v); succ i)
      1 l
  in stmt

(*
let stmt_column_INT stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.INT i -> i
    | _ -> failwith msg

let stmt_column_FLOAT stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.FLOAT i -> i
    | _ -> failwith msg

let stmt_column_TEXT stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.TEXT i -> i
    | _ -> failwith msg
*)

let stmt_column_int stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.INT i -> Int64.to_int i
    | _ -> failwith msg

let int64_from_bool b =
  if b then 1L else 0L

let bool_from_int64 i =
  if i=0L then false else
    if i=1L then true else
      failwith "Db.bool_from_int64"

let stmt_column_bool stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.INT i -> bool_from_int64 i
    | _ -> failwith msg

let stmt_column_string stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.TEXT i -> i
    | _ -> failwith msg

(** Data *)

type prover_id =
    { prover_id : int;
      prover_name : string;
    }

let prover_name p = p.prover_name

module Hprover = Hashtbl.Make
  (struct
     type t = prover_id
     let equal p1 p2 = p1.prover_id == p2.prover_id
     let hash p = Hashtbl.hash p.prover_id
   end)

type transf_id =
    { transf_id : int;
      transf_name : string;
    }

let transf_name t = t.transf_name

module Htransf = Hashtbl.Make
  (struct
     type t = transf_id
     let equal t1 t2 = t1.transf_id == t2.transf_id
     let hash t = Hashtbl.hash t.transf_id
   end)




type proof_status =
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | Failure (** external prover call failed *)

type proof_attempt = {
    mutable proof_attempt_id : int;
    mutable prover : prover_id;
    mutable timelimit : int;
    mutable memlimit : int;
    mutable status : proof_status;
    mutable result_time : float;
    mutable edited_as : string;
    mutable proof_obsolete : bool;
}

let prover p = p.prover
let status p = p.status
let proof_obsolete p = p.proof_obsolete
let time p = p.result_time
let edited_as p = p.edited_as

type transf =
    { mutable transf_id : transf_id;
      mutable subgoals : goal list;
    }

and goal = {
  mutable goal_id : int;
  mutable task_checksum: string;
  mutable proved : bool;
  mutable external_proofs : proof_attempt Hprover.t;
  mutable transformations : transf Htransf.t;
}

(** goal accessors *)

let task_checksum g = g.task_checksum
let proved g = g.proved
let external_proofs g = g.external_proofs
let transformations g = g.transformations

(** transf accessors *)

let transf_id t = t.transf_id
let subgoals t = t.subgoals



type theory 

let theory_name _ = assert false
let goals _ = assert false
let verified _ = assert false

type file = int64 

let file_name _ = assert false
let theories _ = assert false




module ProverId = struct

  let init db =
    let sql = 
      "CREATE TABLE IF NOT EXISTS prover \
       (prover_id INTEGER PRIMARY KEY AUTOINCREMENT,prover_name TEXT);" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    let sql = 
      "CREATE UNIQUE INDEX IF NOT EXISTS prover_name_idx \
       ON prover (prover_name)" 
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
         let stmt = bind db sql [ Sqlite3.Data.TEXT name ] in
         db_must_done db (fun () -> Sqlite3.step stmt);
         let new_id = Sqlite3.last_insert_rowid db.raw_db in
         { prover_id = Int64.to_int new_id ; 
	   prover_name = name })

  let get db name =
    let sql =
      "SELECT prover.prover_id, prover.prover_name FROM prover \
       WHERE prover.prover_name=?" 
    in
    let stmt = bind db sql [Sqlite3.Data.TEXT name] in
    (* convert statement into record *)
    let of_stmt stmt =
      { prover_id = stmt_column_int stmt 0 "ProverId.get: bad prover id";
	prover_name = stmt_column_string stmt 1 "ProverId.get: bad prover name";
      }
    in 
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

  let from_id db id =
    let sql =
      "SELECT prover.prover_id, prover.prover_name FROM prover \
       WHERE prover.prover_id=?" 
    in
    let stmt = bind db sql [Sqlite3.Data.INT id] in
    (* convert statement into record *)
    let of_stmt stmt =
      { prover_id = Int64.to_int id ;
	prover_name = stmt_column_string stmt 1 
          "ProverId.from_id: bad prover_name";
      }
    in 
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

end

(*
let prover_memo = Hashtbl.create 7

let get_prover_from_id id =
  try
    Hashtbl.find prover_memo id
  with Not_found ->
    let p =
      let db = current () in
      try ProverId.from_id db id
      with Not_found -> assert false
    in
    Hashtbl.add prover_memo id p;
    p

let prover e = get_prover_from_id e.prover

let get_prover name (* ~short ~long ~command ~driver *) =
  let db = current () in
(*
  let checksum = Digest.file driver in
*)
  try ProverId.get db name (* ~short ~long ~command ~checksum *)
  with Not_found -> 
    ProverId.add db name (* ~short ~long ~command ~checksum *)
 
*)
	

(*
module Loc = struct

  let init db =
    let sql = 
      "CREATE TABLE IF NOT EXISTS loc \
       (id INTEGER PRIMARY KEY AUTOINCREMENT,file TEXT,line INTEGER,\
        start INTEGER,stop INTEGER);" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  (* admin functions *)
  let delete db loc =
    match loc.loc_id with
      | None -> ()
      | Some id ->
          let sql = "DELETE FROM loc WHERE id=?" in
          let stmt = bind db sql [Sqlite3.Data.INT id] in
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
               let stmt = bind db sql [
                 Sqlite3.Data.TEXT loc.file ;
                 Sqlite3.Data.INT (Int64.of_int loc.line);
                 Sqlite3.Data.INT (Int64.of_int loc.start);
                 Sqlite3.Data.INT (Int64.of_int loc.stop);
               ] 
               in
               db_must_done db (fun () -> Sqlite3.step stmt);
               let new_id = Sqlite3.last_insert_rowid db.raw_db in
               loc.loc_id <- Some new_id;
               new_id
           | Some id -> 
               (* update *)
               let sql = 
                 "UPDATE loc SET file=?,line=?,start=?,stop=? WHERE id=?" 
               in
               let stmt = bind db sql [
                 Sqlite3.Data.TEXT loc.file ;
                 Sqlite3.Data.INT (Int64.of_int loc.line);
                 Sqlite3.Data.INT (Int64.of_int loc.start);
                 Sqlite3.Data.INT (Int64.of_int loc.stop);
                 Sqlite3.Data.INT id;
               ] 
               in
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

*)

let int64_from_status = function
  | Success -> 1L
  | Timeout -> 2L
  | Unknown -> 3L
  | Failure -> 4L

let status_from_int64 i = 
  if i=1L then Success else
    if i=2L then Timeout else
      if i=3L then Unknown else
        if i=4L then Failure else
          failwith "Db.status_from_int64"

(*

module External_proof = struct

  let init db =
    let sql = 
      "CREATE TABLE IF NOT EXISTS external_proof \
       (external_proof_id INTEGER PRIMARY KEY AUTOINCREMENT,\
        prover INTEGER,timelimit INTEGER,memlimit INTEGER,\
        status INTEGER,result_time REAL,trace TEXT,obsolete INTEGER);" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  let delete db e =
    let id = e.external_proof_id in
    assert (id <> 0L);
    let sql = "DELETE FROM external_proof WHERE external_proof_id=?" in
    let stmt = bind db sql [ Sqlite3.Data.INT id ] in
    ignore(step_fold db stmt (fun _ -> ()));
    e.external_proof_id <- 0L

  let add db (e : external_proof) = 
    transaction db 
      (fun () ->
	 assert (e.external_proof_id = 0L);
	 let sql = "INSERT INTO external_proof VALUES(NULL,?,?,?,?,?,?,?)" in
	 let stmt = bind db sql [
           Sqlite3.Data.INT e.prover ;
           Sqlite3.Data.INT (Int64.of_int e.timelimit);
           Sqlite3.Data.INT (Int64.of_int e.memlimit);
           Sqlite3.Data.INT (int64_from_status e.status);
           Sqlite3.Data.FLOAT e.result_time;
           Sqlite3.Data.TEXT e.trace;
           Sqlite3.Data.INT (int64_from_bool e.proof_obsolete);
         ]
         in
	 db_must_done db (fun () -> Sqlite3.step stmt);
	 let new_id = Sqlite3.last_insert_rowid db.raw_db in
	 e.external_proof_id <- new_id)


  let set_status db e stat =
    try
      transaction db 
        (fun () ->
	   let id = e.external_proof_id in
	   let sql = 
	     "UPDATE external_proof SET status=? WHERE external_proof_id=?" 
	   in
	   let stmt = bind db sql [
             Sqlite3.Data.INT (int64_from_status stat);
             Sqlite3.Data.INT id;
           ]
           in
	   db_must_done db (fun () -> Sqlite3.step stmt))
    with e ->
      Format.eprintf "External_proof.set_status raised an exception %s@."
        (Printexc.to_string e)
      
    
  let set_result_time db e t =
      transaction db 
        (fun () ->
	   let id = e.external_proof_id in
	   let sql = 
	     "UPDATE external_proof SET result_time=? \
              WHERE external_proof_id=?" 
	   in
	   let stmt = bind db sql [
             Sqlite3.Data.FLOAT t;
             Sqlite3.Data.INT id;
           ]
           in
	   db_must_done db (fun () -> Sqlite3.step stmt))
    
  let from_id db id =
      let sql="SELECT external_proof.prover, external_proof.timelimit, \
               external_proof.memlimit, external_proof.status, \
               external_proof.result_time, external_proof.trace, \
               external_proof.obsolete FROM external_proof \
               WHERE external_proof.external_proof_id=?"
      in
      let stmt = bind db sql [Sqlite3.Data.INT id] in
      let l = step_fold db stmt 
        (fun stmt ->
           { external_proof_id = id;
	     prover = 
               stmt_column_INT stmt 0 
                 "External_Proof.from_id: bad prover id";
             timelimit = 
               stmt_column_int stmt 1
                 "External_Proof.from_id: bad timelimit";
	     memlimit = 
               stmt_column_int stmt 2
                 "External_Proof.from_id: bad memlimit";
	     status =
               status_from_int64 (stmt_column_INT stmt 3
                               "External_Proof.from_id: bad status");
	     result_time =
               stmt_column_FLOAT stmt 4
                 "External_Proof.from_id: bad result_time";
	     trace =
               stmt_column_TEXT stmt 5
                 "External_Proof.from_id: bad trace";
	     proof_obsolete =
               stmt_column_bool stmt 6
	         "External_Proof.from_id: bad proof_obsolete";
	   })
    in
    match l with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false   

    
  let from_ids db idl =
    let len = List.length idl in
    if len = 0 then [] else
      let sql = ref ")" in
      for i=1 to len-1 do sql := ",?" ^ !sql done;
      let sql="SELECT external_proof.external_proof_id,\
               external_proof.prover, external_proof.timelimit,\
               external_proof.memlimit, external_proof.status,\
               external_proof.result_time, external_proof.trace,\
               external_proof.obsolete FROM external_proof \
               WHERE external_proof.external_proof_id IN (?" ^ !sql
      in
      let stmt = Sqlite3.prepare db.raw_db sql in
      let _ =
        List.fold_left
          (fun i id ->
             db_must_ok db 
               (fun () -> Sqlite3.bind stmt i (Sqlite3.Data.INT id));
             succ i)
          1 idl
      in
      step_fold db stmt 
        (fun stmt ->
           { external_proof_id = 
	       stmt_column_INT stmt 0
                 "External_Proof.from_ids: bad external_proof_id";
	     prover = 
	       stmt_column_INT stmt 1 
                 "External_Proof.fromids: bad prover id";
             timelimit =
               stmt_column_int stmt 2
                 "External_Proof.fromids: bad timelimit";
	     memlimit =
               stmt_column_int stmt 3 
                 "External_Proof.fromids: bad memlimit";
	     status =
               status_from_int64 (stmt_column_INT stmt 4 
                                    "External_Proof.fromids: bad status");
	     result_time =
               stmt_column_FLOAT stmt 5 
                 "External_Proof.fromids: bad result_time";
	     trace =
               stmt_column_TEXT stmt 6 
                 "External_Proof.fromids: bad trace";
	     proof_obsolete =
               stmt_column_bool stmt 7
                 "External_Proof.fromids: bad proof_obsolete";
	   })
   
end
*)



(*
module Goal = struct
  
  type t = goal
      
  let hash g = Hashtbl.hash g.goal_id 

  let equal g1 g2 = g1.goal_id = g2.goal_id

  let compare g1 g2 = Pervasives.compare g1.goal_id g2.goal_id


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

  let init db =
    (* TODO: store the goal origin too *)
    let sql = 
      "CREATE TABLE IF NOT EXISTS goal \
       (goal_id INTEGER PRIMARY KEY AUTOINCREMENT,\
        task_checksum TEXT,proved INTEGER);" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    let sql = 
      "CREATE TABLE IF NOT EXISTS map_goal_prover_external_proof \
       (goal_id INTEGER, prover_id INTEGER, external_proof_id INTEGER, \
        PRIMARY KEY(goal_id, prover_id));" 
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  let add db (g : goal) = 
    transaction db 
      (fun () ->
	 assert (g.goal_id = 0L);
	 let sql = 
	   "INSERT INTO goal VALUES(NULL,?,?)" 
	 in
	 let stmt = bind db sql [
           Sqlite3.Data.TEXT g.task_checksum;
           Sqlite3.Data.INT (int64_from_bool g.proved);
         ]
         in
	 db_must_done db (fun () -> Sqlite3.step stmt);
	 let new_id = Sqlite3.last_insert_rowid db.raw_db in         
         (*
           Format.eprintf "Db.Goal.add: add a new goal with id=%Ld@." new_id;
         *)
	 g.goal_id <- new_id)


  let get_all_external_proofs db g =
    let sql="SELECT map_goal_prover_external_proof.external_proof_id \
             FROM map_goal_prover_external_proof WHERE goal_id=?" 
    in
    let stmt = bind db sql [ Sqlite3.Data.INT g.goal_id ] in
    let l =
      step_fold db stmt 
        (fun stmt -> stmt_column_INT stmt 0 "Db.get_all_external_proofs")
    in External_proof.from_ids db l

  let get_external_proof db ~prover g =
    let sql="SELECT map_goal_prover_external_proof.external_proof_id \
             FROM map_goal_prover_external_proof \
             WHERE goal_id=? AND prover_id=?" 
    in
    let stmt = bind db sql [
      Sqlite3.Data.INT g.goal_id;
      Sqlite3.Data.INT prover.prover_id
    ]
    in
    let l = step_fold db stmt 
      (fun stmt -> stmt_column_INT stmt 0 "Db.get_external_proof")
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
	   let stmt = bind db sql [
             Sqlite3.Data.INT g.goal_id;
             Sqlite3.Data.INT prover.prover_id;
             Sqlite3.Data.INT id;
           ]
           in
	   db_must_done db (fun () -> Sqlite3.step stmt)
        );
      e


  let set_proved db g b =
      transaction db 
        (fun () ->
	   let id = g.goal_id in
	   let sql = 
	     "UPDATE goal SET proved=? WHERE goal_id=?" 
	   in
	   let stmt = bind db sql [
             Sqlite3.Data.INT (int64_from_bool b);
	     Sqlite3.Data.INT id;
           ]
           in
	   db_must_done db (fun () -> Sqlite3.step stmt))
    

  let from_id _db _id : goal =
    assert false
      (*
	let sql="SELECT goal.id, goal.task_checksum, goal.parent_id, goal.name, goal.pos_id, goal.proved, goal_pos.id, goal_pos.file, goal_pos.line, goal_pos.start, goal_pos.stop, goal_parent.id, goal_parent.name, goal_parent.obsolete FROM goal LEFT JOIN transf AS goal_parent ON (goal_parent.id = goal.parent_id) LEFT JOIN loc AS goal_pos ON (goal_pos.id = goal.pos_id) " ^ q in
	let stmt=Sqlite3.prepare db.db sql in
      *)

end

*)

(*

let external_proofs g = 
  Goal.get_all_external_proofs (current ()) g

let transformations _g = assert false

*)


(*

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

*)


module Main = struct

  let init db =
    let sql = "CREATE TABLE IF NOT EXISTS files (file_name TEXT);" in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    ()

  let all_files db =
    let sql="SELECT file_name FROM files" in
    let stmt = Sqlite3.prepare db.raw_db sql in
    let of_stmt stmt = stmt_column_string stmt 0 "Db.all_files" in
    step_fold db stmt of_stmt 

  let add db name = 
    transaction db 
      (fun () ->
         let sql = "INSERT INTO files VALUES(?)" in
         let stmt = bind db sql [ Sqlite3.Data.TEXT name ] in
         db_must_done db (fun () -> Sqlite3.step stmt);
         let new_id = Sqlite3.last_insert_rowid db.raw_db in
	 new_id
(*
         { prover_id = Int64.to_int new_id ; 
	   prover_name = name }
*)
      )
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
	ProverId.init db;
(*
	Loc.init db;
	External_proof.init db;
	Goal.init db;
          Transf.init db;
	*)
	Main.init db

    | Some _ -> failwith "Db.init_db: already opened"


let init_base f = init_db ~mode:Exclusive f

(*
let root_goals () = 
  let db = current () in
  let l = Main.all_root_goals db in
  List.rev_map (Goal.from_id db) l
    
*)

let files _ = assert false



let prover_from_name n = 
  let db = current () in
  try ProverId.get db n 
  with Not_found -> ProverId.add db n

let transf_from_name _n = assert false

exception AlreadyExist 

let add_proof_attempt _ = assert false

let set_status _ = assert false

let set_obsolete _ = assert false
let set_edited_as _ = assert false
let add_transformation _ = assert false
let add_goal _ = assert false
let add_theory _ = assert false

let add_file f = Main.add (current()) f


(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/whydb.byte"
End: 
*)
