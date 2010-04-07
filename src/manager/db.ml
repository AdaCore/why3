
open Sqlite3
open Printf
  
type transaction_mode = | Deferred | Immediate | Exclusive
  
type state = {
  db : db;
  mutable in_transaction: int;
  busyfn: db -> unit;
  mode: transaction_mode;
}
  
let default_busyfn (db:Sqlite3.db) =
  print_endline "WARNING: busy";
  Thread.delay (Random.float 1.)
  
let raise_sql_error x = raise (Sqlite3.Error (Rc.to_string x))
  
let try_finally fn finalfn =
  try
    let r = fn () in
    finalfn ();
    r
  with e -> begin
    print_endline (sprintf "WARNING: exception: %s" (Printexc.to_string e));
    finalfn ();
    raise e
  end
    
(* retry until a non-BUSY error code is returned *)
let rec db_busy_retry db fn =
  match fn () with
    | Rc.BUSY -> db.busyfn db.db; db_busy_retry db fn
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
         begin
           db_must_ok db 
             (fun () -> exec db.db (sprintf "BEGIN %s TRANSACTION" m))
         end;
       db.in_transaction <- db.in_transaction + 1;
       fn ();
    ) 
    (fun () ->
       if db.in_transaction = 1 then 
         begin
           db_must_ok db (fun () -> exec db.db "END TRANSACTION")
         end;
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


module Loc = struct

  type t = {
    mutable id : int64 option;
    mutable file : string;
    mutable line : int64;
    mutable start : int64;
    mutable stop : int64;
  }

  let init db =
    let sql = "create table if not exists loc (id integer primary key autoincrement,file text,line integer,start integer,stop integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    ()

  (* object definition *)
  let t ?id ~file ~line ~start ~stop db : t = 
    { 
      id = id;
      file = file;
      line = line;
      start = start;
      stop = stop;
    }

  (* admin functions *)
  let delete db loc =
    match loc.id with
      | None -> ()
      | Some id ->
          let sql = "DELETE FROM loc WHERE id=?" in
          let stmt = Sqlite3.prepare db.db sql in
          db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
          ignore (step_fold db stmt (fun _ -> ()));
          loc.id <- None

  let save db loc = 
    transaction db 
      (fun () ->
         (* insert any foreign-one fields into their table and get id *)
         let curobj_id = match loc.id with
           | None -> 
               (* insert new record *)
               let sql = "INSERT INTO loc VALUES(NULL,?,?,?,?)" in
               let stmt = Sqlite3.prepare db.db sql in
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 1 
                    (let v = loc.file in Sqlite3.Data.TEXT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 2 
                    (let v = loc.line in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 3 
                    (let v = loc.start in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 4 
                    (let v = loc.stop in Sqlite3.Data.INT v));
               db_must_done db (fun () -> Sqlite3.step stmt);
               let new_id = Sqlite3.last_insert_rowid db.db in
               loc.id <- Some new_id;
               new_id
           | Some id -> 
               (* update *)
               let sql = 
                 "UPDATE loc SET file=?,line=?,start=?,stop=? WHERE id=?" 
               in
               let stmt = Sqlite3.prepare db.db sql in
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 1 
                    (let v = loc.file in Sqlite3.Data.TEXT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 2 
                    (let v = loc.line in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 3 
                    (let v = loc.start in Sqlite3.Data.INT v));
               db_must_ok db 
                 (fun () -> Sqlite3.bind stmt 4 
                    (let v = loc.stop in Sqlite3.Data.INT v));
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
      | None -> q | Some b -> q ^ (f()) ^ "loc.id=?" in
    let q = match file with 
      | None -> q | Some b -> q ^ (f()) ^ "loc.file=?" in
    let q = match line with 
      | None -> q | Some b -> q ^ (f()) ^ "loc.line=?" in
    let q = match start with 
      | None -> q | Some b -> q ^ (f()) ^ "loc.start=?" in
    let q = match stop with 
      | None -> q | Some b -> q ^ (f()) ^ "loc.stop=?" in
    let q = match custom_where with 
      | "",_ -> q | w,_ -> q ^ (f()) ^ "(" ^ w ^ ")" in
    let sql =
      "SELECT loc.id, loc.file, loc.line, loc.start, loc.stop FROM loc " ^ q 
    in
    let stmt=Sqlite3.prepare db.db sql in
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
    t
      (* native fields *)
      ?id:(
      (match Sqlite3.column stmt 0 with
        |Sqlite3.Data.NULL -> None
        |x -> Some (match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: loc id")))
      )
      ~file:(
      (match Sqlite3.column stmt 1 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> Sqlite3.Data.to_string x)
      )
      ~line:(
      (match Sqlite3.column stmt 2 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: loc line"))
      )
      ~start:(
      (match Sqlite3.column stmt 3 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: loc start"))
      )
      ~stop:(
      (match Sqlite3.column stmt 4 with
        |Sqlite3.Data.NULL -> failwith "null of_stmt"
        |x -> match x with |Sqlite3.Data.INT i -> i |x -> (try Int64.of_string (Sqlite3.Data.to_string x) with _ -> failwith "error: loc stop"))
      )
      (* foreign fields *)
    db
    in 
    (* execute the SQL query *)
    step_fold db stmt of_stmt

end

(*
module External_proof = struct
  type t = <
    id : int64 option;
    set_id : int64 option -> unit;
    prover : string;
    set_prover : string -> unit;
    timelimit : int64;
    set_timelimit : int64 -> unit;
    memlimit : int64;
    set_memlimit : int64 -> unit;
    status : int64;
    set_status : int64 -> unit;
    result_time : float;
    set_result_time : float -> unit;
    trace : string;
    set_trace : string -> unit;
    obsolete : int64;
    set_obsolete : int64 -> unit;
    save: int64; delete: unit
  >

  let init db =
    let sql = "create table if not exists external_proof (id integer primary key autoincrement,prover text,timelimit integer,memlimit integer,status integer,result_time real,trace text,obsolete integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    ()

  (* object definition *)
  let t ?(id=None) ~prover ~timelimit ~memlimit ~status ~result_time ~trace ~obsolete db : t = object
    (* get functions *)
    val mutable _id = id
    method id : int64 option = _id
    val mutable _prover = prover
    method prover : string = _prover
    val mutable _timelimit = timelimit
    method timelimit : int64 = _timelimit
    val mutable _memlimit = memlimit
    method memlimit : int64 = _memlimit
    val mutable _status = status
    method status : int64 = _status
    val mutable _result_time = result_time
    method result_time : float = _result_time
    val mutable _trace = trace
    method trace : string = _trace
    val mutable _obsolete = obsolete
    method obsolete : int64 = _obsolete

    (* set functions *)
    method set_id v =
      _id <- v
    method set_prover v =
      _prover <- v
    method set_timelimit v =
      _timelimit <- v
    method set_memlimit v =
      _memlimit <- v
    method set_status v =
      _status <- v
    method set_result_time v =
      _result_time <- v
    method set_trace v =
      _trace <- v
    method set_obsolete v =
      _obsolete <- v

    (* admin functions *)
    method delete =
      match _id with
      |None -> ()
      |Some id ->
        let sql = "DELETE FROM external_proof WHERE id=?" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
        ignore(step_fold db stmt (fun _ -> ()));
        _id <- None

    method save = transaction db (fun () ->
      (* insert any foreign-one fields into their table and get id *)
      let _curobj_id = match _id with
      |None -> (* insert new record *)
        let sql = "INSERT INTO external_proof VALUES(NULL,?,?,?,?,?,?,?)" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (let v = _prover in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (let v = _timelimit in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 3 (let v = _memlimit in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 4 (let v = _status in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 5 (let v = _result_time in Sqlite3.Data.FLOAT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 6 (let v = _trace in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 7 (let v = _obsolete in Sqlite3.Data.INT v));
        db_must_done db (fun () -> Sqlite3.step stmt);
        let __id = Sqlite3.last_insert_rowid db.db in
        _id <- Some __id;
        __id
      |Some id -> (* update *)
        let sql = "UPDATE external_proof SET prover=?,timelimit=?,memlimit=?,status=?,result_time=?,trace=?,obsolete=? WHERE id=?" in
        let stmt = Sqlite3.prepare db.db sql in
        db_must_ok db (fun () -> Sqlite3.bind stmt 1 (let v = _prover in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 2 (let v = _timelimit in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 3 (let v = _memlimit in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 4 (let v = _status in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 5 (let v = _result_time in Sqlite3.Data.FLOAT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 6 (let v = _trace in Sqlite3.Data.TEXT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 7 (let v = _obsolete in Sqlite3.Data.INT v));
        db_must_ok db (fun () -> Sqlite3.bind stmt 8 (Sqlite3.Data.INT id));
        db_must_done db (fun () -> Sqlite3.step stmt);
        id
      in
      _curobj_id
    )
  end

  (* General get function for any of the columns *)
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

end

module Goal = struct
  type t = <
    id : int64 option;
    set_id : int64 option -> unit;
    task_checksum : string;
    set_task_checksum : string -> unit;
    parent : Transf.t;
    set_parent : Transf.t -> unit;
    name : string;
    set_name : string -> unit;
    pos : Loc.t;
    set_pos : Loc.t -> unit;
    external_proofs : External_proof.t list;
    set_external_proofs : External_proof.t list -> unit;
    transformations : Transf.t list;
    set_transformations : Transf.t list -> unit;
    proved : int64;
    set_proved : int64 -> unit;
    save: int64; delete: unit
  >

  let init db =
    let sql = "create table if not exists goal (id integer primary key autoincrement,task_checksum text,parent_id integer,name text,pos_id integer,proved integer);" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_external_proofs_goal_external_proof (goal_id integer, external_proof_id integer, primary key(goal_id, external_proof_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_transformations_goal_transf (goal_id integer, transf_id integer, primary key(goal_id, transf_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    ()

  (* object definition *)
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

  (* General get function for any of the columns *)
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

end

module Transf = struct
  type t = <
    id : int64 option;
    set_id : int64 option -> unit;
    name : string;
    set_name : string -> unit;
    obsolete : int64;
    set_obsolete : int64 -> unit;
    subgoals : Goal.t list;
    set_subgoals : Goal.t list -> unit;
    save: int64; delete: unit
  >

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

end

*)


type handle = state

let create ?(busyfn=default_busyfn) ?(mode=Immediate) db_name =
  let db = {
    db = Sqlite3.db_open db_name; 
    in_transaction = 0; 
    mode = mode; 
    busyfn = busyfn } 
  in
  Loc.init db;
  (*
    External_proof.init db;
    Goal.init db;
    Transf.init db;
  *)
  db

let raw db = db.db

