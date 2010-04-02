#load "printer_utils.cmo"
#load "sql_orm_header.cmo"
#load "sql_orm.cmo"

open Sql_orm

open Schema

let boolean = integer

let all_tables = make 
  [
    (* table of locs *)
    ("loc",
     [ text "file";
       integer "line";
       integer "start";
       integer "stop";
     ],
     [], default_opts);

    (* external proofs *)
    ("external_proof",
     [ text "prover"; (* prover identifier *)
       integer "timelimit"; (* CPU limit given in seconds *)
       integer "memlimit"; (* VM limit given in megabytes *)
       integer "status"; (* enum{proof_attempt_status}; the current state *)
       real "result_time"; (* CPU time for that run in seconds *)
       text "trace"; (* any kind of trace returned by an automatic prover,
			or any kind of proof script for an interactive prover *)
       boolean "obsolete";
     ],
     [], default_opts);

    (* goal *)
    ("goal",
     [ text "task_checksum";
       foreign "transf" "parent"; (* parent transf if any *)
       text "name"; (* qualified proposition name *)
       foreign "loc" "pos"; 
       foreign_many "external_proof" "external_proofs";
       foreign_many "transf" "transformations";
       boolean "proved";
     ],
     [], default_opts);

    (* transformations *)
    ("transf",
     [ text "name"; (* transformation name *)
       boolean "obsolete";
       foreign_many "goal" "subgoals";
     ],
     [], default_opts);
    
  ]       

let () = generate ~debug:false all_tables "src/manager/db"

