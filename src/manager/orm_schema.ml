#load "printer_utils.cmo"
#load "sql_orm_header.cmo"
#load "sql_orm.cmo"

open Sql_orm

open Schema

let boolean = integer

let all_tables = make 
  [
    (* table of challenges *)
    ("challenge",
     [ integer "log"; (* ref to log it belongs to *)
       text "input"; (* input of the problem *)
       text ~flags:[`Optional] "answer";
       (* no answer means "timeout" *)
       real "time"; (* time to answer *)
       boolean "correct"; 
     ],
     [], default_opts);

    (* log entries *)
    ("log_entry",
     [ integer "attempt"; (* ref to attempt it belongs to *)
       boolean "successful";
       date "starting_date";
       date "end_date";
       foreign_many "challenge" "challenges";
     ],
     [], default_opts);

    (* table of attempts *)
    ("attempts",
     [ integer "solution"; (* ref to solution it belongs to *)
       foreign_many "log_entry" "log_entries";
     ],
     [], default_opts);
       
    (* table of submitted solutions, successful or not *)
    ("solution",
     [ text "user";
       integer "problem_id";
       boolean "solved";
       foreign_many "attempts" "attempts"; (* list of attempts *)
     ],
     [], default_opts);

    (* table of problems *)
    ("problems",
     [ integer ~flags:[`Unique; `Index] "number";
       text "short_descr";
       text "description";
       integer "solved_by" ;
     ],
     [],
     default_opts);
    
    
    (* table of user profiles *)
    ("user" ,
     [ text ~flags:[`Unique ; `Index] "username";
       text "password";       
       text "email";
       boolean "allow_contact"; (* if allows to make email public *)
       text ~flags:[`Optional; `Index] "nationality";
       text ~flags:[`Optional; `Index] "preferred_language";
       integer "score";
       foreign_many "solution" "solutions"; (* list of submitted solutions *)
     ],
     [], default_opts) ;
    


  ]       

let () = generate ~debug:false all_tables "src/manager/db"

