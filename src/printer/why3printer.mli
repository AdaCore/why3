

(*
   TODO not implemented yet as forgetting functions.
   TODO only vars implemented as forgetting. We assume it is
   not necessary for others.

   When printing for errors reporting, we can have to print things that
   are not already in the task. So, printing those things will change
   the printer.
   Lets say that "tac" is a transformation that fails on "task" and that
   the error message is about a new variable "n". Then if you call "tac"
   several times on the same "task" (which is possible), you will get
   error messages with "n1" then "n2" then "n3" then...

   So we have these functions that should print elements inside term/variable...
   And they should forget the new printed things they just created.
   So the function printing all these should then forget all the ids that were
   recorded after it has printed everything.

*)

val print_ls   : Task.name_tables -> Format.formatter -> Term.lsymbol  -> unit
val print_tv   : Task.name_tables -> Format.formatter -> Ty.tvsymbol   -> unit
val print_ts   : Task.name_tables -> Format.formatter -> Ty.tysymbol   -> unit
val print_forget_vsty : Task.name_tables -> Format.formatter -> Term.vsymbol  -> unit
val print_pr   : Task.name_tables -> Format.formatter -> Decl.prsymbol -> unit
val print_pat  : Task.name_tables -> Format.formatter -> Term.pattern  -> unit
val print_ty   : Task.name_tables -> Format.formatter -> Ty.ty         -> unit
val print_term : Task.name_tables -> Format.formatter -> Term.term     -> unit
val print_decl : Task.name_tables -> Format.formatter -> Decl.decl     -> unit
