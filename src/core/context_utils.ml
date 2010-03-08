open Ident
open Theory


let cloned_from ctxt i1 i2 =
(*  Format.printf "@[<hov 2>cloned (%a = %a)?: %a@]@\n" 
    print_ident i2 print_ident i1 
    print_ctxt ctxt;*)
  try i1 == i2 || Sid.mem i2 (Mid.find i1 ctxt.ctxt_cloned)
  with Not_found -> false
