open Ident
open Theory


let cloned_from ctxt i1 i2 =
(*  Format.printf "@[<hov 2>cloned (%a = %a)?: %a@]@\n" 
    print_ident i2 print_ident i1 
    print_ctxt ctxt;*)
  let rec aux i =
    i == i1 ||   
      try 
        let i3 = Mid.find i ctxt.ctxt_cloned in
        List.exists aux i3
      with Not_found -> false
  in
  aux i2
