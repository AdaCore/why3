open Ident
open Theory


let cloned_from ctxt i1 i2 =
  let rec aux i =
    i == i2 || (let i3 = Mid.find i1 ctxt.ctxt_cloned in
                aux i3)
  in
  try
    aux i1
  with Not_found -> false
