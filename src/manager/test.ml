
open Why

let autodetection () = 
  Whyrc.add_driver_config "Alt-Ergo 0.9" "drivers/alt_ergo.drv" "alt-ergo";
  Whyrc.add_driver_config "Z3 2.2" "drivers/z3.drv" "z3";
  Whyrc.add_driver_config "CVC3 2.1" "drivers/cvc3.drv" "cvc3";
  Whyrc.add_driver_config "Coq 8.3" "drivers/coq.drv" "coqc";
  Whyrc.save ()

let () = 
  try Whyrc.read_config_file ()
  with Not_found -> 
    Format.eprintf "No whyrc file found. Running autodetection of provers.@.";
    autodetection ()



    



