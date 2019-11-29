
(* main file for ../test_extraction.mlw so that we *run* the extracted code *)

open Test

let () = assert (test_array   () = 42)

let (=) = Z.equal

let b42 = Z.of_int 42
let () = assert (test_int      () = b42)
let () = assert (test_int63    () = b42)
let () = assert (test_ref      () = b42)
let () = assert (test_array63  () = b42)
let () = assert (test_partial2    = b42)
let () = main ()

let () = Format.printf "OCaml extraction test successful@."

(*
Local Variables:
compile-command: "make -C ../.. test-ocaml-extraction"
End:
*)
