
(* main file for ../test_extraction.mlw so that we *run* the extracted code *)

let (=) = Z.eq

let b42 = Z.of_int 42
let () = assert (test_int    () = b42)
let () = assert (test_int32  () = b42)
let () = assert (test_uint32 () = b42)
let () = assert (test_int63  () = b42)
let () = assert (test_int64  () = b42)
let () = assert (test_uint64 () = b42)

let () = assert (test_ref     () = b42)
let () = assert (test_array   () = b42)
let () = assert (test_array31 () = b42)

let () = Format.printf "  OCaml extraction test successful@."

(*
Local Variables:
compile-command: "make -C ../.. test-ocaml-extraction"
End:
*)
