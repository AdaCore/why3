let () =
  if not (Z.equal (Clone.main (Z.of_int 5)) (Z.of_int 42)) then
    exit 1
