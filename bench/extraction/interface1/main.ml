open Interface1

let () =
  let (b1, b2) = main () in
  assert (b1 = true && b2 = false)
