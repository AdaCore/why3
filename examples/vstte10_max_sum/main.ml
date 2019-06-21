
open Format

let () =
  let (s,m) = Vstte10_max_sum.test () in
  printf "sum=%s, max=%s@."
    (Z.to_string s) (Z.to_string m)
