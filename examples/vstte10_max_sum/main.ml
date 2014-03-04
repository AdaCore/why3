
open Why3extract
open Format

let () =
  let (s,m) = Vstte10_max_sum__TestCase.test () in
  printf "sum=%s, max=%s@."
    (Why3__BigInt.to_string s) (Why3__BigInt.to_string m)
