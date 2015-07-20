
let n = Why3extract.Why3__BigInt.of_int

let () =
  Format.eprintf "Running the test (zenon10 2)@.";
  ProverMain__Impl.main (ProverTest__Impl.zenon10 (n 2)) (n 1);
  Format.eprintf "Done (which means 'unsat')@."
