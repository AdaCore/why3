
open Format

open Map_iterators

module M = MapAppInt

let pp_map fmt m =
  M.iter
    (fun k n -> Format.printf "%s -> %s " (Z.to_string k) (Z.to_string n))
    m

let z = Z.of_int

let () =
  let m = M.empty in
  let m = M.add (z 42) (z 1) m in
  let m = M.add (z (-17)) (z 3) m in
  let m = M.add (z 26) (z (-5)) m in
  let m = M.add (z (-1)) (z (-9)) m in
  printf "before incr: %a@." pp_map m;
  let m = incr m in
  printf "after incr: %a@." pp_map m;
  ()

module MP = MapAppPeano

let pp_map fmt m =
  MP.iter
    (fun k n -> Format.printf "%d -> %s " k (Z.to_string n))
    m

let () =
  let m = MP.empty in
  let m = MP.add 42 (z 1) m in
  let m = MP.add (-17) (z 3) m in
  let m = MP.add 26 (z (-5)) m in
  let m = MP.add (-1) (z (-9)) m in
  printf "before incr: %a@." pp_map m;
  let m = incr_peano m in
  printf "after incr: %a@." pp_map m;
  ()

module M63 = MapAppInt63

let pp_map fmt m =
  M63.iter
    (fun k n -> Format.printf "%d -> %s " k (Z.to_string n))
    m

let () =
  let m = M63.empty in
  let m = M63.add 42 (z 1) m in
  let m = M63.add (-17) (z 3) m in
  let m = M63.add 26 (z (-5)) m in
  let m = M63.add (-1) (z (-9)) m in
  printf "before incr: %a@." pp_map m;
  let m = incr63 m in
  printf "after incr: %a@." pp_map m;
  ()

module MS = MapAppString

let pp_map fmt m =
  MS.iter
    (fun k n -> Format.printf "%s -> %s " k (Z.to_string n))
    m

let () =
  let m = MS.empty in
  let m = MS.add "aa" (z 1) m in
  let m = MS.add "b" (z 3) m in
  let m = MS.add "ccc" (z (-5)) m in
  let m = MS.add "de" (z (-9)) m in
  printf "before incr: %a@." pp_map m;
  let m = incr_str m in
  printf "after incr: %a@." pp_map m;
  ()
