
open Format

open Set_iterators

module S = SetAppInt

let pp_set fmt s =
  S.iter
    (fun n -> Format.printf "%s " (Z.to_string n))
    s

let z = Z.of_int

let () =
  let s = S.empty in
  let s = S.add (z 42) s in
  let s = S.add (z (-17)) s in
  let s = S.add (z 26) s in
  let s = S.add (z (-1)) s in
  printf "before filter_non_neg: %a@." pp_set s;
  let s = filter_non_neg s in
  printf "after filter_non_neg: %a@." pp_set s;
  ()

module SP = SetAppPeano

let pp_setp fmt s =
  SP.iter
    (fun n -> Format.printf "%d " n)
    s

let () =
  let s = SP.empty in
  let s = SP.add 42 s in
  let s = SP.add (-17) s in
  let s = SP.add 26 s in
  let s = SP.add (-1) s in
  printf "before filter_non_neg_peano: %a@." pp_setp s;
  let s = filter_non_neg_peano s in
  printf "after filter_non_neg_peano: %a@." pp_setp s;
  ()

module S63 = SetAppInt63

let pp_set63 fmt s =
  S63.iter
    (fun n -> Format.printf "%d " n)
    s

let () =
  let s = S63.empty in
  let s = S63.add 42 s in
  let s = S63.add (-17) s in
  let s = S63.add 26 s in
  let s = S63.add (-1) s in
  printf "before filter_non_neg_int63: %a@." pp_set63 s;
  let s = filter_non_neg_int63 s in
  printf "after filter_non_neg_int63: %a@." pp_set63 s;
  ()

module St = SetAppString

let pp_sets fmt s =
  St.iter
    (fun n -> Format.printf "%s " n)
    s


let () =
  let s = St.empty in
  let s = St.add "abc" s in
  let s = St.add "de" s in
  let s = St.add "f" s in
  let s = St.add "ghij" s in
  printf "before filter_min_length 3: %a@." pp_sets s;
  let s = filter_minlength s 3 in
  printf "after filter_min_length 3: %a@." pp_sets s;
  ()
