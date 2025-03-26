
open Set_iterators

module S = SetAppInt

open Format

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
