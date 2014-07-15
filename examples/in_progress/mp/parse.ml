
open Mp__N

let n__add = Mp__N.add
let n__zero = Mp__N.zero
let n__from_limb = Mp__N.from_limb


open Format

let pr fmt a =
  let a = a.digits in
  let l = Array.length a in
  for i=l-1 downto 0 do
    fprintf fmt "|%08LX" a.(i);
  done;
  fprintf fmt "|"

exception SyntaxError

(*
let times10 a =
  let a2 = n__add a a in
  let a4 = n__add a2 a2 in
  let a5 = n__add a4 a in
  n__add a5 a5

let parse_dec s idx =
  let a = ref (n__zero ()) in
  let i = ref idx in
  try
  while !i < String.length s do
    match String.get s !i with
      | '0'..'9' as c ->
        let d = Int64.of_int (Char.code c - Char.code '0') in
        a := n__add (times10 !a) (n__from_limb d);
        i := succ !i
      | _ ->
        raise Exit
  done;
  raise Exit
  with Exit ->
    if !i = idx then raise SyntaxError else !a,!i
*)

let times10_ip a =
  let b = copy a in
  add_in_place a a; (* times 2 *)
  add_in_place a a; (* times 4 *)
  add_in_place a b; (* times 5 *)
  add_in_place a a  (* times 10 *)

let parse_dec_ip s idx =
  let a = n__zero () in
  let i = ref idx in
  try
  while !i < String.length s do
    match String.get s !i with
      | '0'..'9' as c ->
        let d = Int64.of_int (Char.code c - Char.code '0') in
        eprintf "parse_dec_ip: a = %a@." pr a;
        times10_ip a;
        eprintf "parse_dec_ip: 10a = %a, d=%Ld@." pr a d;
        add_in_place a (n__from_limb d);
        eprintf "parse_dec_ip: a = %a@." pr a;
        i := succ !i
      | _ ->
        raise Exit
  done;
  raise Exit
  with Exit ->
    if !i = idx then raise SyntaxError else a,!i

let parse_sep_star s idx =
  let i = ref idx in
  try
  while !i < String.length s do
    match String.get s !i with
      | ' ' | '\t' | '\n' | '\r' -> i := succ !i
      | _ -> raise Exit
  done;
  raise Exit
  with Exit -> !i


