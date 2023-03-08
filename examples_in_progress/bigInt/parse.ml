
open BigInt__N

exception SyntaxError

let times10 a =
  let a2 = add a a in
  let a4 = add a2 a2 in
  let a5 = add a4 a in
  add a5 a5

let parse_dec s idx =
  let a = ref (from_small_int 0) in
  let i = ref idx in
  try
  while !i < String.length s do
    match String.get s !i with
      | '0'..'9' as c ->
        let d = Char.code c - Char.code '0' in
        a := add (times10 !a) (from_small_int d);
        i := succ !i
      | _ ->
        raise Exit
  done;
  raise Exit
  with Exit ->
    if !i = idx then raise SyntaxError else !a,!i

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

open Format

let pr fmt a =
  let a = a.digits in
  let l = Array.length a in
  fprintf fmt "%d" a.(l-1);
  for i=l-2 downto 0 do
    fprintf fmt "%04d" a.(i);
  done

