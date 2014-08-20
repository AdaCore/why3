open Why3

let string fmt s =
  let b = Buffer.create (2 * String.length s) in
  Buffer.add_char b '"';
  for i = 0 to String.length s -1 do
    match s.[i] with
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | c -> Buffer.add_char b c
  done;
  Buffer.add_char b '"';
  Format.fprintf fmt "%s" (Buffer.contents b)

let int fmt d = Format.fprintf fmt "%d" d
let bool fmt b = Format.fprintf fmt "%b" b

let print_json_field key value_pr fmt value =
  Format.fprintf fmt "%a : %a " string key value_pr value

let list pr fmt l =
  if l = [] then Format.fprintf fmt "[]"
  else
    Pp.print_list_delim ~start:Pp.lsquare ~stop:Pp.rsquare ~sep:Pp.comma
    pr fmt l
