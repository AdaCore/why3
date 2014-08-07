open Why3

let string fmt s = Format.fprintf fmt "\"%s\"" s
let int fmt d = Format.fprintf fmt "%d" d
let bool fmt b = Format.fprintf fmt "%b" b

let print_json_field key value_pr fmt value =
  Format.fprintf fmt "%a : %a " string key value_pr value

let list pr fmt l =
  if l = [] then Format.fprintf fmt "[]"
  else
    Pp.print_list_delim ~start:Pp.lsquare ~stop:Pp.rsquare ~sep:Pp.comma
    pr fmt l
