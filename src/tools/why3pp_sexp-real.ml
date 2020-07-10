open Format
open Sexplib.Sexp

(* Check if a string contains only characters [a-zA-Z0-9_-] *)
let is_simple_token s =
  let rec loop i =
    if i < 0 then
      true
    else match s.[i] with
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' ->
          loop (i-1)
      | _ -> false in
  loop (String.length s-1)

let rec output fmt = function
  | Atom s ->
      if is_simple_token s then
        fprintf fmt "%s" s
      else
        fprintf fmt "%S" s
  | List l ->
      let pp_sep fmt () = fprintf fmt "@ " in
      fprintf fmt "@[<hv2>(%a)@]" (pp_print_list ~pp_sep output) l

let why3pp_sexp out mlw_file =
  let sexp = Why3.Ptree.sexp_of_mlw_file mlw_file in
  output (Format.formatter_of_out_channel out) sexp
  (* Functions [Sexplib.Sexp.output*] do not escape brackets and quotes in tokens *)
