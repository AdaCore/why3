type simple_loc  = { file : string; line : int ; col : int }
type loc = simple_loc list

let mk_simple_loc fn l c =
   { file = fn; line = l; col = c }
let mk_loc fn l c =
   [mk_simple_loc fn l c]

let mk_loc_line fn l = mk_loc fn l 0

let equal_line l1 l2 =
   let l1 = List.hd l1 and l2 = List.hd l2 in
   l1.line = l2.line && l1.file = l2.file

let orig_loc l =
   (* the original source is always the last source location *)
   List.hd l

let simple_print_loc fmt l =
   Format.fprintf fmt "%s:%d:%d" l.file l.line l.col

let print_line_loc fmt l =
   Format.fprintf fmt "%s:%d" l.file l.line

let print_loc _ _ =
   assert false

let parse_loc =
   let rec parse_loc_list acc l =
      match l with
      | file::line::col::rest ->
            let new_loc =
               mk_simple_loc file (int_of_string line) (int_of_string col) in
            parse_loc_list (new_loc :: acc) rest
      | [] -> acc
      | _ -> Gnat_util.abort_with_message "location list malformed."
   in
   fun l -> List.rev (parse_loc_list [] l)

let get_file l = l.file
let get_line l = l.line
let get_col l = l.col
