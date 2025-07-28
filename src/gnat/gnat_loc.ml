open Why3

type context = Inlined | Instantiated

let context_of_string = function
    "inlined" -> Inlined
  | "instantiated" -> Instantiated
  | _ -> failwith "context_of_string"

(* This wording for messages related to instantiations and inlined calls is the
   same for flow and proof messages. If you change it here, also change it in
   flow_error_messages.adb *)
let print_context fmt = function
    None -> ()
  | Some Inlined -> Format.fprintf fmt ", in call inlined at "
  | Some Instantiated -> Format.fprintf fmt ", in instantiation at "

type simple_loc  =
   { file : string; line : int; col : int; ctxt : context option }
type loc = simple_loc list
type region =
  { context: loc; rfile : string; first_line : int; last_line : int }

let mk_simple_loc fn l c ctx =
   { file = fn; line = l; col = c; ctxt = ctx }
let mk_loc fn l c ctx =
   [mk_simple_loc fn l c ctx]
let mk_region loc fn f l =
  { context = loc; rfile = fn; first_line = f; last_line = l }

let mk_loc_line fn l = mk_loc fn l 0 None

let simple_print_loc fmt l =
   Format.fprintf fmt "%s:%d:%d" l.file l.line l.col

let print_loc fmt l =
  let colon fmt () = Format.fprintf fmt ":" in
  Pp.print_list_delim ~start:Pp.nothing ~stop:Pp.nothing ~sep:colon simple_print_loc fmt l

let print_line_loc fmt l =
   Format.fprintf fmt "%a%s:%d" print_context l.ctxt l.file l.line

let print_region fmt l =
   Format.fprintf fmt "%a%s:%d:%d" print_loc l.context l.rfile l.first_line l.last_line

let rec equal_line l1 l2 =
  match l1, l2 with
  | hd1::rest1, hd2::rest2 ->
      hd1.line = hd2.line && hd1.file = hd2.file && equal_line rest1 rest2
  (* reaching the end means a match, partial matches are also OK *)
  | _, _ -> true

let in_region r l =
  match l with
  | [] -> raise (Invalid_argument "empty loc")
  | hd :: rest ->
      equal_line r.context rest &&
      hd.file = r.rfile && r.first_line <= hd.line && hd.line <= r.last_line

let equal_loc l1 l2 =
  match l1, l2 with
  | hd1::rest1, hd2::rest2 ->
    hd1.file = hd2.file && hd1.line = hd2.line && hd1.col = hd2.col && equal_line rest1 rest2
  | _, _ -> true

let compare_simple = Stdlib.compare

let rec compare_loc a b =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x::xs, y::ys ->
      let c = compare_simple x y in
      if c = 0 then compare_loc xs ys else c

let orig_loc l =
   (* the original source is always the last source location *)
   List.hd l

let parse_loc =
   let rec parse_loc_list acc ~first l =
      match l with
      | file::line::col::rest when first ->
            let new_loc =
               mk_simple_loc file (int_of_string line) (int_of_string col)
                 None
            in
            parse_loc_list (new_loc :: acc) ~first:false rest
      | ctx::file::line::col::rest when not first ->
            let new_loc =
               mk_simple_loc file (int_of_string line) (int_of_string col)
                 (Some (context_of_string ctx))
            in
            parse_loc_list (new_loc :: acc) ~first:false rest
      | [] -> acc
      | _ ->
        raise (Failure "incorrect format")
   in
   fun l ->
   try
     List.rev (parse_loc_list [] ~first:true l)
   with e when Debug.test_flag Debug.stack_trace -> raise e
   | Failure s ->
          Gnat_util.abort_with_message ~internal:true
            ("failure when parsing location list: " ^ s)

let parse_loc_line_only =
   let rec parse_loc_list acc l =
      match l with
      | file::line::rest ->
            let new_loc = mk_simple_loc file (int_of_string line) 0 None in
            parse_loc_list (new_loc :: acc) rest
      | [] -> acc
      | _ ->
        raise (Failure "incorrect format")
   in
   fun l ->
   try
     List.rev (parse_loc_list [] l)
   with e when Debug.test_flag Debug.stack_trace -> raise e
   | Failure s ->
          Gnat_util.abort_with_message ~internal:true
            ("failure when parsing location list: " ^ s)

let get_file l = l.file
let get_line l = l.line
let get_col l = l.col
let explode l = l.file, l.line, l.col

let set_col l c =
  match List.rev l with
  | hd::rest -> List.rev ({ hd with col = c} :: rest)
  | _ -> raise (Invalid_argument "empty location not supported")

module S = Extset.Make (struct type t = loc let compare = compare end)
