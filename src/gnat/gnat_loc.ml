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
   { rfile : string; first_line : int; last_line : int }

let mk_simple_loc fn l c ctx =
   { file = fn; line = l; col = c; ctxt = ctx }
let mk_loc fn l c ctx =
   [mk_simple_loc fn l c ctx]
let mk_region fn f l =
   { rfile = fn; first_line = f; last_line = l }

let mk_loc_line fn l = mk_loc fn l 0 None

let equal_line l1 l2 =
   let l1 = List.hd l1 and l2 = List.hd l2 in
   l1.line = l2.line && l1.file = l2.file

let equal_orig_loc l1 l2 =
  let l1 = List.hd l1 and l2 = List.hd l2 in
  l1.file = l2.file && l1.line = l2.line && l1.col = l2.col

let in_region r l =
  let l = List.hd l in
  l.file = r.rfile && r.first_line <= l.line && l.line <= r.last_line

let compare_simple = Pervasives.compare

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

let simple_print_loc fmt l =
   Format.fprintf fmt "%s:%d:%d" l.file l.line l.col

let print_line_loc fmt l =
   Format.fprintf fmt "%a%s:%d" print_context l.ctxt l.file l.line

let print_loc _ _ =
   assert false

let print_region fmt l =
   Format.fprintf fmt "%s:%d:%d" l.rfile l.first_line l.last_line

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

let get_file l = l.file
let get_line l = l.line
let get_col l = l.col
let explode l = l.file, l.line, l.col

module S = Extset.Make (struct type t = loc let compare = compare end)
