

exception Parse_error of string

let () = Exn_printer.register (fun fmt exn -> match exn with
  | Parse_error msg -> Format.fprintf fmt "Sexp parser syntax error: %s" msg
  | _ -> raise exn)

let read_channel env path file c =
  let sexp = Sexplib.Sexp.input_sexp c in
  try
    let ptree = Ptree.mlw_file_of_sexp sexp in
    Typing.type_mlw_file env path file ptree
  with Sexplib.Conv.Of_sexp_error(e,_) ->
    let loc = Loc.user_position (String.concat Filename.dir_sep (path@[file])) 0 0 0 0 in
    match e with
    | Failure msg ->
        raise (Loc.Located(loc,Parse_error msg))
    | _ ->
        raise (Loc.Located(loc,e))

let sexp_format = "sexp"

let () = Env.register_format Pmodule.mlw_language sexp_format ["sexp"]
    read_channel ~desc:"WhyML@ code in s-expressions format"
