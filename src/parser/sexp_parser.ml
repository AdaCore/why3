

let read_channel env path file c =
  let sexp = Sexplib.Sexp.input_sexp c in
  let ptree = Ptree.mlw_file_of_sexp sexp in
  Typing.type_mlw_file env path file ptree

  let sexp_format = "sexp"

  let () = Env.register_format Pmodule.mlw_language sexp_format ["sexp"]
      read_channel ~desc:"WhyML@ code in s-expressions format"
