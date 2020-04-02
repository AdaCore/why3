let why3pp_sexp mlw_file =
  Why3.Ptree.sexp_of_mlw_file mlw_file |>
  Sexplib.Sexp.output_hum_indent 2 stdout
