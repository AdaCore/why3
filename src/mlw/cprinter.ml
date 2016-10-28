


let fg ?fname m =
  let n = m.Pmodule.mod_theory.Theory.th_name.Ident.id_string in
  match fname with
  | None -> n ^ ".c"
  | Some f -> f ^ "__" ^ n ^ ".c"

open Format

let pr args ?old fmt m =
  ignore(args);
  ignore(old);
  ignore(m);
  fprintf fmt "#include <stdio.h>\n\
\n\
int main() {\n\
  printf \"Extraction from WhyML to C not yet implemented\\n\";\n\
  return 1;\n\
}\n\
"

let () = Pdriver.register_printer "c" ~desc:"printer for C code" fg pr
