(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

let read_channel _env _path _file _c =
(*
  let ast = Coma_lexer.parse file c in
  Format.printf "@[%a@]@." (fun fmt l ->
    List.iter (fun d -> Coma_syntax.print_decl fmt d) l) ast;
*)
  Wstdlib.Mstr.empty

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel
  ~desc:"Continuation Machine language"
