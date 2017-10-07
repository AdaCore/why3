open Why3

let read_channel env path file c =
  assert false;
  Env.read_file Pmodule.mlw_language env file

let () =
  Env.register_format Pmodule.mlw_language "why3 AI" ["imlw"] read_channel
    ~desc:"mlw with abstract interpretation"

