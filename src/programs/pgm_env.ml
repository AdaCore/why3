
open Why
open Pgm_module

type t = {
  env      : Env.env;
  retrieve : retrieve_module;
  memo     : (string list, Pgm_module.t Mnm.t) Hashtbl.t;
}

and retrieve_module = t -> string -> in_channel -> Pgm_module.t Mnm.t

let get_env penv = penv.env

let create env retrieve = {
  env = env;
  retrieve = retrieve;
  memo = Hashtbl.create 17;
}

exception ModuleNotFound of string list * string

let rec add_suffix = function
  | [] -> assert false
  | [f] -> [f ^ ".mlw"]
  | p :: f -> p :: add_suffix f

let find_library penv sl =
  try Hashtbl.find penv.memo sl
  with Not_found ->
    Hashtbl.add penv.memo sl Mnm.empty;
    let file, c = Env.find_channel penv.env (add_suffix sl) in
    let m = penv.retrieve penv file c in
    close_in c;
    Hashtbl.replace penv.memo sl m;
    m

let find_module penv sl s =
  try Mnm.find s (find_library penv sl)
  with Not_found -> raise (ModuleNotFound (sl, s))
