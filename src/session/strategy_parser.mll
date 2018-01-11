(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{
  open Session
  open Strategy

  exception SyntaxError of string

  let error f =
    Printf.kbprintf
      (fun b ->
        let s = Buffer.contents b in Buffer.clear b; raise (SyntaxError s))
      (Buffer.create 1024)
      f

  type label = {
    mutable defined: int option;
    temporary: int;
  }

  type 'a code = {
    env: 'a Session.env_session;
    mutable instr: instruction array;
    mutable next: int;
    labels: (string, label) Hashtbl.t; (* label name -> label *)
    mutable temp: int;
  }

  let create_code env =
    let h = Hashtbl.create 17 in
    Hashtbl.add h "exit" { defined = Some (-1); temporary = 0 };
    { env = env;
      instr = Array.make 10 (Igoto 0);
      next = 0;
      temp = 1;
      labels = h; }

  let enlarge_code code =
    let old = code.instr in
    let n = Array.length old in
    code.instr <- Array.make (2 * n) (Igoto 0);
    Array.blit old 0 code.instr 0 n

  let add_instr code i =
    let n = code.next in
    if n = Array.length code.instr then enlarge_code code;
    code.instr.(n) <- i;
    code.next <- n + 1

  let temp code =
    let t = code.temp in code.temp <- t + 1; t

  let define_label code l =
    let n = code.next in
    try
      let lab = Hashtbl.find code.labels l in
      if lab.defined = None then lab.defined <- Some n
      else error "duplicate label %s" l
    with Not_found ->
      let lab =  { defined = Some n; temporary = temp code } in
      Hashtbl.add code.labels l lab

  let find_label code l =
    try
      let lab = Hashtbl.find code.labels l in lab.temporary
    with Not_found ->
      let t = temp code in
      Hashtbl.add code.labels l { defined = None; temporary = t };
      t

  let prover code p =
    try
      let fp = Whyconf.parse_filter_prover p in
      Whyconf.filter_one_prover code.env.whyconf fp
    with
      | Whyconf.ProverNotFound _ ->
          error "Prover %S not installed or not configured" p
      | Whyconf.ProverAmbiguity _ ->
          error "Prover description %s is ambiguous" p

  let integer msg s =
    try int_of_string s
    with Failure _ -> error "unable to parse %s argument '%s'" msg s

  let transform code t =
    try
      ignore (Trans.lookup_transform t code.env.Session.env)
    with Trans.UnknownTrans _ ->
    try
      ignore (Trans.lookup_transform_l t code.env.Session.env)
    with Trans.UnknownTrans _->
      error "transformation %S is unknown" t

}

let space = [' ' '\t' '\r' '\n']
let ident = [^ ' ' '\t' '\r' '\n' ':' '#']+
let integer = ['0'-'9']+
let goto = 'g' | "goto"
let call = 'c' | "call"
let transform = 't' | "transform"

rule scan code = parse
  | space+
      { scan code lexbuf }
  | '#' [^ '\n']* ('\n' | eof)
      { scan code lexbuf }
  | ident as id ':'
      { define_label code id;
        scan code lexbuf }
  | goto space+ (ident as id)
      { add_instr code (Igoto (find_label code id));
        scan code lexbuf }
  | call space+ (ident as p) space+ (integer as t) space+ (integer as m)
      { let p = prover code p in
        let t = integer "timelimit" t in
        if t <= 0 then error "timelimit %d is invalid" t;
        let m = integer "memlimit" m in
        if m <= 0 then error "memlimit %d is invalid" m;
        add_instr code (Icall_prover (p.Whyconf.prover, t, m));
        scan code lexbuf }
  | transform space+ (ident as t) space+ (ident as l)
      { transform code t;
        add_instr code (Itransform (t, find_label code l));
        scan code lexbuf }
  | _ as c
      { let i = Lexing.lexeme_start lexbuf in
        error "syntax error on character '%c' at position %d" c i }
  | eof
      { () }

{

  let parse env s =
    let code = create_code env in
    scan code (Lexing.from_string s);
    let label = Array.make code.temp 0 in
    let fill name lab = match lab.defined with
      | None -> error "label '%s' is undefined" name
      | Some n -> label.(lab.temporary) <- n in
    Hashtbl.iter fill code.labels;
    let solve = function
      | Icall_prover _ as i -> i
      | Itransform (t, n) -> Itransform (t, label.(n))
      | Igoto n -> Igoto label.(n) in
    Array.map solve (Array.sub code.instr 0 code.next)

}
