(*
   This file is completely copied from Compcert's preparser. Reference manual of
   menhir takes this as example.
 *)

 open Parser.MenhirInterpreter

 (* -------------------------------------------------------------------------- *)

 (* There are places where we may hit an internal error and we would like to fail
    abruptly because "this cannot happen". Yet, it is safer when shipping to
    silently cover up for our internal error. Thus, we typically use an idiom of
    the form [if debug then assert false else <some default value>]. *)

 let debug = false

 (* -------------------------------------------------------------------------- *)

 (* [env checkpoint] extracts the parser's environment out of a checkpoint. *)

 let env checkpoint =
   match checkpoint with
   | HandlingError env ->
       env
   | _ ->
       assert false (* this cannot happen, I promise *)

 (* -------------------------------------------------------------------------- *)

 (* [state checkpoint] extracts the number of the current state out of a
    parser checkpoint. *)

 let state checkpoint : int =
   match top (env checkpoint) with
   | None ->
       (* Hmm... The parser is in its initial state. Its number is
          usually 0. This is a BIG HACK. TEMPORARY *)
       0
   | Some Element (s, _, _, _) ->
       number s

 (* -------------------------------------------------------------------------- *)

 (* We allow an error message to contain the special form $i. We only use it to
    print what was read. *)

 let fragment text message =
   try
     let i = int_of_string (Str.matched_group 1 message) in
     match i with
     | 0 -> text
     | _ -> text
   with
   | Failure _ ->
       (* In principle, this should not happen, but if it does, let's cover up
          for our internal error. *)
       if debug then assert false else "???"
   | Not_found ->
       (* In principle, this should not happen, but if it does, let's cover up
          for our internal error. *)
       if debug then assert false else "???"


 let fragments text (message : string) : string =
   Str.global_substitute
     (Str.regexp "\\$\\([0-9]+\\)")
     (fragment text)
     message

exception Found of string

let message_from_token token =
  match token with
  | Parser.MODULE ->
      raise (Found "Trying to open a module inside a module")
  | _ -> ()

let message_from_state_id text checkpoint =
  (* Find out in which state the parser failed. *)
  let s : int = state checkpoint in
  (* Choose an error message, based on the state number [s].
     Then, customize it, based on dynamic information. *)
  match Parser_messages.message s with
  | exception Not_found -> ()
  | message ->
      raise (Found (fragments text message))

let report text token checkpoint : string option =
  try
    message_from_token token;
    message_from_state_id text checkpoint;
    None
   with Found s -> Some s
