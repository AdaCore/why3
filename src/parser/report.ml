(*
   This file is completely copied from Compcert's preparser. Reference manual of
   menhir takes this as example.
 *)

 open Parser.MenhirInterpreter
 module S = MenhirLib.General (* Streams *)

 (* -------------------------------------------------------------------------- *)

 (* There are places where we may hit an internal error and we would like to fail
    abruptly because "this cannot happen". Yet, it is safer when shipping to
    silently cover up for our internal error. Thus, we typically use an idiom of
    the form [if debug then assert false else <some default value>]. *)

 let debug = false

 (* -------------------------------------------------------------------------- *)

 (* [stack checkpoint] extracts the parser's stack out of a checkpoint. *)

 let stack checkpoint =
   match checkpoint with
   | HandlingError env ->
       stack env
   | _ ->
       assert false (* this cannot happen, I promise *)

 (* -------------------------------------------------------------------------- *)

 (* [state checkpoint] extracts the number of the current state out of a
    parser checkpoint. *)

 let state checkpoint : int =
   match Lazy.force (stack checkpoint) with
   | S.Nil ->
       (* Hmm... The parser is in its initial state. Its number is
          usually 0. This is a BIG HACK. TEMPORARY *)
       0
   | S.Cons (Element (s, _, _, _), _) ->
       number s

 (* -------------------------------------------------------------------------- *)

 (* We allow an error message to contain the special form $i. We only use it to
    print what was read. *)

 let fragment text message =
   try
     let i = int_of_string (Str.matched_group 1 message) in
     match i with
     | 0 -> fst text
     | _ -> snd text
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

 let report text checkpoint : string =
   (* Find out in which state the parser failed. *)
   let s : int = state checkpoint in
   (* Choose an error message, based on the state number [s].
      Then, customize it, based on dynamic information. *)
   let message = try
     Parser_messages.message s |>
     fragments text
   with Not_found ->
     (* If the state number cannot be found -- which, in principle,
        should not happen, since our list of erroneous states is
        supposed to be complete! -- produce a generic message. *)
     Printf.sprintf "This is an unknown syntax error (%d).\n\
                     Please report.\n" s
   in
   (* Construct the full error message. *)
   Printf.sprintf "%s" message
