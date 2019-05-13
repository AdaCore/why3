(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type exn_printer = Format.formatter -> exn -> unit

let exn_printers =
  (Stack.create () : (Format.formatter -> exn -> unit) Stack.t)

let register exn_printer = Stack.push exn_printer exn_printers

let anomaly_exn_printer fmt exn =
  Format.fprintf fmt "anomaly: %s" (Printexc.to_string exn)

exception Exit_loop

let registered_exn_printer fmt exn =
  let test f =
    try
      Format.fprintf fmt "@[%a@]" f exn;
      raise Exit_loop
    with
      | Exit_loop -> raise Exit_loop
      | _ -> ()
  in
  Stack.iter test exn_printers


let exn_printer fmt exn =
  try
    registered_exn_printer fmt exn;
    anomaly_exn_printer fmt exn
  with Exit_loop -> ()


let () =
  Printexc.register_printer (fun exn ->
      let b = Buffer.create 10 in
      let fmt = Format.formatter_of_buffer b in
      try
        registered_exn_printer fmt exn;
        None
      with Exit_loop ->
        Format.pp_print_flush fmt ();
        Some (Buffer.contents b)
    )
