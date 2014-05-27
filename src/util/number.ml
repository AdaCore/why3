(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format

(** Construction *)

type integer_constant =
  | IConstDec of string
  | IConstHex of string
  | IConstOct of string
  | IConstBin of string

type real_constant =
  | RConstDec of string * string * string option (* int / frac / exp *)
  | RConstHex of string * string * string option

type constant =
  | ConstInt  of integer_constant
  | ConstReal of real_constant

exception InvalidConstantLiteral of int * string
let invalid_constant_literal n s = raise (InvalidConstantLiteral(n,s))

let check_integer_literal n f s =
  let l = String.length s in
  if l = 0 then invalid_constant_literal n s;
  for i = 0 to l-1 do
    if not (f s.[i]) then invalid_constant_literal n s;
  done

let is_hex = function '0'..'9' | 'A'..'F' | 'a'..'f' -> true | _ -> false
let is_dec = function '0'..'9' -> true | _ -> false
let is_oct = function '0'..'7' -> true | _ -> false
let is_bin = function '0'..'1' -> true | _ -> false

let int_const_dec s =
  check_integer_literal 10 is_dec s;
  IConstDec s

let int_const_hex s =
  check_integer_literal 16 is_hex s;
  IConstHex s

let int_const_oct s =
  check_integer_literal 8 is_oct s;
  IConstOct s

let int_const_bin s =
  check_integer_literal 2 is_bin s;
  IConstBin s

let check_exp e =
  let e = if e.[0] = '-' then String.sub e 1 (String.length e - 1) else e in
  check_integer_literal 10 is_dec e

let real_const_dec i f e =
  if i <> "" then check_integer_literal 10 is_dec i;
  if f <> "" then check_integer_literal 10 is_dec f;
  Opt.iter check_exp e;
  RConstDec (i,f,e)

let real_const_hex i f e =
  if i <> "" then check_integer_literal 16 is_hex i;
  if f <> "" then check_integer_literal 16 is_hex f;
  Opt.iter check_exp e;
  RConstHex (i,f,e)

(** Printing *)


let compute_any radix s =
  let n = String.length s in
  let rec compute acc i =
    if i = n then
      acc
    else begin
      let v = match s.[i] with
        | '0'..'9' as c -> Char.code c - Char.code '0'
        | 'A'..'Z' as c -> 10 + Char.code c - Char.code 'A'
        | 'a'..'z' as c -> 10 + Char.code c - Char.code 'a'
        | _ -> assert false in
      assert (v < radix);
      compute (BigInt.add_int v (BigInt.mul_int radix acc)) (i + 1)
    end in
  (compute BigInt.zero 0)

let compute_int c =
  match c with
  | IConstDec s -> compute_any 10 s
  | IConstHex s -> compute_any 16 s
  | IConstOct s -> compute_any 8 s
  | IConstBin s -> compute_any 2 s

let any_to_dec radix s =
  BigInt.to_string (compute_any radix s)

let power2 n =
  BigInt.to_string (BigInt.pow_int_pos 2 n)

type integer_format =
  (string -> unit, Format.formatter, unit) format

type real_format =
  (string -> string -> string -> unit, Format.formatter, unit) format

type part_real_format =
  (string -> string -> unit, Format.formatter, unit) format

type dec_real_format =
  | PrintDecReal of part_real_format * real_format

type frac_real_format =
  | PrintFracReal of integer_format * part_real_format * part_real_format

type 'a number_support_kind =
  | Number_unsupported
  | Number_default
  | Number_custom of 'a

type integer_support_kind = integer_format number_support_kind

type number_support = {
  long_int_support  : bool;
  extra_leading_zeros_support : bool;
  dec_int_support   : integer_support_kind;
  hex_int_support   : integer_support_kind;
  oct_int_support   : integer_support_kind;
  bin_int_support   : integer_support_kind;
  def_int_support   : integer_support_kind;
  dec_real_support  : dec_real_format number_support_kind;
  hex_real_support  : real_format number_support_kind;
  frac_real_support : frac_real_format number_support_kind;
  def_real_support  : integer_support_kind;
}

let check_support support default do_it try_next v =
  match support with
  | Number_unsupported -> try_next v
  | Number_default -> do_it (Opt.get default) v
  | Number_custom f -> do_it f v

let force_support support do_it v =
  match support with
  | Number_unsupported -> assert false
  | Number_default -> assert false
  | Number_custom f -> do_it f v

let simplify_max_int = BigInt.of_string "2147483646"

let remove_minus e =
  if e.[0] = '-' then
    (let e' = String.copy e in e'.[0] <- 'm'; e')
  else e

let print_dec_int support fmt i =
  let fallback i =
    force_support support.def_int_support (fprintf fmt) i in
  if not support.long_int_support &&
     (BigInt.compare (BigInt.of_string i) simplify_max_int > 0) then
    fallback i
  else
    check_support support.dec_int_support (Some "%s") (fprintf fmt)
    fallback i

let print_hex_int support fmt =
  check_support support.hex_int_support (Some "0x%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 16 i))

let print_oct_int support fmt =
  check_support support.oct_int_support (Some "0o%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 8 i))

let print_bin_int support fmt =
  check_support support.bin_int_support (Some "0b%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 2 i))

let remove_leading_zeros support s =
  if support.extra_leading_zeros_support then s else
  let len = String.length s in
  let rec aux i =
    if i+1 < len && s.[i] = '0' then aux (i+1) else i
  in
  let i = aux 0 in
  String.sub s i (len - i)

let print_dec_real support fmt =
  check_support support.dec_real_support
    (Some (PrintDecReal ("%s.%s", "%s.%se%s")))
    (fun (PrintDecReal (noexp,full)) i f e ->
      match e with
      | None -> fprintf fmt noexp
          (remove_leading_zeros support i)
          (if f = "" then "0" else f)
      | Some e -> fprintf fmt full
          (remove_leading_zeros support i)
          (if f = "" then "0" else f)
          (remove_leading_zeros support e))
    (check_support support.frac_real_support None
    (fun (PrintFracReal (exp_zero, exp_pos, exp_neg)) i f e ->
      let f = if f = "0" then "" else f in
      let e = Opt.fold (fun _ -> int_of_string) 0 e in
      let e = e - String.length f in
      if e = 0 then
        fprintf fmt exp_zero (remove_leading_zeros support (i ^ f))
      else if e > 0 then
        fprintf fmt exp_pos (remove_leading_zeros support (i ^ f))
          ("1" ^ String.make e '0')
      else
        fprintf fmt exp_neg (remove_leading_zeros support (i ^ f))
          ("1" ^ String.make (-e) '0'))
  (force_support support.def_real_support
    (fun def i f e -> fprintf fmt def (sprintf "%s_%s_e%s" i f
      (match e with None -> "0" | Some e -> remove_minus e)))
  ))

let print_hex_real support fmt =
  check_support support.hex_real_support
    (Some "0x%s.%sp%s")
    (fun s i f e -> fprintf fmt s i
      (if f = "" then "0" else f)
      (Opt.get_def "0" e))
  (* TODO: add support for decay to decimal floats *)
  (check_support support.frac_real_support None
    (fun (PrintFracReal (exp_zero, exp_pos, exp_neg)) i f e ->
      let f = if f = "0" then "" else f in
      let dec = any_to_dec 16 (i ^ f) in
      let e = Opt.fold (fun _ -> int_of_string) 0 e in
      let e = e - 4 * String.length f in
      if e = 0 then
        fprintf fmt exp_zero dec
      else if e > 0 then
        fprintf fmt exp_pos dec (power2 e)
      else
        fprintf fmt exp_neg dec (power2 (-e)))
  (force_support support.def_real_support
    (fun def i f e -> fprintf fmt def (sprintf "0x%s_%s_p%s" i f
      (match e with None -> "0" | Some e -> remove_minus e)))
  ))

let print support fmt = function
  | ConstInt (IConstDec i) -> print_dec_int support fmt i
  | ConstInt (IConstHex i) -> print_hex_int support fmt i
  | ConstInt (IConstOct i) -> print_oct_int support fmt i
  | ConstInt (IConstBin i) -> print_bin_int support fmt i
  | ConstReal (RConstDec (i, f, e)) -> print_dec_real support fmt i f e
  | ConstReal (RConstHex (i, f, e)) -> print_hex_real support fmt i f e

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | InvalidConstantLiteral (n,s) ->
      fprintf fmt "Invalid constant literal in base %d: '%s'" n s
  | _ -> raise exn
  end

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
