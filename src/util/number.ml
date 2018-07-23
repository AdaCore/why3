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

open Format

(** Construction *)

type integer_literal =
  | IConstRaw of BigInt.t
  | IConstDec of string
  | IConstHex of string
  | IConstOct of string
  | IConstBin of string

type integer_constant = {
    ic_negative : bool;
    ic_abs : integer_literal;
  }

type real_literal =
  | RConstDec of string * string * string option (* int / frac / exp *)
  | RConstHex of string * string * string option

type real_constant = {
    rc_negative : bool;
    rc_abs : real_literal;
  }

type constant =
  | ConstInt  of integer_constant
  | ConstReal of real_constant

let is_negative c =
  match c with
  | ConstInt i -> i.ic_negative
  | ConstReal r -> r.rc_negative

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

let int_literal_dec s =
  check_integer_literal 10 is_dec s;
  IConstDec s

let int_literal_hex s =
  check_integer_literal 16 is_hex s;
  IConstHex s

let int_literal_oct s =
  check_integer_literal 8 is_oct s;
  IConstOct s

let int_literal_bin s =
  check_integer_literal 2 is_bin s;
  IConstBin s

let int_literal_raw i =
  assert (BigInt.ge i BigInt.zero);
  IConstRaw i

let int_const_of_big_int n =
  let neg, n =
    if BigInt.ge n BigInt.zero then
      false, n
    else
      true, BigInt.minus n
  in
  { ic_negative = neg; ic_abs = IConstRaw n }

let int_const_of_int n =
  int_const_of_big_int (BigInt.of_int n)

let const_of_big_int n =
  ConstInt (int_const_of_big_int n)

let const_of_int n =
  const_of_big_int (BigInt.of_int n)

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

(** Printing *)

let compute_int_literal c =
  match c with
  | IConstRaw i -> i
  | IConstDec s -> compute_any 10 s
  | IConstHex s -> compute_any 16 s
  | IConstOct s -> compute_any 8 s
  | IConstBin s -> compute_any 2 s

let compute_int_constant c =
  let a = compute_int_literal c.ic_abs in
  if c.ic_negative then BigInt.minus a else a

let to_small_integer i =
  match i with
  | IConstRaw i -> BigInt.to_int i
  | IConstDec s -> int_of_string s
  | IConstHex s -> int_of_string ("0x"^s)
  | IConstOct s -> int_of_string ("0o"^s)
  | IConstBin s -> int_of_string ("0b"^s)


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

type 'a negative_format =
  ((Format.formatter->'a->unit)->'a->unit,Format.formatter,unit) format

type number_support = {
  long_int_support  : bool;
  extra_leading_zeros_support : bool;
  negative_int_support  : (integer_literal negative_format) number_support_kind;
  dec_int_support   : integer_support_kind;
  hex_int_support   : integer_support_kind;
  oct_int_support   : integer_support_kind;
  bin_int_support   : integer_support_kind;
  def_int_support   : integer_support_kind;
  negative_real_support  : (real_literal negative_format) number_support_kind;
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
  if e.[0] = '-' then begin
    let e = Bytes.of_string e in
    Bytes.set e 0 'm';
    Bytes.unsafe_to_string e
  end else e

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

let print_int_literal support fmt = function
  | IConstRaw i -> print_dec_int support fmt (BigInt.to_string i)
  | IConstDec i -> print_dec_int support fmt i
  | IConstHex i -> print_hex_int support fmt i
  | IConstOct i -> print_oct_int support fmt i
  | IConstBin i -> print_bin_int support fmt i

let print_real_literal support fmt = function
  | RConstDec (i, f, e) -> print_dec_real support fmt i f e
  | RConstHex (i, f, e) -> print_hex_real support fmt i f e

let print_int_constant support fmt i =
  if i.ic_negative then
    check_support support.negative_int_support (Some "(- %a)")
                  (fun def n -> fprintf fmt def (print_int_literal support) n)
                  (fun _ -> assert false)
                  i.ic_abs
  else
    fprintf fmt "%a" (print_int_literal support) i.ic_abs

let print_real_constant support fmt r =
  if r.rc_negative then
    check_support support.negative_real_support (Some "(- %a)")
                  (fun def n -> fprintf fmt def (print_real_literal support) n)
                  (fun _ -> assert false)
                  r.rc_abs
  else
    fprintf fmt "%a" (print_real_literal support) r.rc_abs


let print support fmt = function
  | ConstInt i -> print_int_constant support fmt i
  | ConstReal r -> print_real_constant support fmt r







let char_of_int i =
  if i < 10 then
    Char.chr (i + Char.code '0')
  else
    Char.chr (i + Char.code 'A' - 10)

open BigInt

let print_zeros fmt n =
  for _i = 0 to n - 1 do
    pp_print_char fmt '0'
  done

let rec print_in_base_aux radix digits fmt i =
  if lt i radix then begin
    begin match digits with
      | Some n -> print_zeros fmt (n - 1)
      | None -> ()
    end;
    fprintf fmt "%c" (char_of_int (to_int i))
  end
  else
    let d,m = euclidean_div_mod i radix in
    let digits = Opt.map ((+) (-1)) digits in
    print_in_base_aux radix digits fmt d;
    fprintf fmt "%c" (char_of_int (to_int m))

let print_in_base radix digits fmt i =
  print_in_base_aux (of_int radix) digits fmt i

(** Range checks *)

type int_range = {
  ir_lower : BigInt.t;
  ir_upper : BigInt.t;
}

let create_range lo hi =
  { ir_lower = lo;
    ir_upper = hi;
}

exception OutOfRange of integer_constant

let check_range c {ir_lower = lo; ir_upper = hi} =
  let cval = compute_int_literal c.ic_abs in
  let cval = if c.ic_negative then BigInt.minus cval else cval in
  if BigInt.lt cval lo || BigInt.gt cval hi then raise (OutOfRange c)

(** Float checks *)

type float_format = {
  fp_exponent_digits    : int;
  fp_significand_digits : int; (* counting the hidden bit *)
}

exception NonRepresentableFloat of real_literal

let debug_float = Debug.register_info_flag "float"
  ~desc:"Avoid@ catching@ exceptions@ in@ order@ to@ get@ \
         float@ literal@ checks@ messages."

let float_parser c =
  let exp_parser e = match e.[0] with
    | '-' -> minus (compute_any 10 (String.sub e 1 (String.length e - 1)))
    | _   -> compute_any 10 e
  in

  (* get the value s and e such that c = s * 2 ^ e *)
  let s, e =
    match c with
    (* c = a.b * 10 ^ e *)
    | RConstDec (a,b,e) ->
      let b_length = String.length b in
      let s = ref (compute_any 10 (a ^ b)) in
      let e = sub (match e with
          | None -> Debug.dprintf debug_float "c = %s.%s" a b;
            zero
          | Some e -> Debug.dprintf debug_float "c = %s.%se%s" a b e;
            exp_parser e)
          (of_int b_length)
      in
      (* transform c = s * 10 ^ i into c = s' * 2 ^ i' *)
      let s =
        if lt e zero then begin
          let efive = pow_int_pos_bigint 5 (minus e) in
          let dv, rem = euclidean_div_mod !s efive in
          if not (eq rem zero) then begin
            raise (NonRepresentableFloat c);
          end else
            dv
        end else
          mul !s (pow_int_pos_bigint 5 e)
      in
      Debug.dprintf debug_float " = %s * 2 ^ %s" (to_string s) (to_string e);
      ref s, ref e

    (* c = a.b * 2 ^ e *)
    | RConstHex (a,b,e) ->
      let b_length = String.length b in
      ref (compute_any 16 (a ^ b)),
      ref (sub (match e with
          | None -> Debug.dprintf debug_float "c = %s.%s" a b;
            zero
          | Some e -> Debug.dprintf debug_float "c = %s.%sp%s" a b e;
            exp_parser e)
          (of_int (b_length * 4)))
  in
  s, e

let compute_float c fp =
  let eb = BigInt.of_int fp.fp_exponent_digits in
  let sb = BigInt.of_int fp.fp_significand_digits in
  (* 2 ^ (sb - 1)    min representable normalized significand*)
  let smin = pow_int_pos_bigint 2 (sub sb one) in
  (* (2 ^ sb) - 1    max representable normalized significand*)
  let smax = sub (pow_int_pos_bigint 2 sb) one in
  (* 2 ^ (eb - 1)    exponent of the infinities *)
  let emax = pow_int_pos_bigint 2 (sub eb one) in
  (* 1 - emax        exponent of the denormalized *)
  let eden = sub one emax in
  (* 3 - emax - sb   smallest denormalized' exponent *)
  let emin = sub (add (of_int 2) eden) sb in

  (* get [s] and [e] such that "c = s * 2 ^ e" *)
  let s, e = float_parser c in

  (* if s = 0 stop now *)
  if eq !s zero then
    zero, zero

  else begin

    (* if s is too big or e is too small, try to remove trailing zeros
       in s and incr e *)
    while gt !s smax || lt !e emin do
      let new_s, rem = euclidean_div_mod !s (of_int 2) in
      if not (eq rem zero) then begin
        Debug.dprintf debug_float "Too many digits in significand.";
        raise (NonRepresentableFloat c);
      end else begin
        s := new_s;
        e := succ !e
      end
    done;

    (* if s is too small and e is too big, add trailing zeros in s and
       decr e *)
    while lt !s smin && gt !e emin do
      s := mul_int 2 !s;
      e := pred !e
    done;

    Debug.dprintf debug_float " = %s * 2 ^ %s@." (to_string !s) (to_string !e);

    if lt !s smin then begin
      (* denormal case *)

      Debug.dprintf debug_float "final: c = 0.[%s] * 2 ^ ([0] - bias + 1); bias=%s, i.e, 0[%a][%a]@."
        (to_string !s) (to_string (sub emax one)) (print_in_base 2 (Some (to_int eb))) zero
      (print_in_base 2 (Some (to_int (sub sb one)))) !s;

      zero, !s

    end else begin
      (* normal case *)

      (* normalize the exponent *)
      let fe = add !e (sub sb one) in

      (* now that s and e are in shape, check that e is not too big *)
      if ge fe emax then begin
        Debug.dprintf debug_float "Exponent too big.";
        raise (NonRepresentableFloat c)
      end;

      (* add the exponent bia to e *)
      let fe = add fe (sub emax one) in
      let fs = sub !s smin in

      Debug.dprintf debug_float "final: c = 1.[%s] * 2 ^ ([%s] - bias); bias=%s, i.e, 0[%a][%a]@."
        (to_string fs) (to_string fe) (to_string (sub emax one))
        (print_in_base 2 (Some (to_int eb))) fe
        (print_in_base 2 (Some (to_int (sub sb one)))) fs;

      assert (le zero fs && lt fs (pow_int_pos_bigint 2 (sub sb one))
              && le zero fe && lt fe (sub (pow_int_pos_bigint 2 eb) one));

      fe, fs
    end
  end

let check_float c fp = ignore (compute_float c fp)


let full_support =
  {
    long_int_support = true;
    extra_leading_zeros_support = true;
    negative_int_support = Number_default;
    dec_int_support = Number_default;
    hex_int_support = Number_default;
    oct_int_support = Number_default;
    bin_int_support = Number_default;
    def_int_support = Number_default;
    negative_real_support = Number_default;
    dec_real_support = Number_default;
    hex_real_support = Number_default;
    frac_real_support = Number_default;
    def_real_support = Number_default;
  }

(*

let print_integer_literal fmt = function
  | IConstDec s -> fprintf fmt "%s" s
  | IConstHex s -> fprintf fmt "0x%s" s
  | IConstOct s -> fprintf fmt "0o%s" s
  | IConstBin s -> fprintf fmt "0b%s" s

let print_real_literal fmt = function
  | RConstDec (i,f,None)   -> fprintf fmt "%s.%s" i f
  | RConstDec (i,f,Some e) -> fprintf fmt "%s.%se%s" i f e
  | RConstHex (i,f,Some e) -> fprintf fmt "0x%s.%sp%s" i f e
  | RConstHex (i,f,None)   -> fprintf fmt "0x%s.%s" i f

let print_unsigned_constant fmt = function
  | ConstInt c  -> print_integer_literal fmt c
  | ConstReal c -> print_real_literal fmt c

let print_constant fmt c =
  if c.is_positive then print_unsigned_constant fmt c.abs_value
  else fprintf fmt "-%a" print_unsigned_constant c.abs_value
 *)

let () = Exn_printer.register (fun fmt exn -> match exn with
  | InvalidConstantLiteral (n,s) ->
      fprintf fmt "Invalid integer literal in base %d: '%s'" n s
  | NonRepresentableFloat c ->
      fprintf fmt "Invalid floating point literal: '%a'"
        (print_real_literal full_support) c
  | OutOfRange c ->
      fprintf fmt "Integer literal %a is out of range"
              (print_int_constant full_support) c
  | _ -> raise exn)

let print_constant = print full_support
