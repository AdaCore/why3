(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Sexplib.Std

let debug_float = Debug.register_info_flag "float"
  ~desc:"Avoid@ catching@ exceptions@ in@ order@ to@ get@ \
         float@ literal@ checks@ messages."

(** Construction *)
type int_value = BigInt.t
[@@deriving sexp]

type int_literal_kind =
  ILitUnk | ILitDec | ILitHex | ILitOct | ILitBin
[@@deriving sexp]

type int_constant = {
  il_kind : int_literal_kind;
  il_int  : BigInt.t;
}
[@@deriving sexp]

type real_value = {
  rv_sig  : BigInt.t;
  rv_pow2 : BigInt.t;
  rv_pow5 : BigInt.t;
}
[@@deriving sexp]

type real_literal_kind =
  RLitUnk | RLitDec of int | RLitHex of int
[@@deriving sexp]

type real_constant = {
  rl_kind : real_literal_kind;
  rl_real : real_value
}
[@@deriving sexp]

let compare_real { rv_sig = s1; rv_pow2 = p21; rv_pow5 = p51 } { rv_sig = s2; rv_pow2 = p22; rv_pow5 = p52 } =
  let c = BigInt.compare s1 s2 in
  if c <> 0 then c else
  let c = BigInt.compare p21 p22 in
  if c <> 0 then c else
  BigInt.compare p51 p52

let neg_int { il_kind; il_int = i } =
  { il_kind; il_int = BigInt.minus i }

let neg_real { rl_kind = k; rl_real = r } =
  { rl_kind = k; rl_real = { r with rv_sig = BigInt.minus r.rv_sig } }

let abs_int { il_kind; il_int = i } =
  { il_kind; il_int = BigInt.abs i }

let abs_real { rl_kind; rl_real = r } =
  { rl_kind; rl_real = { r with rv_sig = BigInt.abs r.rv_sig } }

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

let rec normalize v p e =
  let (d,m) = BigInt.computer_div_mod v p in
  if BigInt.eq m BigInt.zero then
    let e2 = BigInt.add e e in
    let (v,f) = normalize d (BigInt.mul p p) e2 in
    let (d,m) = BigInt.computer_div_mod v p in
    if BigInt.eq m BigInt.zero then (d, BigInt.add f e2) else (v, BigInt.add f e)
  else (v, BigInt.zero)

let normalize v p =
  normalize v (BigInt.of_int p) BigInt.one

let real_value ?(pow2 = BigInt.zero) ?(pow5 = BigInt.zero) i =
  if BigInt.eq i BigInt.zero then { rv_sig = i; rv_pow2 = i; rv_pow5 = i }
  else
    let (i, p2) = normalize i 2 in
    let (i, p5) = normalize i 5 in
    { rv_sig = i; rv_pow2 = BigInt.add pow2 p2; rv_pow5 = BigInt.add pow5 p5 }

(** Parsing *)

let parse_in_base radix s =
  let n = String.length s in
  let rec aux acc i =
    if i = n then
      acc
    else begin
      let v = match s.[i] with
        | '0'..'9' as c -> Char.code c - Char.code '0'
        | 'A'..'Z' as c -> 10 + Char.code c - Char.code 'A'
        | 'a'..'z' as c -> 10 + Char.code c - Char.code 'a'
        | _ -> invalid_constant_literal radix s in
      if v >= radix then invalid_constant_literal radix s;
      aux (BigInt.add_int v (BigInt.mul_int radix acc)) (i + 1)
    end in
  aux BigInt.zero 0

let int_literal k ~neg s =
  let i =
    match k with
    | ILitUnk -> assert false
    | ILitBin -> parse_in_base 2 s
    | ILitOct -> parse_in_base 8 s
    | ILitDec -> parse_in_base 10 s
    | ILitHex -> parse_in_base 16 s in
  let i = if neg then BigInt.minus i else i in
  { il_kind = k; il_int = i }

let check_exp e =
  let e = if e.[0] = '-' then String.sub e 1 (String.length e - 1) else e in
  check_integer_literal 10 is_dec e

let real_literal ~radix ~neg ~int ~frac ~exp =
  let e =
    match exp with
    | Some e -> check_exp e; int_of_string e
    | None -> 0 in
  let k, check =
    match radix with
    | 10 -> RLitDec e, is_dec
    | 16 -> RLitHex e, is_hex
    | _ -> assert false in
  if int  <> "" then check_integer_literal radix check int;
  if frac <> "" then check_integer_literal radix check frac;
  let s = parse_in_base radix (int ^ frac) in
  let s = if neg then BigInt.minus s else s in
  let f = BigInt.of_int (- String.length frac) in
  let f = if radix = 16 then BigInt.mul_int 4 f else f in
  let e = BigInt.add_int e f in
  let r =
    match radix with
    | 10 -> real_value ~pow2:e ~pow5:e s
    | 16 -> real_value ~pow2:e ~pow5:BigInt.zero s
    | _ -> assert false in
  { rl_kind = k; rl_real = r }

(** Printing *)

let char_of_int i =
  if i < 10 then
    Char.chr (i + Char.code '0')
  else
    Char.chr (i + Char.code 'A' - 10)

let print_in_base radix digits fmt i =
  let radix = BigInt.of_int radix in
  assert (BigInt.ge i BigInt.zero);
  let rec aux digits i =
    if BigInt.eq i BigInt.zero then
      for _i = 1 to digits do Format.pp_print_char fmt '0' done
    else
      let d,m = BigInt.euclidean_div_mod i radix in
      aux (digits - 1) d;
      Format.pp_print_char fmt (char_of_int (BigInt.to_int m)) in
  aux (Opt.get_def 1 digits) i

let to_small_integer i =
  BigInt.to_int i.il_int

let any_to_dec radix s =
  BigInt.to_string (parse_in_base radix s)

let power2 n =
  BigInt.to_string (BigInt.pow_int_pos 2 n)

type default_format =
  Format.formatter -> string -> unit

type integer_format =
  Format.formatter -> BigInt.t -> unit

type real_format =
  Format.formatter -> string -> string -> string option -> unit

type two_strings_format =
  Format.formatter -> string -> string -> unit

type frac_real_format =
  (Format.formatter -> string -> unit) * two_strings_format * two_strings_format

type delayed_format =
  Format.formatter -> (Format.formatter -> unit) -> unit

type number_support = {
  long_int_support  : [`Default|`Custom of default_format];
  negative_int_support : [`Default|`Custom of delayed_format];
  dec_int_support   : [`Default|`Custom of integer_format|`Unsupported of default_format];
  hex_int_support   : [`Default|`Custom of integer_format|`Unsupported];
  oct_int_support   : [`Default|`Custom of integer_format|`Unsupported];
  bin_int_support   : [`Default|`Custom of integer_format|`Unsupported];
  negative_real_support : [`Default|`Custom of delayed_format];
  dec_real_support  : [`Default|`Custom of real_format|`Unsupported];
  hex_real_support  : [`Default|`Custom of real_format|`Unsupported];
  frac_real_support : [`Custom of frac_real_format|`Unsupported of default_format];
}

let check_support support default try_next =
  match support with
  | `Unsupported -> try_next
  | `Default -> default
  | `Custom f -> f

let force_support support default =
  match support with
  | `Default -> default
  | `Custom f -> f

let force_support_nodef support do_it fallback =
  match support with
  | `Unsupported f -> fallback f
  | `Custom f -> do_it f

let simplify_max_int = BigInt.of_string "2147483646"

let remove_minus e =
  if e.[0] = '-' then begin
    let e = Bytes.of_string e in
    Bytes.set e 0 'm';
    Bytes.unsafe_to_string e
  end else e

let print_dec_int support fmt i =
  match support.long_int_support with
  | `Custom f when BigInt.gt i simplify_max_int ->
      f fmt (BigInt.to_string i)
  | `Default | `Custom _ ->
      match support.dec_int_support with
      | `Default -> Format.pp_print_string fmt (BigInt.to_string i)
      | `Custom f -> f fmt i
      | `Unsupported f -> f fmt (BigInt.to_string i)

let print_hex_int support =
  let default fmt i =
    assert (support.long_int_support = `Default);
    Format.fprintf fmt "0x%a" (print_in_base 16 None) i in
  check_support support.hex_int_support default (print_dec_int support)

let print_oct_int support =
  let default fmt i =
    assert (support.long_int_support = `Default);
    Format.fprintf fmt "0o%a" (print_in_base 8 None) i in
  check_support support.oct_int_support default (print_hex_int support)

let print_bin_int support =
  let default fmt i =
    assert (support.long_int_support = `Default);
    Format.fprintf fmt "0b%a" (print_in_base 2 None) i in
  check_support support.oct_int_support default (print_hex_int support)

let print_dec_real support =
  let default fmt i f e =
    let f = if f = "" then "0" else f in
    match e with
    | None -> Format.fprintf fmt "%s.%s" i f
    | Some e -> Format.fprintf fmt "%s.%se%s" i f e in
  let do_frac (exp_zero, exp_pos, exp_neg) fmt i f e =
    let f = if f = "0" then "" else f in
    let e = Opt.fold (fun _ -> int_of_string) 0 e in
    let e = e - String.length f in
    let n = if i = "0" && f <> "" then f else i ^ f in
    if e = 0 then exp_zero fmt n
    else if e > 0 then exp_pos fmt n ("1" ^ String.make e '0')
    else exp_neg fmt n ("1" ^ String.make (-e) '0') in
  let fallback k fmt i f e =
    let e = match e with None -> "0" | Some e -> remove_minus e in
    k fmt (Printf.sprintf "%s_%s_e%s" i f e) in
  check_support support.dec_real_support default
    (force_support_nodef support.frac_real_support do_frac fallback)

let print_hex_real support =
  let default fmt i f e =
    let f = if f = "" then "0" else f in
    let e = Opt.get_def "0" e in
    Format.fprintf fmt "0x%s.%sp%s" i f e in
  let do_frac (exp_zero, exp_pos, exp_neg) fmt i f e =
    let f = if f = "0" then "" else f in
    let n = any_to_dec 16 (i ^ f) in
    let e = Opt.fold (fun _ -> int_of_string) 0 e in
    let e = e - 4 * String.length f in
    if e = 0 then exp_zero fmt n
    else if e > 0 then exp_pos fmt n (power2 e)
    else exp_neg fmt n (power2 (-e)) in
  let fallback k fmt i f e =
    let e = match e with None -> "0" | Some e -> remove_minus e in
    k fmt (Printf.sprintf "0x%s_%s_p%s" i f e) in
  check_support support.hex_real_support default
  (* TODO: add support for decay to decimal floats *)
    (force_support_nodef support.frac_real_support do_frac fallback)

let print_int_literal support fmt k i =
  let p = match k with
    | ILitUnk -> print_dec_int
    | ILitBin -> print_bin_int
    | ILitOct -> print_oct_int
    | ILitDec -> print_dec_int
    | ILitHex -> print_hex_int in
  if BigInt.lt i BigInt.zero then
    let default fmt f =
      Format.fprintf fmt "(- %t)" f in
    force_support support.negative_int_support default fmt
      (fun fmt -> p support fmt (BigInt.abs i))
  else
    p support fmt i

let print_int_constant support fmt = function
  | { il_kind = k; il_int = i } ->
      print_int_literal support fmt k i

let print_dec_constant support fmt k { rv_sig = i; rv_pow2 = p2; rv_pow5 = p5 } =
  let e = BigInt.min (BigInt.min p2 p5) k in
  let i = BigInt.mul i (BigInt.pow_int_pos_bigint 2 (BigInt.sub p2 e)) in
  let i = BigInt.mul i (BigInt.pow_int_pos_bigint 5 (BigInt.sub p5 e)) in
  let i = BigInt.to_string i in
  let p = BigInt.to_int (BigInt.sub k e) in
  let (i,n) =
    let n = String.length i in
    if n <= p then (String.make (p + 1 - n) '0' ^ i, p + 1) else (i, n) in
  let (i,f) = String.sub i 0 (n - p), String.sub i (n - p) p in
  let f = if f = "" then "0" else f in
  let e =
    if BigInt.eq k BigInt.zero then None
    else Some (BigInt.to_string k) in
  print_dec_real support fmt i f e

let print_hex_constant support fmt k { rv_sig = i; rv_pow2 = p2; rv_pow5 = p5 } =
  let e =
    if BigInt.lt p2 k then
      BigInt.sub p2 (BigInt.euclidean_mod (BigInt.sub p2 k) (BigInt.of_int 4))
    else k in
  assert (BigInt.ge p5 BigInt.zero);
  let i = BigInt.mul i (BigInt.pow_int_pos_bigint 2 (BigInt.sub p2 e)) in
  let i = BigInt.mul i (BigInt.pow_int_pos_bigint 5 p5) in
  let i = Format.asprintf "%a" (print_in_base 16 None) i in
  let p = BigInt.to_int (BigInt.sub k e) in
  assert (p mod 4 = 0);
  let p = p / 4 in
  let (i,n) =
    let n = String.length i in
    if n <= p then (String.make (p + 1 - n) '0' ^ i, p + 1) else (i, n) in
  let (i,f) = String.sub i 0 (n - p), String.sub i (n - p) p in
  let f = if f = "" then "0" else f in
  let e =
    if BigInt.eq k BigInt.zero then None
    else Some (BigInt.to_string k) in
  print_hex_real support fmt i f e

let print_real_constant support fmt
      { rl_kind = k; rl_real = { rv_pow2 = p2; rv_pow5 = p5 } as r } =
  match k with
  | RLitDec e -> print_dec_constant support fmt (BigInt.of_int e) r
  | RLitHex e -> print_hex_constant support fmt (BigInt.of_int e) r
  | RLitUnk ->
      let e = BigInt.min p2 p5 in
      let e =
        try (* if the decimal exponent is between 0 and 2, do not use it *)
          let ei = BigInt.to_int e in
          if 0 <= ei && ei <= 2 then BigInt.zero else e
        with _ -> e in
      print_dec_constant support fmt e r

let print_real_constant support fmt r =
  if BigInt.lt r.rl_real.rv_sig BigInt.zero then
    let r = { r with rl_real = { r.rl_real with rv_sig = BigInt.minus r.rl_real.rv_sig } } in
    let default fmt f =
      Format.fprintf fmt "(- %t)" f in
    force_support support.negative_real_support default fmt
      (fun fmt -> print_real_constant support fmt r)
  else
    print_real_constant support fmt r

(** Range checks *)

type int_range = {
  ir_lower : BigInt.t;
  ir_upper : BigInt.t;
}
[@@deriving sexp]

let create_range lo hi =
  { ir_lower = lo;
    ir_upper = hi;
}

exception OutOfRange of int_constant

let check_range c {ir_lower = lo; ir_upper = hi} =
  let cval = c.il_int in
  if BigInt.lt cval lo || BigInt.gt cval hi then raise (OutOfRange c)

(** Float checks *)

type float_format = {
  fp_exponent_digits    : int;
  fp_significand_digits : int; (* counting the hidden bit *)
}
[@@deriving sexp]

exception NonRepresentableFloat of real_constant

open BigInt

let float_parser c =
  let { rv_sig = i; rv_pow2 = p2; rv_pow5 = p5 } = c.rl_real in
  (* get the value i and e such that c = i * 2 ^ e *)
  if lt p5 zero then raise (NonRepresentableFloat c)
  else
    let i = BigInt.mul i (BigInt.pow_int_pos_bigint 5 p5) in
    i, p2

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
  let s, e = ref s, ref e in

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
    long_int_support = `Default;
    negative_int_support = `Default;
    dec_int_support = `Default;
    hex_int_support = `Default;
    oct_int_support = `Default;
    bin_int_support = `Default;
    negative_real_support = `Default;
    dec_real_support = `Default;
    hex_real_support =  `Default;
    frac_real_support = `Unsupported (fun _ _ -> assert false);
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
      Format.fprintf fmt "Invalid integer literal in base %d: '%s'" n s
  | NonRepresentableFloat c ->
      Format.fprintf fmt "Invalid floating point literal: '%a'"
        (print_real_constant full_support) c
  | OutOfRange c ->
      Format.fprintf fmt "Integer literal %a is out of range"
              (print_int_constant full_support) c
  | _ -> raise exn)

