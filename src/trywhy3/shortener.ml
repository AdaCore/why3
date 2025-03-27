(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* The likelihood of operators having spaces before and after them is
   known a priori. This likelihood will be updated as operators are
   encountered. *)

module Knowledge = struct

  let operator t1 t2 =
    let v1 =
      match t1 with
      | ']' | ')' | '.' | ',' -> -2
      | ';' | ':' | '?' | '!' | '@' | '[' | '"' | '\'' -> -1
      | _ -> 0 in
    let v2 =
      match t2 with
      | '[' | '(' -> -2
      | '`' | '"' | '@'  -> -1
      | _ -> 0 in
    (v1, v2)

  let operator t =
    let l = String.length t in
    assert (l > 0);
    let v = operator t.[0] t.[l - 1] in
    if l = 1 then
      match t.[0] with
      | '"' | '`' | '\'' -> ((0, -1), (-1, 0))
      | _ -> (v, v)
    else (v, v)

end

module Base64 = struct

  let encode i =
    if  0 <= i && i < 26 then Char.chr (65 + i) else
    if 26 <= i && i < 52 then Char.chr (97 + i - 26) else
    if 52 <= i && i < 62 then Char.chr (48 + i - 52) else
    if i = 62 then '+' else
    if i = 63 then '/' else
    assert false

  let decode c =
    match c with
    | 'A' .. 'Z' -> Char.code c - 65
    | 'a' .. 'z' -> Char.code c - 97 + 26
    | '0' .. '9' -> Char.code c - 48 + 52
    | '+' -> 62
    | '/' -> 63
    | _ -> invalid_arg "Base64.decode"

end

module Token = struct

  let ops = "!\"#$%&'()*+,-./:;<=>?@[\\]^`{|}"
  let () = assert (String.length ops <= 32)

  (* all the letters, all the digits, and one more character *)
  let is_alnum = function
    | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' -> true
    | _ -> false

  let count_ws inps inpi =
    let inpl = String.length inps in
    let i = ref inpi in
    while !i < inpl && inps.[!i] = ' ' do incr i; done;
    !i - inpi

  let get inps inpi =
    let inpl = String.length inps in
    if inpi >= inpl then 0
    else
      let i = ref inpi in
      if is_alnum inps.[inpi] then
        let () = incr i in
        while !i < inpl && is_alnum inps.[!i] do incr i; done
      else
        while !i < inpl && String.index_opt ops inps.[!i] <> None do incr i; done;
      !i - inpi

end

(* Each operator comes with a likelihood of having spaces on the left
   and/or on the right of it. Explicit spaces or antispaces are added
   whenever the prediction is wrong. The likelihood is updated as new
   tokens arrive. Two predictors are used alternatively for each
   operator; this makes the prediction for quotes much more robust, at
   the cost of a slower learning for operators that would be correctly
   predicted by a single predictor. *)

module Predictor = struct

  type token = Id | Op of string | Sp | Nil | Unk

  let last = ref Nil

  let prob = Hashtbl.create 100

  let delayed = ref false

  let reset () =
    last := Nil;
    Hashtbl.clear prob;
    delayed := false

  let get t =
    match Hashtbl.find_opt prob t with
    | Some v -> v
    | None -> Knowledge.operator t

  let clamp v =
    if v < -2 then -2
    else if v > 1 then 1
    else v

  let update_left t d =
    let ((v1, v2), w) = get t in
    let d = if d = 0 then if v1 >= 0 then 1 else -1 else d in
    let v1 = clamp (v1 + d) in
    Hashtbl.replace prob t ((v1, v2), w);
    v1 >= 0

  let update_right t d =
    let ((v1, v2), w) = get t in
    let d = if d = 0 then if v2 >= 0 then 1 else -1 else d in
    let v2 = clamp (v2 + d) in
    Hashtbl.replace prob t (w, (v1, v2));
    v2 >= 0

  let query_left t =
    let ((v1, _), _) = get t in
    v1 >= 0

  let query_right t =
    let ((_, v2), _) = get t in
    v2 >= 0

  let update t =
    let b =
      match !last, t with
      | Nil, Op t -> update_left t (-1) && false
      | Sp, Op t -> update_left t 1 && false
      | Id, Op t -> update_left t 0
      | Op t, Nil -> update_right t (-1) && false
      | Op t, Sp -> update_right t 1 && false
      | Op t, Id -> update_right t 0
      | Op _, Op _ -> true
      | Id, Id -> true
      | Unk, _ -> false
      | _, Unk -> false
      | _, _ -> false in
    last := t;
    b

  let query t =
    match !last, t with
    | _, Sp -> false
    | _, Nil -> false
    | Nil, _ -> false
    | Op t, Id -> query_right t
    | Id, Op t -> query_left t
    | Op _, Op _ -> true
    | Id, Id -> true
    | Unk, _ -> false
    | _, Unk -> false
    | Sp, _ -> false

end

exception Invalid

(* Tokens are stored at the end of a queue. Tokens present in the queue
   are encoded in compact form. If recently encountered, they are
   directly encoded in the category. Otherwise, their queue position is
   encoded as a single character, and overflowing bits are stored as the
   category. Recently encountered identifiers are moved to the end of the
   queue. Length-1 identifiers are discarded as soon as they are no
   longer encodable for free. Other identifiers are discarded once they
   reach the start of the queue. *)

module Dict = struct

  let nb_long_cat = 4
  let max_short = 32
  let dict_size = nb_long_cat * 64 + max_short
  let nb_cat = nb_long_cat + max_short

  let dict = Array.make dict_size ""
  let last = ref 0

  let find s =
    let i = ref 0 in
    while !i < !last && not (String.equal s dict.(!i)) do incr i; done;
    !i

  let promote s i =
    let j = !last - max_short in
    if (i < j || (i >= !last && j >= 0)) && String.length dict.(j) = 1 then
      begin
        Array.blit dict (j + 1) dict j (max_short - 1);
        decr last;
      end;
    if i < !last then
      Array.blit dict (i + 1) dict i (!last - i - 1)
    else if !last = dict_size then
      Array.blit dict 1 dict 0 (dict_size - 1)
    else incr last;
    dict.(!last - 1) <- s

  let insert s =
    promote s dict_size

  let reset () =
    last := 0

  let encode s l =
    let i = find s in
    if i >= !last then raise Invalid;
    let short = i - (!last - max_short) in
    promote s i;
    let m = if Token.is_alnum s.[0] then Predictor.Id else Predictor.Op s in
    if 0 <= short then (l, m, short, "")
    else
      let se = String.make 1 (Base64.encode (i mod 64)) in
      (l, m, max_short + i / 64, se)

  let decode cat inps inpi =
    let i =
      if cat < max_short then !last - max_short + cat
      else if inpi + 1 > String.length inps then invalid_arg "Dict.decode"
      else (cat - max_short) * 64 + Base64.decode inps.[inpi] in
    if i >= !last then invalid_arg "Dict.decode";
    let s = dict.(i) in
    promote s i;
    let m = if Token.is_alnum s.[0] then Predictor.Id else Predictor.Op s in
    let l = if cat < max_short then 0 else 1 in
    (l, m, s)

end

(* Identifiers are composed of "A..Za..z0..9_". When unknown, they are
   encoded as is, with '_' replaced by '+'. If their length is not too
   large, it is part of the category. Otherwise, '/' serves as end
   marker. *)

module Ident = struct

  let max_length = 8
  let nb_cat = max_length + 1

  let encode s l =
    let s = String.map (function '_' -> '+' | c -> c) s in
    if l <= max_length then (l, l, s)
    else (l, 0, s ^ "/")

  let decode cat inps inpi =
    let l =
      if cat = 0 then
        try String.index_from inps inpi '/' - inpi
        with Not_found -> invalid_arg "Ident.decode"
      else cat in
    if inpi + l > String.length inps then invalid_arg "Ident.decode";
    let s = String.sub inps inpi l in
    let s = String.map (function '+' -> '_' | c -> c) s in
    let l = if cat = 0 then l + 1 else l in
    (l, Predictor.Id, s)

end

(* Operators are encoded as a sequence of characters. The end of the sequence
   is marked by setting the msb of the last character. *)

module Operator = struct

  let encode s l =
    let enc i c =
      let j = String.index Token.ops c in
      let j = if i = l - 1 then j + 32 else j in
      Base64.encode j in
    let s = String.mapi enc s in
    (l, 0, s)

  let decode _cat inps inpi =
    let inpl = String.length inps in
    let s = Buffer.create 10 in
    let rec aux i =
      if i >= inpl then invalid_arg "Operator.decode";
      let o = Base64.decode inps.[i] in
      let p = o mod 32 in
      if p >= String.length Token.ops then invalid_arg "Operator.decode";
      Buffer.add_char s Token.ops.[p];
      if o >= 32 then i + 1 - inpi
      else aux (i + 1) in
    let l = aux inpi in
    let s = Buffer.contents s in
    (l, Predictor.Op s, s)

end

(* Identifiers are either found in a dictionary or encoded directly. In
   the later case, they are added to the dictionary. *)

module Word = struct

  let nb_cat = Dict.nb_cat + Ident.nb_cat + 1

  let encode inps inpi =
    let l = Token.get inps inpi in
    if l = 0 then raise Invalid;
    let s = String.sub inps inpi l in
    try Dict.encode s l
    with Invalid ->
      Dict.insert s;
      if Token.is_alnum inps.[inpi] then
        let (l, cat, se) = Ident.encode s l in
        (l, Predictor.Id, cat + Dict.nb_cat, se)
      else
        let (l, _, se) = Operator.encode s l in
        (l, Predictor.Op s, Dict.nb_cat + Ident.nb_cat, se)

  let decode cat inps inpi =
    if cat < Dict.nb_cat then
      Dict.decode cat inps inpi
    else
      let (_, _, s) as r =
        if cat < Dict.nb_cat + Ident.nb_cat then
          Ident.decode (cat - Dict.nb_cat) inps inpi
        else
          Operator.decode 0 inps inpi in
      Dict.insert s;
      r

end

(* 0, 1, and 2 spaces are encoded as 0-character chunks. The 0-space
   token (aka Nil) is used to indicate an incorrect prediction for the
   number of spaces before or after an operator. *)

module Whitespace = struct

  let nb_cat = 3

  let encode inps inpi =
    let l = Token.count_ws inps inpi in
    if l = 0 then raise Invalid;
    let l = if l >= nb_cat then nb_cat - 1 else l in
    (l, Predictor.Sp, l, "")

  let decode cat _inps _inpi =
    if cat = 0 then (0, Predictor.Nil, "")
    else (0, Predictor.Sp, String.make cat ' ')

end

(* The encoding of newline bytes also encompass the following
   indentation. This indentation is either absent, or stored relatively
   to the previous indentation, or stored in a 1-character chunk (hence,
   up to 64 spaces). An absent indentation does not modify the previously
   stored indentation, so that empty lines have no impact. *)

module Newline = struct

  let max_rel = 4
  let nb_cat = max_rel * 2 + 3

  let last = ref 2

  let reset () =
    last := 2

  let encode inps inpi =
    if inps.[inpi] <> '\n' then raise Invalid;
    let l = Token.count_ws inps (inpi + 1) in
    if l = 0 then (1, Predictor.Sp, nb_cat - 1, "")
    else
      let la = !last in
      if abs (l - la) <= max_rel then
        let () = last := l in
        (l + 1, Predictor.Sp, l - la + max_rel, "")
      else
        let l = if l > 64 then 64 else l in
        last := l;
        (l + 1, Predictor.Sp, nb_cat - 2, String.make 1 (Base64.encode (l - 1)))

  let decode cat inps inpi =
    let (w, l) =
      if cat < nb_cat - 2 then
        (!last + cat - max_rel, 0)
      else if cat = nb_cat - 1 then (0, 0)
      else if inpi + 1 > String.length inps then invalid_arg "Newline.decode"
      else (Base64.decode inps.[inpi] + 1, 1) in
    if cat < nb_cat - 1 then last := w;
    let s = Bytes.make (w + 1) ' ' in
    Bytes.set s 0 '\n';
    (l, Predictor.Sp, Bytes.to_string s)

end

(* The remaining bytes are stored as 1-character chunks. The category
   encodes the two most significant bits of a byte, while the chunk
   content contains the six other bits. *)

module Garbage = struct

  let encode inps inpi =
    let c = Char.code inps.[inpi] in
    (1, Predictor.Unk, c / 64, String.make 1 (Base64.encode (c mod 64)))

  let decode cat inps inpi =
    if inpi + 1 > String.length inps then invalid_arg "Garbage.decode";
    let c = Char.chr (cat * 64 + Base64.decode inps.[inpi]) in
    (1, Predictor.Unk, String.make 1 c)

end

(* Encoding functions return a tuple comprised of the length of the read
   bytes, data for the space predictor, the relative category, and the
   content of the chunk. Decoding functions return a tuple comprised of
   the length of the chunk, data for the space predictor, and the decoded
   text. *)

let categories = [|
    (Whitespace.nb_cat, Whitespace.encode, Whitespace.decode);
    (Newline.nb_cat, Newline.encode, Newline.decode);
    (Word.nb_cat, Word.encode, Word.decode);
    (4, Garbage.encode, Garbage.decode);
  |]

let encode_categories, decode_categories =
  let max = 64 in
  let t = Array.make max (fun _ _ -> invalid_arg "decode") in
  let l = ref [] in
  let i = ref 0 in
  let add enc dec =
    assert (!i < max);
    l := (!i, enc) :: !l;
    t.(!i) <- dec;
    incr i in
  let add_dec dec =
    assert (!i < max);
    t.(!i) <- dec;
    incr i in
  Array.iter (function
      | (nb, enc, dec) ->
          add enc (dec 0);
          for i = 1 to nb - 1 do
            add_dec (dec i)
          done
    ) categories;
  (*Printf.printf "%d\n%!" !i;*)
  List.rev !l, t

let reset () =
  Predictor.reset ();
  Dict.reset ();
  Newline.reset ()

let encode inps inpi buf =
  let rec aux = function
    | [] -> assert false
    | (idx, enc) :: next ->
        try
          let (l, t, i, s) = enc inps inpi in
          (l, t, idx + i, s)
        with Invalid -> aux next in
  let (l, t, i, s) = aux encode_categories in
  assert (l > 0);
  if !Predictor.delayed <> Predictor.query t then
    begin
      Buffer.add_char buf (Base64.encode (if !Predictor.delayed then 1 else 0));
      ignore (Predictor.update (if !Predictor.delayed then Predictor.Sp else Predictor.Nil))
    end;
  ignore (Predictor.update t);
  Predictor.delayed := false;
  Buffer.add_char buf (Base64.encode i);
  Buffer.add_string buf s;
  l

(* The encoded text uses only the characters from the base64 encoding
   (but is not base64-encoded for the most part). The first character
   stores the version number. Then comes a sequence of chunks. The first
   character of a chunk is its category (hence, up to 64 categories). The
   size of a chunk depends of the category. *)

let version = 0

let encode input =
  reset ();
  let l = String.length input in
  let buf = Buffer.create 1024 in
  Buffer.add_char buf (Base64.encode version);
  let i = ref 0 in
  while !i < l do
    if input.[!i] = ' ' then
      if !Predictor.delayed then
        begin
          decr i;
          Predictor.delayed := false;
          i := !i + encode input !i buf
        end
      else
        begin
          incr i;
          Predictor.delayed := true
        end
    else
      i := !i + encode input !i buf
  done;
  if !Predictor.delayed then
    Buffer.add_char buf (Base64.encode 1);
  Buffer.contents buf

let decode input =
  reset ();
  let inpl = String.length input in
  if inpl = 0 then "" else
  let buf = Buffer.create 1024 in
  if Base64.decode input.[0] <> version then invalid_arg "decode";
  let i = ref 1 in
  while !i < inpl do
    let cat = Base64.decode input.[!i] in
    let (l, m, s) = decode_categories.(cat) input (!i + 1) in
    if Predictor.update m then Buffer.add_char buf ' ';
    Buffer.add_string buf s;
    i := !i + 1 + l
  done;
  Buffer.contents buf

(*
let () =
  let inp =
    let buf = Buffer.create 1024 in
    try
      while true do Buffer.add_channel buf stdin 1024; done;
      assert false
    with End_of_file -> Buffer.contents buf in
  let enc = encode inp in
  print_endline enc;
  let dec = decode enc in
  (*print_endline dec;*)
  exit (if String.equal inp dec then 0 else 1)
*)
