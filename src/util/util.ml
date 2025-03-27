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

(* useful combinators *)

let const f _ = f

let const2 f _ _ = f

let const3 f _ _ _ = f

let flip f x y = f y x

(* useful iterator on int *)
let rec foldi f acc min max =
  if min > max then acc else foldi f (f acc min) (succ min) max

let mapi f = foldi (fun acc i -> f i::acc) []

(* useful iterator on float *)
let rec iterf f min max step =
  if min > max then () else
    (f min; iterf f (min+.step) max step)

(* boolean fold accumulators *)

exception FoldSkip

let all_fn pr = (fun _ x -> pr x || raise FoldSkip)
let any_fn pr = (fun _ x -> pr x && raise FoldSkip)

let all2_fn pr = (fun _ x y -> pr x y || raise FoldSkip)
let any2_fn pr = (fun _ x y -> pr x y && raise FoldSkip)

type ('z,'a,'c) fold = ('z -> 'a -> 'z) -> 'z -> 'c -> 'z

let all fold pr x = try fold (all_fn pr) true x with FoldSkip -> false
let any fold pr x = try fold (any_fn pr) false x with FoldSkip -> true

type ('z,'a,'b,'c,'d) fold2 = ('z -> 'a -> 'b -> 'z) -> 'z -> 'c -> 'd -> 'z

let all2 fold pr x y = try fold (all2_fn pr) true x y with FoldSkip -> false
let any2 fold pr x y = try fold (any2_fn pr) false x y with FoldSkip -> true

type ('z,'a,'b,'c) foldd =
  ('z -> 'a -> 'z) -> ('z -> 'b -> 'z) -> 'z -> 'c -> 'z

let alld fold pr1 pr2 x =
  try fold (all_fn pr1) (all_fn pr2) true x with FoldSkip -> false

let anyd fold pr1 pr2 x =
  try fold (any_fn pr1) (any_fn pr2) false x with FoldSkip -> true

(* constant boolean function *)
let ttrue _ = true
let ffalse _ = false

type _ cmptr = Cmptr : {proj: 'a -> 'b; cmp: 'b -> 'b -> int} -> 'a cmptr

type 'a compare = 'a -> 'a -> int

let cmptr proj cmp = Cmptr {proj; cmp}

let cmptr_direct cmp = Cmptr {cmp; proj= fun x -> x}

let rec cmp ls x y = match ls with
  | [] -> 0
  | Cmptr c :: ls ->
      match c.cmp (c.proj x) (c.proj y) with
      | 0 -> cmp ls x y
      | n -> n

let rec cmp_lists ls l1 l2 = match l1, l2 with
  | h1::t1, h2::t2 ->
      let ls = [cmptr fst (cmp ls); cmptr snd (cmp_lists ls)] in
      cmp ls (h1, t1) (h2, t2)
  | [], _ -> -1 | _, [] -> 1

let terminal_has_color =
  let term = try Sys.getenv "TERM" with Not_found -> "" in
  term <> "" && term <> "dumb" && Unix.isatty Unix.stdout

let esc_seq_of_tag str =
  let str = match str with Format.String_tag str -> str | _ -> assert false in
  let tokens = String.split_on_char ' ' (String.lowercase_ascii str) in
  let bold, tokens = match tokens with
    | "bold" :: tokens -> true, tokens
    | tokens -> false, tokens in
  let fg, bg = match tokens with
    | [] -> None, None
    | [fg] -> Some fg, None
    | ["on"; bg] -> None, Some bg
    | [fg; "on"; bg] -> Some fg, Some bg
    | _ -> Format.ksprintf failwith
             "ANSI format tag must be <[bold] [<color>] [on <bg-color>]>, not %s" str in
  let code = function
    | "black" -> 0 | "red"     -> 1 | "green" -> 2 | "yellow" -> 3
    | "blue"  -> 4 | "magenta" -> 5 | "cyan"  -> 6 | "white"  -> 7
    | s -> Format.ksprintf failwith "Unknown color in ANSI format tag: %s" s in
  let aux offset = function Some s -> [string_of_int (code s + offset)] | None -> [] in
  let bold = if bold then ["1"] else [] in
  String.concat ";" (aux 30 fg @ aux 40 bg @ bold)

let ansi_color_tags = Format.{
  mark_open_stag   = (fun tag -> sprintf "\027[%sm" (esc_seq_of_tag tag));
  mark_close_stag  = (fun _ -> "\027[0m");
  print_open_stag  = ignore;
  print_close_stag = ignore;
}

let iter_first (type a) iter f =
  let exception Found of a in
  let f x = match f x with Some y -> raise (Found y) | None -> () in
  try iter f; raise Not_found with Found y -> y

let get_home_dir () =
  try Sys.getenv "HOME"
  with Not_found ->
    (* try windows env var *)
    try Sys.getenv "USERPROFILE"
    with Not_found -> ""

let split_version s =
  let l = String.length s in
  let rec aux_num i t v =
    if i >= l then [t, v]
    else
      match s.[i] with
      | '0' .. '9' as c -> aux_num (i + 1) t (v * 10 + Char.code c - Char.code '0')
      | _ -> (t, v) :: aux_str (i + 1) i
  and aux_str i j =
    if i >= l then [String.sub s j (i - j), 0]
    else
      match s.[i] with
      | '0' .. '9' as c ->
          aux_num (i + 1) (String.sub s j (i - j)) (Char.code c - Char.code '0')
      | _ -> aux_str (i + 1) j in
  aux_str 0 0
