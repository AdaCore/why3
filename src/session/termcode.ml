(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Term
open Number
open Constant

(*******************************)
(*          explanations       *)
(*******************************)

let expl_prefixes = ref ["expl:";"infer:"]

let arg_extra_expl_prefix =
  ("--extra-expl-prefix",
   Arg.String (fun s -> expl_prefixes := s :: !expl_prefixes),
   "<s> register s as an additional prefix for VC explanations")

let opt_extra_expl_prefix =
  let open Getopt in
  KLong "extra-expl-prefix",
  Hnd1 (AString, fun s -> expl_prefixes := s :: !expl_prefixes),
  "<expl> register <expl> as an additional prefix\nfor VC explanations"

let collect_expls attr =
  Ident.Sattr.fold
    (fun attr acc ->
       let attr = attr.Ident.attr_string in
       let rec aux l =
         match l with
           | [] -> acc
           | p :: r ->
              try
                let s = Strings.remove_prefix p attr in s :: acc
              with Not_found -> aux r
       in aux !expl_prefixes)
    attr
    []

let concat_expls = function
  | [] -> None
  | [l] -> Some l
  | l :: ls -> Some (l ^ " (" ^ String.concat ". " ls ^ ")")

let search_attrs callback =
  let rec aux acc f =
    if f.t_ty <> None then acc
    else if Ident.Sattr.mem Term.stop_split f.Term.t_attrs then acc
    else
      let res = callback f.Term.t_attrs in
      if res = [] then match f.t_node with
        | Term.Ttrue | Term.Tfalse | Term.Tapp _ -> acc
        | Term.Tbinop (Term.Timplies, _, f) -> aux acc f
        | Term.Tlet _ | Term.Tcase _ | Term.Tquant (Term.Tforall, _) ->
          Term.t_fold aux acc f
        | _ -> raise Exit
      else if acc = [] then res
      else raise Exit
  in
  aux []

let get_expls_fmla =
  let search = search_attrs collect_expls in
  fun f -> try search f with Exit -> []

let goal_expl_task ~root task =
  let gid = (Task.task_goal task).Decl.pr_name in
  let info =
    let res = get_expls_fmla (Task.task_goal_fmla task) in
    concat_expls
      (if res <> [] && not root
       then res
       else collect_expls gid.Ident.id_attrs)
  in
  let info =
    match info with
      | Some i -> i
      | None -> ""
  in
  gid, info, task

(* {2 ident dictionaries for shapes} *)

(*
let dict_table = Hashtbl.create 17
let dict_count = ref 0
let reverse_ident_table = Hashtbl.create 17
let reverse_dict_count = ref 0

let reset_dict () =
  Hashtbl.clear dict_table;
  Hashtbl.clear reverse_ident_table;
  dict_count := 0;
  reverse_dict_count := 0
 *)

(* {3 direct table to read shapes from strings} *)

(*
let get_name s b i =
  try while !i < String.length s do
    match String.get s !i with
      | ')' -> incr i; raise Exit
      | c -> incr i; Buffer.add_char b c
    done;
    invalid_arg "Termcode.get_name: missing closing parenthesis"
  with Exit ->
    let id = Buffer.contents b in
    Hashtbl.add dict_table !dict_count id;
(*
    Format.eprintf "%d -> %s@." !dict_count id;
*)
    incr dict_count;
    id

let get_num s n i =
  try while !i < String.length s do
    match String.get s !i with
      | ')' -> incr i; raise Exit
      | '0'..'9' as c ->
        incr i; n := !n * 10 + (Char.code c - Char.code '0')
      | _ ->
        invalid_arg "Termcode.get_num: decimal digit expected"
    done;
    invalid_arg "Termcode.get_num: missing closing parenthesis"
  with Exit ->
    try Hashtbl.find dict_table !n
    with Not_found ->
      invalid_arg
        ("Termcode.get_num: invalid ident number " ^ string_of_int !n)
      *)

(*
let get_id s i =
  if !i >= String.length s then
    invalid_arg "Termcode.get_id: missing closing parenthesis";
  match String.get s !i with
    | '0'..'9' as c ->
      let n = ref (Char.code c - Char.code '0') in
      incr i;
      get_num s n i
    | ')' -> invalid_arg "Termcode.get_id: unexpected closing parenthesis"
    | c ->
      let b = Buffer.create 17 in
      Buffer.add_char b c;
      incr i;
      get_name s b i
*)

(*
let store_id s i =
  let b = Buffer.create 17 in
  try while !i < String.length s do
    match String.get s !i with
      | ')' -> incr i; raise Exit
      | c -> incr i; Buffer.add_char b c
    done;
    invalid_arg "Termcode.store_id: missing closing parenthesis"
  with Exit ->
    let id = Buffer.contents b in
    try
      let n = Hashtbl.find reverse_ident_table id in
      string_of_int n
    with
        Not_found ->
          Hashtbl.add reverse_ident_table id !reverse_dict_count;
          incr reverse_dict_count;
          id
*)

module Common = struct

let sign fmt n =
  if n then Format.pp_print_char fmt '-'

let const_v1 fmt c =
  match c with
  | ConstInt { il_kind=k; il_int=i } ->
      sign fmt (BigInt.lt i BigInt.zero);
      let i = BigInt.abs i in
      begin match k with
      | ILitUnk | ILitDec -> Format.pp_print_string fmt (BigInt.to_string i)
      | ILitHex -> Format.fprintf fmt "0x%a" (Number.print_in_base 16 None) i
      | ILitOct -> Format.fprintf fmt "0o%a" (Number.print_in_base 8 None) i
      | ILitBin -> Format.fprintf fmt "0b%a" (Number.print_in_base 2 None) i
      end
  | ConstReal { rl_kind=k; rl_real={ rv_sig=i; rv_pow2=p2; rv_pow5=p5 } } ->
      (* not the actual encoding *)
      sign fmt (BigInt.lt i BigInt.zero);
      let i = BigInt.abs i in
      begin match k with
      | RLitUnk | RLitDec _ ->
          Format.fprintf fmt "%s.0e%sp%s"
            (BigInt.to_string i) (BigInt.to_string p5) (BigInt.to_string p2)
      | RLitHex _ ->
          Format.fprintf fmt "%a.0p%se%s"
            (Number.print_in_base 16 None) i (BigInt.to_string p2) (BigInt.to_string p5)
      end
  | ConstStr c ->
      print_string_def fmt c

let const_v2 fmt c =
  match c with
  | ConstInt { il_kind=_; il_int=i } ->
      Format.pp_print_string fmt (BigInt.to_string i)
  | ConstReal { rl_kind=_; rl_real={ rv_sig=i; rv_pow2=p2; rv_pow5=p5 } } ->
      Format.fprintf fmt "%s.p%se%s"
        (BigInt.to_string i) (BigInt.to_string p2) (BigInt.to_string p5)
  | ConstStr c ->
      print_string_def fmt c

end

(* {2 Shapes} *)

type shape = string

type bound_shape = int list

type sum_shape_version = SV1 | SV2 | SV3 | SV4 | SV5 | SV6

let current_sum_shape_version = SV6

exception InvalidShape

let string_to_sum_shape_version n =
  match n with
  | "1" -> SV1 | "2" -> SV2 | "3" -> SV3 | "4" -> SV4 | "5" -> SV5 | "6" -> SV6
  | _ -> raise InvalidShape

let string_of_sum_shape_version n =
  match n with
  | SV1 -> "1" | SV2 -> "2" | SV3 -> "3" | SV4 -> "4" | SV5 -> "5" | SV6 -> "6"

let pp_sum_shape_version fmt v =
  Format.pp_print_string fmt (string_of_sum_shape_version v)

let is_bound_sum_shape_version v =
    match v with
    | SV1 | SV2 | SV3 | SV4 | SV5 -> false
    | SV6 -> true

type shape_v =
  | Old_shape of shape
  | Bound_shape of bound_shape

let string_of_shape sv =
  match sv with
  | Old_shape s -> s
  | Bound_shape l ->
      Format.asprintf "%a" (Pp.print_list (Pp.constant_string "H") Pp.int) l

let shape_of_string =
  let cache = ref [] in
  fun ~version s ->
  if is_bound_sum_shape_version version then
    let s = Strings.rev_split 'H' s in
    (* most consecutive shapes have very long common suffixes,
       so we look for some sharing with the previously computed shape
       in order to reduce the memory footprint of large sessions *)
    let c, lc =
      let lc = List.length !cache in
      let ls = List.length s in
      (* this avoids reverting a uselessly long list below *)
      if lc > ls then Lists.chop (lc - ls) !cache, ls
      else !cache, lc in
    let rec aux c s n =
      match c, s with
      | hc :: tc, hs :: ts ->
          begin match int_of_string hs with
          | x -> if x = hc then aux tc ts (n + 1) else (n, s)
          | exception _ -> aux c ts n
          end
      | _, _ -> (n, s) in
    let (common, remaining) = aux (List.rev c) s 0 in
    let common = Lists.chop (lc - common) c in
    let s = List.fold_left (fun acc x ->
        try int_of_string x :: acc with
        | _ -> acc) common remaining in
    cache := s;
    Bound_shape s
  else
    Old_shape s

let empty_shape = ""

let empty_bound_shape = []

let debug = Debug.register_info_flag "session_pairing"
  ~desc:"Print@ debugging@ messages@ about@ reconstruction@ of@ \
         session@ trees@ after@ modification@ of@ source@ files."

module Shape = struct

(* similarity code of terms, or of "shapes"

example:

  shape(forall x:int, x * x >= 0) =
         Forall(Int,App(infix_gteq,App(infix_st,Tvar 0,Tvar 0),Const(0)))
       i.e: de bruijn indexes, first-order term

*)

let tag_and = 'A'
let tag_app = 'a'
let tag_case = 'C'
let tag_const = 'c'
let tag_exists = 'E'
let tag_eps = 'e'
let tag_forall = 'F'
let tag_false = 'f'
let tag_impl = 'I'
let tag_if = 'i'
let tag_let = 'L'
let tag_not = 'N'
let tag_or = 'O'
let tag_iff = 'q'
let tag_true = 't'
let tag_var = 'V'
let tag_wild = 'w'
let tag_as = 'z'

exception ShapeTooLong

let shape_buffer = Buffer.create 17

let check () =
  if Buffer.length shape_buffer >= 1024 then raise ShapeTooLong

let push s =
  Buffer.add_string shape_buffer s;
  check ()

let pushc c =
  Buffer.add_char shape_buffer c;
  check ()

(* Remove infix and mixfix. (prefix should be rare enough) *)
let decoded pr id =
  Ident.(match sn_decode id.id_string with
  | SNword _ -> Ident.id_unique pr id
  | SNinfix s | SNtight s | SNprefix s | SNget s | SNset s
  | SNupdate s | SNcut s | SNlcut s | SNrcut s -> s)

let ident_v4 h id =
  let x =
    try Ident.Mid.find id !h
    with Not_found ->
      let s = id.Ident.id_string in
      h := Ident.Mid.add id s !h; s
  in
  push x

let ident_v5 pr h id =
  let x =
    try Ident.Mid.find id !h
    with Not_found ->
      let s = decoded pr id in
      h := Ident.Mid.add id s !h; s
  in
  push x

let vs_rename_alpha c h vs =
  incr c;
  let s = string_of_int !c in
  h := Ident.Mid.add vs.vs_name s !h

let vl_rename_alpha c h vl = List.iter (vs_rename_alpha c h) vl

let rec pat_rename_alpha c h p = match p.pat_node with
  | Pvar v -> vs_rename_alpha c h v
  | Pas (p, v) -> vs_rename_alpha c h v; pat_rename_alpha c h p
  | Por (p, _) -> pat_rename_alpha c h p
  | _ -> Term.pat_fold (fun () -> pat_rename_alpha c h) () p

(*
let id_string_shape id = push id

let ident_shape id = id_string_shape id.Ident.id_string
*)

let const_shape v c =
  let fmt = Format.formatter_of_buffer shape_buffer in
  begin match v with
  | SV1 | SV2 | SV3 | SV4 | SV5 -> Common.const_v1 fmt c
  | SV6 -> Common.const_v2 fmt c
  end;
  Format.pp_print_flush fmt ();
  check ()

let ident_shape v pr m id =
  match v with
  | SV1 | SV2 | SV3 | SV4 | SV5 -> ident_v4 m id
  | SV6 -> ident_v5 pr m id

let rec pat_shape ~version pr c m p : 'a =
  match p.pat_node with
    | Pwild -> pushc tag_wild
    | Pvar _ -> pushc tag_var
    | Papp (f, l) ->
        pushc tag_app;
        ident_shape version pr m f.ls_name;
        List.iter (pat_shape ~version pr c m) l
    | Pas (p, _) -> pat_shape ~version pr c m p; pushc tag_as
    | Por (p, q) ->
       pat_shape ~version pr c m q; pushc tag_or; pat_shape ~version pr c m p

let rec t_shape ~version pr c m t =
  let fn = t_shape ~version pr c m in
  match t.t_node with
    | Tconst c -> pushc tag_const; const_shape version c
    | Tvar v -> pushc tag_var; ident_shape version pr m v.vs_name
    | Tapp (s,l) ->
        pushc tag_app;
        ident_shape version pr m s.ls_name;
        List.iter fn l
    | Tif (f,t1,t2) ->
      begin match version with
      | SV1 | SV2 -> pushc tag_if; fn f; fn t1; fn t2
      | SV3 | SV4 | SV5 | SV6 -> pushc tag_if; fn t2; fn t1; fn f
      end
    | Tcase (t1,bl) ->
        let br_shape b =
          let p,t2 = t_open_branch b in
          match version with
          | SV1 | SV2 ->
            pat_shape ~version pr c m p;
            pat_rename_alpha c m p;
            fn t2
          | SV3 | SV4 | SV5 | SV6 ->
            pat_rename_alpha c m p;
            fn t2;
            pat_shape ~version pr c m p
        in
        begin match version with
        | SV1 | SV2 ->
                 pushc tag_case;
                 fn t1;
                 List.iter br_shape bl
        | SV3 | SV4 | SV5 | SV6->
           pushc tag_case;
           List.iter br_shape bl;
           fn t1
        end
    | Teps b ->
        pushc tag_eps;
        let u,f = t_open_bound b in
        vs_rename_alpha c m u;
        fn f
    | Tquant (q,b) ->
        let vl,triggers,f1 = t_open_quant b in
        vl_rename_alpha c m vl;
        (* argument first, intentionally, to give more weight on A in
           forall x,A *)
        fn f1;
        let hq = match q with Tforall -> tag_forall | Texists -> tag_exists in
        pushc hq;
        List.iter (fun trigger -> List.iter fn trigger) triggers
    | Tbinop (o,f,g) ->
       (* g first, intentionally, to give more weight on B in A->B *)
       fn g;
       let tag = match o with
         | Tand -> tag_and
         | Tor -> tag_or
         | Timplies -> tag_impl
         | Tiff -> tag_iff
       in
       pushc tag;
       fn f
    | Tlet (t1,b) ->
        let u,t2 = t_open_bound b in
        vs_rename_alpha c m u;
        begin
          match version with
            | SV1 ->
                pushc tag_let; fn t1; fn t2
            | SV2 | SV3 | SV4 | SV5 | SV6 ->
                (* t2 first, intentionally *)
                fn t2; pushc tag_let; fn t1
        end
    | Tnot f ->
      begin match version with
      | SV1 | SV2 -> fn f; pushc tag_not
      | SV3 | SV4 | SV5 | SV6 -> pushc tag_not; fn f
      end
    | Ttrue -> pushc tag_true
    | Tfalse -> pushc tag_false

let t_shape_task ~version ~expl t =
  Buffer.clear shape_buffer;
  let pr = Ident.create_ident_printer [] in
  let f = Task.task_goal_fmla t in
  let c = ref (-1) in
  let m = ref Ident.Mid.empty in
  let () =
    try
      (* expl *)
      begin match version with
      | SV1 | SV2 -> ()
      | SV3 | SV4 | SV5 | SV6 -> push expl end;
      (* goal shape *)
      t_shape ~version pr c m f;
      (* All declarations shape *)
      begin match version with
      | SV1 | SV2 | SV3 | SV4 -> ()
      | SV5 | SV6 ->
         let open Decl in
         let do_td td = match td.Theory.td_node with
           | Theory.Decl d ->
              begin match d.d_node with
              | Dparam _ls -> ()
              | Dprop (_, _pr, f) ->
                  t_shape ~version pr c m f
              | _ -> ()
              end
           | _ -> () in
         let _, prev = Task.task_separate_goal t in
         Task.task_iter do_td prev
      end
    with ShapeTooLong -> ()
  in
  Buffer.contents shape_buffer

end

module Gshape = struct

  open Wstdlib

  (* [hyp_shape] associate a shape to its index in the file;
     [index_sh] associate an index to a shape;
     [n] is the last shape variable *)
  type gshape = { mutable hyp_shape: int Mstr.t;
                  mutable index_sh: string Mint.t;
                  mutable n: int }

  let create () =
    { hyp_shape = Mstr.empty;
      index_sh = Mint.empty;
      n = 0 }

  let copy from_s to_s =
    to_s.hyp_shape <- from_s.hyp_shape;
    to_s.index_sh <- from_s.index_sh;
    to_s.n <- from_s.n

  let clear_gs gs =
    gs.hyp_shape <- Mstr.empty;
    gs.index_sh <- Mint.empty;
    gs.n <- 0

  let add_shape gs s =
    try Mstr.find s gs.hyp_shape with
    | Not_found ->
        gs.hyp_shape <- Mstr.add s gs.n gs.hyp_shape;
        gs.index_sh  <- Mint.add gs.n s gs.index_sh;
        gs.n <- gs.n + 1;
        gs.n - 1

  let add_and_prepend gs current_shape s : unit =
    (* Do not save empty: could be confused with end of assingments (TODO to be improved)  *)
    if s = "" then () else
      current_shape := add_shape gs s :: !current_shape

  let add_shape_g gs s =
    let (_: int) = add_shape gs s in ()

  let write_shape_to_file s csh =
    Mint.iter (fun _ s -> Compress.Compress_z.output_string csh s;
                Compress.Compress_z.output_string csh "\n")
      s.index_sh

  let goal_and_expl_shapes (gs: gshape) li =
    try
      match li with
      | expl :: goal :: _ ->
          Mint.find expl gs.index_sh ^ Mint.find goal gs.index_sh
      | _ ->
          ""
    with Not_found -> ""

  let t_bound_shape_task gs ~version ~expl t =
    assert (is_bound_sum_shape_version version);
    let current_shape = ref [] in
    Buffer.clear Shape.shape_buffer;
    let pr = Ident.create_ident_printer [] in
    let c = ref (-1) in
    let m = ref Ident.Mid.empty in
    (* All declarations shape *)
    let local_decls =
      let ut = Task.used_symbols (Task.used_theories t) in
      Task.local_decls t ut in
    let open Decl in
    let do_d d =
      match d.d_node with
      | Dparam _ls -> ()
      | Dprop (_, _pr, f) ->
          let sh =
            (try Shape.t_shape ~version pr c m f with Shape.ShapeTooLong -> ());
            Buffer.contents Shape.shape_buffer in
          Buffer.clear Shape.shape_buffer;
          add_and_prepend gs current_shape sh
      | _ -> () in
    List.iter do_d local_decls;
    (* TODO don't save empty shapes as \n as it could be confused with end of assignments *)
    let expl = if expl = "" then "empty_shape" else expl in
    add_and_prepend gs current_shape expl;
    (* The order should be [|shape|] :: [|goal|] :: [|rest of decl|] *)
    !current_shape

  let empty_bshape = []

end

let t_shape_task ~version ~expl t =
  if is_bound_sum_shape_version version then empty_shape else
  Shape.t_shape_task ~version ~expl t

(* Checksums *)

type checksum = string
let print_checksum = Format.pp_print_string
let string_of_checksum x = x
let checksum_of_string x = x
let equal_checksum x y = (x : checksum) = y
let dumb_checksum = ""

let buffer_checksum b =
  let s = Buffer.contents b in
  Digest.to_hex (Digest.string s)

module Checksum = struct

  let char (_,_,_,buf) c = Buffer.add_char buf c
  let int (_,_,_,buf as b) i =
    char b 'i'; Buffer.add_string buf (string_of_int i)
  let string (_,_,_,buf as b) s =
    char b '"'; Buffer.add_string buf (String.escaped s); char b '"'
  let option e b = function None -> char b 'n' | Some x -> char b 's'; e b x
  let list e b l = char b '['; List.iter (e b) l; char b ']'

  let ident_v1, clear_ident_v1 =
    let hident = Ident.Hid.create 17 in
    let c = ref 0 in
    (fun b id ->
      int b (try Ident.Hid.find hident id
        with Not_found -> incr c; Ident.Hid.add hident id !c; !c)),
    (fun () -> Ident.Hid.clear hident; c := 0)

  let ident_v2 (_,c,m,_ as b) id =
    let i = match Ident.Mid.find_opt id !m with
      | Some i -> i
      | None -> incr c; m := Ident.Mid.add id !c !m; !c
    in
    int b i

  let ident (v,_,_,_ as b) id = match v with
    | SV1 | SV2 | SV3 -> ident_v1 b id
    | SV4 | SV5 | SV6 -> ident_v2 b id

  let const (v,_,_,buf) c =
    let fmt = Format.formatter_of_buffer buf in
    begin match v with
    | SV1 | SV2 | SV3 | SV4 | SV5 -> Common.const_v1 fmt c
    | SV6 -> Common.const_v2 fmt c
    end;
    Format.pp_print_flush fmt ()

  let tvsymbol b tv = ident b tv.Ty.tv_name

  let rec ty b t = match t.Ty.ty_node with
    | Ty.Tyvar tv -> char b 'v'; tvsymbol b tv
    | Ty.Tyapp (ts, tyl) -> char b 'a'; ident b ts.Ty.ts_name; list ty b tyl

  let vsymbol (v,_,_,_ as b) vs = match v with
    | SV1 | SV2 | SV3 -> ty b vs.vs_ty
    | SV4 | SV5 | SV6 -> ident b vs.vs_name; ty b vs.vs_ty

  (* start: _ V ident a o *)
  let rec pat b p = match p.pat_node with
    | Pwild -> char b '_'
    | Pvar vs -> char b 'v'; vsymbol b vs
    | Papp (f, l) -> char b 'a'; ident b f.ls_name; list pat b l
    | Pas (p, vs) -> char b 's'; pat b p; vsymbol b vs
    | Por (p, q) -> char b 'o'; pat b p; pat b q

  (* start: c V v i m e F E A O I q l n t f *)
  let rec term b t = match t.t_node with
    | Tconst c -> const b c
    | Tvar v -> char b 'v'; ident b v.vs_name
    | Tapp (s, l) -> char b 'a'; ident b s.ls_name; list term b l
    | Tif (f, t1, t2) -> char b 'i'; term b f; term b t1; term b t2
    | Tcase (t1, bl) ->
        let branch b br =
          let p, t2 = t_open_branch br in
          pat b p; term b t2
        in
        char b 'm'; term b t1; list branch b bl
    | Teps bf ->
        let vs, f = t_open_bound bf in
        char b 'e'; vsymbol b vs; term b f
    | Tquant (q, bf) ->
        let vl, triggers, f1 = t_open_quant bf in
        char b (match q with Tforall -> 'F' | Texists -> 'E');
        list vsymbol b vl;
        list (list term) b triggers;
        term b f1
    | Tbinop (o, f, g) ->
        let tag = match o with
          | Tand -> 'A'
          | Tor -> 'O'
          | Timplies -> 'I'
          | Tiff -> 'q'
        in
        char b tag; term b f; term b g
    | Tlet (t1, bt) ->
        let vs, t2 = t_open_bound bt in
        char b 'l'; vsymbol b vs; term b t1;
        term b t2
    | Tnot f -> char b 'n'; term b f
    | Ttrue -> char b 't'
    | Tfalse -> char b 'f'

  let tysymbol b ts =
    ident b ts.Ty.ts_name;
    list tvsymbol b ts.Ty.ts_args;
    match ts.Ty.ts_def with
    | Ty.NoDef   -> char b 'n'
    | Ty.Alias x -> char b 's'; ty b x
    | Ty.Range _ -> char b 'r' (* FIXME *)
    | Ty.Float _ -> char b 'f' (* FIXME *)

  let lsymbol b ls =
    ident b ls.ls_name;
    list ty b ls.ls_args;
    option ty b ls.ls_value;
    int b ls.ls_constr

  (* start: T G F D R L I P (C M) *)
  let decl b d = match d.Decl.d_node with
    | Decl.Dtype ts ->
        char b 'T'; tysymbol b ts
    | Decl.Ddata ddl ->
        let constructor b (ls, l) = lsymbol b ls; list (option lsymbol) b l in
        let data_decl b (ts, cl) = tysymbol b ts; list constructor b cl in
        char b 'D'; list data_decl b ddl
    | Decl.Dparam ls ->
        char b 'R'; lsymbol b ls
    | Decl.Dlogic ldl ->
        let logic_decl b (ls, defn) =
          lsymbol b ls;
          let vl, t = Decl.open_ls_defn defn in
          list vsymbol b vl;
          term b t
        in
        char b 'L'; list logic_decl b ldl
    | Decl.Dind (s, idl) ->
        let clause b (pr, f) =
          ident b pr.Decl.pr_name; term b f in
        let ind_decl b (ls, cl) = lsymbol b ls; list clause b cl in
        char b 'I'; char b (match s with Decl.Ind -> 'i' | Decl.Coind -> 'c');
        list ind_decl b idl
    | Decl.Dprop (k,n,t) ->
        let tag = match k with
          | Decl.Plemma -> "PL"
          | Decl.Paxiom -> "PA"
          | Decl.Pgoal  -> "PG"
        in
        string b tag;
        ident b n.Decl.pr_name;
        term b t

  let meta_arg_type b = function
    | Theory.MTty       -> char b 'y'
    | Theory.MTtysymbol -> char b 't'
    | Theory.MTlsymbol  -> char b 'l'
    | Theory.MTprsymbol -> char b 'p'
    | Theory.MTstring   -> char b 's'
    | Theory.MTint      -> char b 'i'
    | Theory.MTid    -> char b 'd'

  let meta b m =
    string b m.Theory.meta_name;
    list meta_arg_type b m.Theory.meta_type;
    char b (if m.Theory.meta_excl then 't' else 'f')

  let meta_arg b = function
    | Theory.MAty t  -> char b 'y'; ty b t
    | Theory.MAts ts -> char b 't'; ident b ts.Ty.ts_name
    | Theory.MAls ls -> char b 'l'; ident b ls.ls_name
    | Theory.MApr pr -> char b 'p'; ident b pr.Decl.pr_name
    | Theory.MAstr s -> char b 's'; string b s
    | Theory.MAint i -> char b 'i'; int b i
    | Theory.MAid i -> char b 'd'; ident b i

  let tdecl b d = match d.Theory.td_node with
    | Theory.Decl d -> decl b d
    | Theory.Use th
    | Theory.Clone (th, _) ->
        char b 'C'; ident b th.Theory.th_name; list string b th.Theory.th_path
    | Theory.Meta (m, mal) -> char b 'M'; meta b m; list meta_arg b mal

(* not used anymore

  NOTE: if we come back to checksumming theories, use the separate recursive
        [tdecl] function for it. [Use] in a theory requires a recursive call
        (as below), [Use] in a task is just a witness declaration.

  let rec tdecl b d = match d.Theory.td_node with
    | Theory.Decl d -> decl b d
    | Theory.Use th ->
      char b 'U'; ident b th.Theory.th_name; list string b th.Theory.th_path;
      string b (theory_v2 th)
    | Theory.Clone (th, _) ->
        char b 'C'; ident b th.Theory.th_name; list string b th.Theory.th_path
    | Theory.Meta (m, mal) -> char b 'M'; meta b m; list meta_arg b mal

  and theory_v2_aux t =
    let c = ref 0 in
    let m = ref Ident.Mid.empty in
    let b = Buffer.create 8192 in
    List.iter (tdecl (CV2,c,m,b)) t.Theory.th_decls;
    let dnew = Digest.string (Buffer.contents b) in
    Digest.to_hex dnew

  and theory_v2 =
    let table = Ident.Wid.create 17 in
    fun t ->
      try Ident.Wid.find table t.Theory.th_name
      with Not_found ->
        let v = theory_v2_aux t in
        Ident.Wid.set table t.Theory.th_name v;
        v

  let theory ~version t = match version with
    | CV1 -> assert false
    | CV2 -> theory_v2 t
 *)

  let task_v1 =
    let c = ref 0 in
    let m = ref Ident.Mid.empty in
    let b = Buffer.create 8192 in
    fun t ->
      Task.task_iter (tdecl (SV1,c,m,b)) t;
      clear_ident_v1 ();
      let dnew = Digest.string (Buffer.contents b) in
      Buffer.clear b;
      Digest.to_hex dnew

  let task_v2 =
    let c = ref 0 in
    let m = ref Ident.Mid.empty in
    let b = Buffer.create 8192 in
    let task_hd t (cold,mold,dold) =
      c := cold;
      m := mold;
      tdecl (SV4,c,m,b) t.Task.task_decl;
      Buffer.add_string b (Digest.to_hex dold);
      let dnew = Digest.string (Buffer.contents b) in
      Buffer.clear b;
      let mnew = match t.Task.task_decl.Theory.td_node with
        | Theory.Decl { Decl.d_news = s } ->
            Ident.Sid.fold (fun id a ->
              Ident.Mid.add id (Ident.Mid.find id !m) a) s mold
        | _ -> !m in
      !c, mnew, dnew
    in
    let tr = Trans.fold task_hd (0, Ident.Mid.empty, Digest.string "") in
    fun t ->
      let _,_,dnew = Trans.apply tr t in
      Digest.to_hex dnew

  module DMid = Diffmap.MakeOfMap (Ident.Mid)

  (* WARNING: The occurence of [Trans.fold] in [task_v3] needs to be executed
     once at initialization in order for all the applications of this
     transformation to share the same Wtask ([h] created on first line of
     [Trans.fold]). In short, the closure is here just so that Trans.fold is
     executed once and shared for all functions.
     So, in particular, don't add arguments to task_v3 here. *)
  let task_v3 =
    let c = ref 0 in
    let m = ref Ident.Mid.empty in
    let b = Buffer.create 8192 in
    let task_hd t (cold,mold,dold) =
      c := cold;
      let mo = DMid.get mold in
      m := mo;
      tdecl (SV6,c,m,b) t.Task.task_decl;
      Buffer.add_string b (Digest.to_hex dold);
      let dnew = Digest.string (Buffer.contents b) in
      Buffer.clear b;
      let mnew = match t.Task.task_decl.Theory.td_node with
        | Theory.Decl { Decl.d_news = s } ->
            (* as metas might be have been put on some symbols before their
               declaration, ignore such symbols *)
            let s = Ident.Mid.set_diff s mo in
            Ident.Mid.mapi (fun id () -> Ident.Mid.find id !m) s
        | _ -> Ident.Mid.set_diff !m mo in
      !c, DMid.union mold mnew, dnew
    in
    let tr = Trans.fold task_hd (0, DMid.empty (), Digest.string "") in
    fun t ->
      let _,_,dnew = Trans.apply tr t in
      Digest.to_hex dnew

  let task ~version t = match version with
    | SV1 | SV2 | SV3 -> task_v1 t
    | SV4 | SV5  -> task_v2 t
    | SV6 -> task_v3 t

end

(*
let time = ref 0.0
 *)

let task_checksum ?(version=current_sum_shape_version) t =
(*
  let version = match version with
    | SV1 | SV2 | SV3 -> CV1
    | 4 | 5 -> CV2
    | 6 -> CV3
    | _ -> assert false (* FIXME !!! *)
  in
 *)
  (*
  let tim = Unix.gettimeofday () in
*)
  let s = Checksum.task ~version t in
(*
  let tim = Unix.gettimeofday () -. tim in
  time := !time +. tim;
  Format.eprintf "[Checksum times] %f/%f@." tim !time;
*)
  s

(*************************************************************)
(* Pairing of new and old subgoals                           *)
(*************************************************************)

(* we have an ordered list of new subgoals

     newgoals = [g1; g2; g3; ...]

   and a list of old subgoals

     oldgoals = [h1 ; h2 ; ... ]

   we build a list

     [g1, None; g2, Some (h3, false); g3, Some (h2, true); ...]

   where each new goal is mapped either to
   - None: no pairing at all
   - Some (h, false): exact matching (equal checksums)
   - Some (h, true): inexact matching (goal obsolete)
*)

module type S = sig
  type 'a t
  val checksum : 'a t -> checksum option
  val shape    : 'a t -> string * (int list)
  val name     : 'a t -> Ident.ident
end

module Pairing (Old: S)(New: S) = struct

  let rec lcp n s1 s2 =
    if String.length s1 <= n || String.length s2 <= n then n
    else if s1.[n] = s2.[n] then lcp (n+1) s1 s2 else n
  let lcp = lcp 0

  let rec count_same_sorted n l1 l2 =
    match l1, l2 with
    | hd1 :: tl1, hd2 :: _ when hd1 < hd2 ->
        count_same_sorted n tl1 l2
    | hd1 :: _, hd2 :: tl2 when hd1 > hd2 ->
        count_same_sorted n l1 tl2
    | hd1 :: tl1, hd2 :: tl2 when hd1 = hd2 ->
        count_same_sorted (n + 1) tl1 tl2
    | _ -> n

  let count_common sl1 sl2 =
    (* The lists are sorted in mk_node *)
    count_same_sorted 0 sl1 sl2

  (* An implicit invariant when comparing lists is that the session share part
     of their global_shape (int -> shape) because this global value is copied
     from old session to new session at the start of the merge process *)
  let lcp_list (sh1, sl1) (sh2, sl2) =
    (lcp sh1 sh2, count_common sl1 sl2)

  open Ident

  type goal_index = Old of int | New of int

  type ('a,'b) goal_table = {
    table_old : 'a Old.t array;
    table_new : 'b New.t array;
  }

  (* doubly linked lists; left and right bounds point to themselves *)

  type node = {
    mutable  prev: node;
            shape: string * (int list);
              elt: goal_index;
    mutable valid: bool;
    mutable  next: node;
  }

  let mk_node table g =
    let s = match g with
      | Old g ->
          let (sh, l) = Old.shape table.table_old.(g) in
          (* Sanitazing: sort the lists only once *)
          (sh, List.sort Int.compare l)
      | New g ->
          let (sh, l) = New.shape table.table_new.(g) in
          (* Sanitazing: sort the lists only once *)
          (sh, List.sort Int.compare l)
    in
    let rec n = { prev = n; shape = s; elt = g; next = n; valid = true }
    in n

  let rec iter_pairs f = function
    | [] | [_] -> ()
    | x :: (y :: _ as l) -> f x y; iter_pairs f l

  let build_list = iter_pairs (fun x y -> x.next <- y; y.prev <- x)

  let remove x =
    x.valid <- false;
    let p = x.prev and n = x.next in
    if p == x then n.prev <- n (* left bound *)
    else if n == x then p.next <- p (* right bound *)
    else begin p.next <- n; n.prev <- p end

  (* priority queues for pairs of nodes *)

  let dprintf = Debug.dprintf debug

  let associate oldgoals newgoals =
    let table = {
      table_old = Array.of_list oldgoals;
      table_new = Array.of_list newgoals;
    }
    in
    (* set up an array [result] containing the solution
       [new_goal_index g] returns the index of goal [g] in that array *)
    let new_goal_index = Hid.create 17 in
    let result =
      let make i newg =
        Hid.add new_goal_index (New.name newg) i; (newg, None)
      in
      Array.mapi make table.table_new
    in
    let new_goal_index newg =
      try Hid.find new_goal_index (New.name newg)
      with Not_found -> assert false in
    (* phase 1: pair goals with identical checksums *)
    let old_checksums = Hashtbl.create 17 in
    let old_goals_without_checksum =
      let acc =ref [] in
      for oldg = 0 to Array.length table.table_old - 1 do
        match Old.checksum table.table_old.(oldg) with
        | None -> acc := mk_node table (Old oldg) :: !acc
        | Some s -> Hashtbl.add old_checksums s oldg
      done;
      !acc
    in
    let newgoals =
      let acc = ref old_goals_without_checksum in
      (* in reverse order, since the hashtable acts like a LIFO *)
      for newi = Array.length table.table_new - 1 downto 0 do
        try
          let newg = table.table_new.(newi) in
          match New.checksum newg with
          | None -> raise Not_found
          | Some c ->
             let oldi = Hashtbl.find old_checksums c in
             let oldg = table.table_old.(oldi) in
             Hashtbl.remove old_checksums c;
             result.(new_goal_index newg) <- (newg, Some (oldg, false))
        with Not_found ->
          acc := mk_node table (New newi) :: !acc
      done;
      !acc
    in
    let add _ oldg acc = mk_node table (Old oldg) :: acc in
    let allgoals = Hashtbl.fold add old_checksums newgoals in
    Hashtbl.clear old_checksums;
    (* phase 2: pair goals according to shapes *)
    let compare e1 e2 = Pervasives.compare e1.shape e2.shape in
    let allgoals = List.sort compare allgoals in
    build_list allgoals;
    if allgoals <> [] then begin
      let module E = struct
        let dummy = let n = List.hd allgoals (* safe *) in (0, 0), (n, n)
        type t = (int * int) * (node * node)
        let compare ((u1,u2), _) ((v1,v2), _) =
          let c = Int.compare v1 u1 in
          if c <> 0 then c
          else Int.compare v2 u2
      end in
      let module PQ = Pqueue.Make(E) in
      let pq = PQ.create () in
      let add x y = match x.elt, y.elt with
        | Old _, New _ | New _, Old _ ->
            PQ.insert (lcp_list x.shape y.shape, (x, y)) pq
        | Old _, Old _ | New _, New _ -> () in
      iter_pairs add allgoals;
      (* FIXME: exit earlier, as soon as we get min(old,new) pairs *)
      while not (PQ.is_empty pq) do
        let _, (x, y) = PQ.extract_min_exn pq in
        if x.valid && y.valid then begin
          let o, n = match x.elt, y.elt with
            | New n, Old o | Old o, New n -> o, n | _ -> assert false in
          dprintf "[assoc] new pairing@.";
          let newg = table.table_new.(n) in
          let oldg = table.table_old.(o) in
          result.(new_goal_index newg) <- newg, Some (oldg, true);
          if x.prev != x && y.next != y then add x.prev y.next;
          remove x;
          remove y
        end
      done
    end;
    let detached =
      List.fold_left
        (fun acc x ->
         if x.valid then
           match x.elt with
           | Old g -> table.table_old.(g) :: acc
           | New _ -> acc
         else acc)
        [] allgoals
    in
    Debug.dprintf debug "[assoc] %d detached goals@." (List.length detached);
    Array.to_list result, detached

  let simple_associate oldgoals newgoals =
    let rec aux acc o n =
      match o,n with
        | old, [] -> acc,old
        | [], n :: rem_n -> aux ((n,None)::acc) [] rem_n
        | o :: rem_o, n :: rem_n -> aux ((n,Some(o,true))::acc) rem_o rem_n
    in
    aux [] oldgoals newgoals

  let associate ~use_shapes =
    if use_shapes then
      associate
    else
      simple_associate

end
