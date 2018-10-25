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

open Term

(*******************************)
(*          explanations       *)
(*******************************)

let expl_prefixes = ref ["expl:"]

let arg_extra_expl_prefix =
  ("--extra-expl-prefix",
   Arg.String (fun s -> expl_prefixes := s :: !expl_prefixes),
   "<s> register s as an additional prefix for VC explanations")

let match_prefix prefix attr =
  (* Return the list of all labels that match the given prefix. Raise Not_found
     if none is found *)
  let acc =
    Ident.Sattr.fold
      (fun attr acc ->
        try
          let attr = attr.Ident.attr_string in
          let s = Strings.remove_prefix prefix attr in
          s :: acc
        with Not_found -> acc
      ) attr []
    in
    if acc = [] then raise Not_found else acc

let collect_expls lab =
  (* return the list of labels that match any of the provided prefixes, but
     return the empty list if any prefix is not matched at all *)
  try
    List.fold_left (fun acc x -> List.rev_append (match_prefix x lab) acc) []
    !expl_prefixes
  with Not_found -> []

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

(* {2 Shapes} *)

type shape = string

let string_of_shape s = s
(*
  try
  let l = String.length s in
  let r = Buffer.create l in
  let i = ref 0 in
  while !i < l do
  match String.get s !i with
    | '(' ->
      Buffer.add_char r '(';
      incr i;
      Buffer.add_string r (store_id s i);
      Buffer.add_char r ')'
    | c -> Buffer.add_char r c; incr i
  done;
  Buffer.contents r
  with e ->
    Format.eprintf "Error while reading shape [%s]@." s;
    raise e
*)

let shape_of_string s = s
(*
  try
  let l = String.length s in
  let r = Buffer.create l in
  let i = ref 0 in
  while !i < l do
  match String.get s !i with
    | '(' -> incr i; Buffer.add_string r (get_id s i)
    | c -> Buffer.add_char r c; incr i
  done;
  Buffer.contents r
  with e ->
    Format.eprintf "Error while reading shape [%s]@." s;
    raise e
 *)

(* tests
let _ = reset_dict () ; shape_of_string "a(b)cde(0)"
let _ = reset_dict () ; shape_of_string "a(bc)d(e)f(1)g(0)h"
let _ = reset_dict () ; shape_of_string "(abc)(def)(1)(0)(1)"
let _ = reset_dict () ; shape_of_string "(abcde)(fghij)(1)(0)(1)"
*)

let equal_shape (x:string) y = x = y
(* unused
let print_shape fmt s = Format.pp_print_string fmt (string_of_shape s)
*)

let debug = Debug.register_info_flag "session_pairing"
  ~desc:"Print@ debugging@ messages@ about@ reconstruction@ of@ \
         session@ trees@ after@ modification@ of@ source@ files."

let current_shape_version = 5

type shape_version = SV1 | SV2 | SV3 | SV4

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

let push s =
  Buffer.add_string shape_buffer s;
  if Buffer.length shape_buffer >= 1024 then raise ShapeTooLong

let pushc c =
  Buffer.add_char shape_buffer c;
  if Buffer.length shape_buffer >= 1024 then raise ShapeTooLong

let ident h id =
  let x =
    try Ident.Mid.find id !h
    with Not_found ->
      let s = id.Ident.id_string in
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

open Number

let integer_const_shape = function
  | IConstRaw i -> push (BigInt.to_string i)
  | IConstDec s -> push s
  | IConstHex s -> push "0x"; push s
  | IConstOct s -> push "0o"; push s
  | IConstBin s -> push "0b"; push s

let real_const_shape = function
  | RConstDec (i,f,None)   -> push i; push "."; push f
  | RConstDec (i,f,Some e) -> push i; push "."; push f; push "e"; push e
  | RConstHex (i,f,Some e) -> push "0x"; push i; push "."; push f; push "p"; push e
  | RConstHex (i,f,None)   -> push "0x"; push i; push "."; push f

let sign_shape is_negative =
  if is_negative then pushc '-'

let const_shape c =
  match c with
  | ConstInt c -> sign_shape c.ic_negative; integer_const_shape c.ic_abs
  | ConstReal c -> sign_shape c.rc_negative; real_const_shape c.rc_abs


let rec pat_shape c m p : 'a =
  match p.pat_node with
    | Pwild -> pushc tag_wild
    | Pvar _ -> pushc tag_var
    | Papp (f, l) ->
       pushc tag_app;
       ident m f.ls_name;
       List.iter (pat_shape c m) l
    | Pas (p, _) -> pat_shape c m p; pushc tag_as
    | Por (p, q) ->
       pat_shape c m q; pushc tag_or; pat_shape c m p

let rec t_shape ~version c m t =
  let fn = t_shape ~version c m in
  match t.t_node with
    | Tconst c -> pushc tag_const; const_shape c
    | Tvar v -> pushc tag_var; ident m v.vs_name
    | Tapp (s,l) ->
       pushc tag_app;
       ident m s.ls_name;
       List.iter fn l
    | Tif (f,t1,t2) ->
      begin match version with
      | SV1 | SV2 -> pushc tag_if; fn f; fn t1; fn t2
      | SV3 | SV4 -> pushc tag_if; fn t2; fn t1; fn f
      end
    | Tcase (t1,bl) ->
        let br_shape b =
          let p,t2 = t_open_branch b in
          match version with
          | SV1 | SV2 ->
            pat_shape c m p;
            pat_rename_alpha c m p;
            t_shape ~version c m t2
          | SV3 | SV4 ->
            pat_rename_alpha c m p;
            t_shape ~version c m t2;
            pat_shape c m p
        in
        begin match version with
        | SV1 | SV2 ->
                 pushc tag_case;
                 fn t1;
                 List.iter br_shape bl
        | SV3 | SV4 ->
           pushc tag_case;
           List.iter br_shape bl;
           fn t1
        end
    | Teps b ->
        pushc tag_eps;
        let u,f = t_open_bound b in
        vs_rename_alpha c m u;
        t_shape ~version c m f
    | Tquant (q,b) ->
        let vl,triggers,f1 = t_open_quant b in
        vl_rename_alpha c m vl;
        (* argument first, intentionally, to give more weight on A in
           forall x,A *)
        t_shape ~version c m f1;
        let hq = match q with Tforall -> tag_forall | Texists -> tag_exists in
        pushc hq;
        List.iter
          (fun trigger ->
             List.iter
               (fun t -> t_shape ~version c m t)
               trigger)
          triggers
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
               pushc tag_let; fn t1; t_shape ~version c m t2
            | SV2 | SV3 | SV4 ->
                     (* t2 first, intentionally *)
                     t_shape ~version c m t2; pushc tag_let; fn t1
        end
    | Tnot f ->
      begin match version with
      | SV1 | SV2 -> fn f; pushc tag_not
      | SV3 | SV4 -> pushc tag_not; fn f
      end
    | Ttrue -> pushc tag_true
    | Tfalse -> pushc tag_false

let t_shape_task ~version ~expl t =
  Buffer.clear shape_buffer;
  let f = Task.task_goal_fmla t in
  let c = ref (-1) in
  let m = ref Ident.Mid.empty in
  let () =
    try
      (* expl *)
      begin match version with
      | SV1 | SV2 -> ()
      | SV3 | SV4 -> push expl end;
      (* goal shape *)
      t_shape ~version c m f;
      (* introduced premises shape *)
      begin match version with
      | SV1 | SV2 | SV3 -> ()
      | SV4 ->
         let open Decl in
         let introduced id = Ident.Sattr.mem
                               Introduction.intro_attr
                               id.Ident.id_attrs in
         let do_td td = match td.Theory.td_node with
           | Theory.Decl d ->
              begin match d.d_node with
              | Dparam _ls -> ()
              | Dprop (_, pr, f) when introduced pr.pr_name ->
                 t_shape ~version c m f
              | _ -> ()
              end
           | _ -> () in
         let _, prev = Task.task_separate_goal t in
         Task.task_iter do_td prev
      end
    with ShapeTooLong -> ()
  in
  Buffer.contents shape_buffer

(*
let time = ref 0.0
 *)

let t_shape_task ?(version=current_shape_version) ~expl t =
  let version = match version with
    | 1 -> SV1 | 2 -> SV2 | 3 | 4 -> SV3 | 5 -> SV4
    | _ -> assert false
  in
(*
  let tim = Unix.gettimeofday () in
 *)
  let s = t_shape_task ~version ~expl t in
(*
  let tim = Unix.gettimeofday () -. tim in
  time := !time +. tim;
  Format.eprintf "[Shape times] %f/%f@." tim !time;
*)
  s

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

type checksum_version = CV1 | CV2

module Checksum = struct

  let char (_,_,_,buf) c = Buffer.add_char buf c
  let int (_,_,_,buf as b) i =
    char b 'i'; Buffer.add_string buf (string_of_int i)
  let raw_string (_,_,_,buf) s = Buffer.add_string buf s
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
    | CV1 -> ident_v1 b id
    | CV2 -> ident_v2 b id

  let integer_const b = function
    | IConstRaw i -> raw_string b (BigInt.to_string i)
    | IConstDec s -> raw_string b s
    | IConstHex s -> raw_string b "0x"; raw_string b s
    | IConstOct s -> raw_string b "0o"; raw_string b s
    | IConstBin s -> raw_string b "0b"; raw_string b s

  let real_const b = function
    | RConstDec (i,f,None)   ->
       raw_string b i; raw_string b "."; raw_string b f
    | RConstDec (i,f,Some e) ->
       raw_string b i; raw_string b "."; raw_string b f; raw_string b "e"; raw_string b e
    | RConstHex (i,f,Some e) ->
       raw_string b "0x"; raw_string b i; raw_string b "."; raw_string b f;
       raw_string b "p"; raw_string b e
    | RConstHex (i,f,None)   ->
       raw_string b "0x"; raw_string b i; raw_string b "."; raw_string b f

  let sign b is_negative =
    if is_negative then raw_string b "-"

  let const b c =
    match c with
    | ConstInt c -> sign b c.ic_negative; integer_const b c.ic_abs
    | ConstReal c -> sign b c.rc_negative; real_const b c.rc_abs

  let tvsymbol b tv = ident b tv.Ty.tv_name

  let rec ty b t = match t.Ty.ty_node with
    | Ty.Tyvar tv -> char b 'v'; tvsymbol b tv
    | Ty.Tyapp (ts, tyl) -> char b 'a'; ident b ts.Ty.ts_name; list ty b tyl

  let vsymbol (v,_,_,_ as b) vs = match v with
    | CV1 -> ty b vs.vs_ty
    | CV2 -> ident b vs.vs_name; ty b vs.vs_ty

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
      Task.task_iter (tdecl (CV1,c,m,b)) t;
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
      tdecl (CV2,c,m,b) t.Task.task_decl;
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


  let task ~version t = match version with
    | CV1 -> task_v1 t
    | CV2 -> task_v2 t

end

(*
let time = ref 0.0
 *)

let task_checksum ?(version=current_shape_version) t =
  let version = match version with
    | 1 | 2 | 3 -> CV1
    | 4 | 5 -> CV2
    | _ -> assert false
  in
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

(* not used anymore
let theory_checksum ?(version=current_shape_version) t =
  let version = match version with
    | 1 | 2 | 3 -> CV1
    | 4 -> CV2
    | _ -> assert false
  in
  Checksum.theory ~version t
 *)

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
  val shape    : 'a t -> string
  val name     : 'a t -> Ident.ident
end

module Pairing(Old: S)(New: S) = struct

  let rec lcp n s1 s2 =
    if String.length s1 <= n || String.length s2 <= n then n
    else if s1.[n] = s2.[n] then lcp (n+1) s1 s2 else n
  let lcp = lcp 0

  open Ident

  type goal_index = Old of int | New of int

  type ('a,'b) goal_table = {
    table_old : 'a Old.t array;
    table_new : 'b New.t array;
  }

  (* doubly linked lists; left and right bounds point to themselves *)

  type node = {
    mutable  prev: node;
            shape: string;
              elt: goal_index;
    mutable valid: bool;
    mutable  next: node;
  }

  let mk_node table g =
    let s = match g with
      | Old g -> Old.shape table.table_old.(g)
      | New g -> New.shape table.table_new.(g)
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
      for newi = 0 to Array.length table.table_new - 1 do
        try
          let newg = table.table_new.(newi) in
          match New.checksum newg with
          | None -> raise Not_found
          | Some c ->
             let oldi = Hashtbl.find old_checksums c in
             let oldg = table.table_old.(oldi) in
             Hashtbl.remove old_checksums c;
             let obs = Old.shape oldg <> New.shape newg in
             result.(new_goal_index newg) <- (newg, Some (oldg, obs))
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
        let dummy = let n = List.hd allgoals (* safe *) in 0, (n, n)
        type t = int * (node * node)
        let compare (v1, _) (v2, _) = Pervasives.compare v2 v1
      end in
      let module PQ = Pqueue.Make(E) in
      let pq = PQ.create () in
      let add x y = match x.elt, y.elt with
        | Old _, New _ | New _, Old _ ->
            PQ.insert (lcp x.shape y.shape, (x, y)) pq
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
