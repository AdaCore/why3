
open Ident
open Ty
open Term

type coercion_kind =
  | CRCleaf of lsymbol
  | CRCcomp of coercion_kind * coercion_kind

type coercion = {
  crc_kind: coercion_kind;
  crc_src : Ty.tysymbol;
  crc_tar : Ty.tysymbol;
  crc_len : int;
}

type t = (coercion Mts.t) Mts.t
  (** invariant: transitively closed *)

let empty = Mts.empty

exception NotACoercion of lsymbol
exception CoercionCycle of coercion
exception CoercionAlreadyDefined of coercion

let create_crc ls =
  match ls.ls_args, ls.ls_value with
  | [{ty_node = Tyapp (ty1,_)}], Some {ty_node = Tyapp (ty2,_)} ->
     if ts_equal ty1 ty2 then raise (NotACoercion ls);
     { crc_kind = CRCleaf ls; crc_src = ty1; crc_tar = ty2; crc_len = 1 }
  | _ -> raise (NotACoercion ls)

let mem crcmap ts1 ts2 =
  try let m = Mts.find ts1 crcmap in Mts.mem ts2 m
  with Not_found -> false

let find_crc crcmap ts1 ts2 =
  Mts.find ts2 (Mts.find ts1 crcmap)

let find crcmap ts1 ts2 =
  let crc = find_crc crcmap ts1 ts2 in
  let rec ls_list_of acc = function
    | CRCleaf ls -> ls :: acc
    | CRCcomp (k1, k2) -> ls_list_of (ls_list_of acc k2) k1 in
  ls_list_of [] crc.crc_kind

(* replace an old coercion by a new one, or fail *)
let rec ck_eq ck_old ck_new =
  match ck_old, ck_new with
  | CRCleaf ls_old, CRCleaf ls_new when ls_equal ls_old ls_new -> ()
  |  CRCcomp (old_ck1, old_ck2), CRCcomp (new_ck1, new_ck2) ->
      ck_eq old_ck1 new_ck1;
      ck_eq old_ck2 new_ck2
  | _  -> raise Not_found

(* replace an old coercion by a new one, or fail *)
let replace c_old c_new _m1 m =
  try ck_eq c_old.crc_kind c_new.crc_kind; m
  with Not_found -> raise (CoercionAlreadyDefined c_old)

(* add a new coercion c, without making the transitive closure *)
let insert crc m =
  let put crc m1 m2 = Mts.add crc.crc_src (Mts.add crc.crc_tar crc m1) m2 in
  if mem m crc.crc_tar crc.crc_src then
    raise (CoercionCycle (find_crc m crc.crc_tar crc.crc_src));
  let m1 = Mts.find_def Mts.empty crc.crc_src m in
  if Mts.mem crc.crc_tar m1 then replace (Mts.find crc.crc_tar m1) crc m1 m
  else put crc m1 m

let compose crc1 crc2 =
  { crc_kind = CRCcomp (crc1.crc_kind, crc2.crc_kind);
    crc_src = crc1.crc_src;
    crc_tar = crc2.crc_tar;
    crc_len = crc1.crc_len + crc2.crc_len }

(* add a new coercion crc, and make the transitive closure *)
let add_crc crcmap crc =
  let close_right c1 _ty c2 macc = insert (compose c1 c2) macc in
  let close_left_right _ty1 m1 macc =
    if Mts.mem crc.crc_src m1 then
      let c1 = Mts.find crc.crc_src m1 in
      let m2 = Mts.find_def Mts.empty crc.crc_tar macc in
      Mts.fold (close_right c1) (Mts.add crc.crc_tar crc m2) macc
    else macc in
  let crcmap_uc1 = insert crc crcmap in
  let crcmap_uc2 =
    let m1 = Mts.find_def Mts.empty crc.crc_tar crcmap_uc1 in
    Mts.fold (close_right crc) m1 crcmap_uc1 in
  Mts.fold (close_left_right) crcmap_uc2 crcmap_uc2

let add crcmap ls =
  add_crc crcmap (create_crc ls)

let union crcmap1 crcmap2 =
  let add _ty2 crc crcmap =
    if crc.crc_len = 1 then add_crc crcmap crc else crcmap in
  Mts.fold (fun _ty1 m1 crcmap -> Mts.fold add m1 crcmap) crcmap2 crcmap1

let print_kind fmt crc =
  let ty_str_of ls =
    match ls.ls_args, ls.ls_value with
    | [{ty_node = Tyapp (ty1,_)}], Some {ty_node = Tyapp (ty2,_)} ->
       ty1.ts_name.id_string, ty2.ts_name.id_string
    | _  -> assert false in
  let rec print_kind fmt = function
    | CRCleaf ls ->
       let s1, s2 = ty_str_of ls in
       Format.fprintf fmt "%s: %s -> %s" ls.ls_name.id_string s1 s2
    | CRCcomp (k1, k2) ->
       Format.fprintf fmt "%a@\n%a" print_kind k1 print_kind k2
  in print_kind fmt crc

let rec print_kind_ls fmt = function
  | CRCleaf ls ->
     Format.fprintf fmt "%s" ls.ls_name.id_string
  | CRCcomp (k1, k2) ->
     Format.fprintf fmt "%a; %a" print_kind_ls k1 print_kind_ls k2

let already_a_coercion fmt crc =
  Format.fprintf fmt
    "There is already a coercion [%a] from type %s to type %s:@\n%a"
    print_kind_ls crc.crc_kind
    crc.crc_src.ts_name.id_string crc.crc_tar.ts_name.id_string
    print_kind crc.crc_kind

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | NotACoercion ls ->
    Format.fprintf fmt "Function %s cannot be used as a coercion"
      ls.ls_name.id_string
  | CoercionCycle crc ->
    Format.fprintf fmt "This coercion introduces a cycle;@ ";
    already_a_coercion fmt crc
  | CoercionAlreadyDefined crc ->
    already_a_coercion fmt crc
  | _ -> raise exn end
