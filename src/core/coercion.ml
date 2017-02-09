
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

let find crcmap ts1 ts2 =
  Mts.find ts2 (Mts.find ts1 crcmap)

(* replace an old coercion by a new one, or fail *)
let replace c_old c_new _m1 m =
  match c_old.crc_kind, c_new.crc_kind with
  | CRCleaf ls_old, CRCleaf ls_new when ls_equal ls_old ls_new -> m
  | _  -> raise (CoercionAlreadyDefined c_old)

(* add a new coercion c, without making the transitive closure *)
let insert crc m =
  let put crc m1 m2 = Mts.add crc.crc_src (Mts.add crc.crc_tar crc m1) m2 in
  if mem m crc.crc_tar crc.crc_src then
    raise (CoercionCycle (find m crc.crc_tar crc.crc_src));
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

let union s1 s2 =
  Mts.fold (fun _ m1 s -> Mts.fold (fun _ c s -> add_crc s c) m1 s) s2 s1

let rec print_kind fmt = function
  | CRCleaf ls ->
    Format.fprintf fmt "%s" ls.ls_name.id_string
  | CRCcomp (k1, k2) ->
    Format.fprintf fmt "%a o %a" print_kind k2 print_kind k1

let already_a_coercion fmt crc =
  Format.fprintf fmt "already a coercion from type %s to type %s@ (%a)"
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
