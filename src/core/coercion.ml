open Ident
open Ty
open Term

type crc = { crc_lsl : lsymbol list;
             crc_src : Ty.tysymbol;
             crc_tar : Ty.tysymbol;
             crc_len : int }

type t = (crc Mts.t) Mts.t
  (** invariant: transitively closed *)

let empty = Mts.empty

exception NotACoercion of lsymbol
exception CoercionCycle of lsymbol
exception CoercionAlreadyDefined of tysymbol * tysymbol

let create_crc ls =
  match ls.ls_args, ls.ls_value with
  | [{ty_node = Tyapp (ty1,_)}], Some {ty_node = Tyapp (ty2,_)} ->
     if ts_equal ty1 ty2 then raise (NotACoercion ls);
     { crc_lsl = [ls]; crc_src = ty1; crc_tar = ty2; crc_len = 1 }
  | _ -> raise (NotACoercion ls)

let mem ts1 ts2 crcmap =
  try let m = Mts.find ts1 crcmap in Mts.mem ts2 m
  with Not_found -> false

let decide c_old c_new _m1 m =
  match c_old.crc_lsl, c_new.crc_lsl with
  | [ls_old], [ls_new] when ls_equal ls_old ls_new -> m
  | _  -> raise (CoercionAlreadyDefined (c_old.crc_src, c_old.crc_tar))

let insert c m =
  let put c m1 m2 = Mts.add c.crc_src (Mts.add c.crc_tar c m1) m2 in
  if mem c.crc_tar c.crc_src m then
    begin match c.crc_lsl with
      | ls :: _ -> raise (CoercionCycle ls)
      | _ -> assert false (* there is always at least one coercion *)
    end;
  let m1 = Mts.find_def empty c.crc_src m in
  if Mts.mem c.crc_tar m1 then decide (Mts.find c.crc_tar m1) c m1 m
  else put c m1 m

let join crc1 crc2 =
  { crc_lsl = crc1.crc_lsl @ crc2.crc_lsl;
    crc_src = crc1.crc_src;
    crc_tar = crc2.crc_tar;
    crc_len = crc1.crc_len + crc2.crc_len }

let add_crc crcmap crc =
  let close_right c1 _ty c2 macc =
    insert (join c1 c2) macc in
  (* add_crc macc (join c1 c2) false in *)
  let close_left_right _ty1 m1 macc =
    if Mts.mem crc.crc_src m1
    then
      let c1 = Mts.find crc.crc_src m1 in
      let m2 = Mts.find_def empty crc.crc_tar macc in
      Mts.fold (close_right c1) (Mts.add crc.crc_tar crc m2) macc
    else macc in
  let crcmap_uc1 = insert crc crcmap in
  let crcmap_uc2 =
    let m1 = Mts.find_def empty crc.crc_tar crcmap_uc1 in
    Mts.fold (close_right crc) m1 crcmap_uc1 in
  Mts.fold (close_left_right) crcmap_uc2 crcmap_uc2

let find crcmap ts1 ts2 =
  Mts.find ts2 (Mts.find ts1 crcmap)

let add crcmap ls =
  add_crc crcmap (create_crc ls)

let union s1 s2 =
  Mts.fold (fun _ m1 s -> Mts.fold (fun _ c s -> add_crc s c) m1 s) s2 s1

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | NotACoercion ls ->
    Format.fprintf fmt "Function %s cannot be used as a coercion"
      ls.ls_name.id_string
  | CoercionCycle ls ->
    Format.fprintf fmt "Coercion %s introduces a cycle" ls.ls_name.id_string
  | CoercionAlreadyDefined (ts1, ts2) ->
    Format.fprintf fmt "A coercion from type %s to type %s@ is already defined"
      ts1.ts_name.id_string ts2.ts_name.id_string
  | _ -> raise exn end
