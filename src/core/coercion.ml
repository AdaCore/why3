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
exception Cycle
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

let decide c_old c_new _m1 _m =
  raise (CoercionAlreadyDefined (c_old.crc_src, c_old.crc_tar))
   (* let c_m1 = Mts.find c.crc_tar m1 in
    if c.crc_len < c_m1.crc_len then
      begin
        Warning.emit
          "Some coercion hides a previous coercion from %s to %s"
          c.crc_src.ts_name.id_string c.crc_tar.ts_name.id_string;
        put c m1 m (*maybe also redo closure with shorter paths *)
      end
  else m *)


let insert c m =
  let put c m1 m2 = Mts.add c.crc_src (Mts.add c.crc_tar c m1) m2 in
  if mem c.crc_tar c.crc_src m then raise Cycle ;
  let m1 = try Mts.find c.crc_src m with Not_found -> Mts.empty in
  if Mts.mem c.crc_tar m1 then decide (Mts.find c.crc_tar m1) c m1 m;
  put c m1 m

let join crc1 crc2 =
  { crc_lsl = crc1.crc_lsl @ crc2.crc_lsl;
    crc_src = crc1.crc_src;
    crc_tar = crc2.crc_tar;
    crc_len = crc1.crc_len + crc2.crc_len }

let rec add_crc crcmap crc trans =
  let close_right c1 _ty c2 macc =
    add_crc macc (join c1 c2) false in
  let close_left_right c ty1 _ macc =
    try
      let m1 = Mts.find ty1 macc in
      if Mts.mem c.crc_src m1
      then
        let c1 = Mts.find c.crc_src m1 in
        let m2 = try Mts.find c.crc_tar macc
                 with Not_found -> Mts.empty in
        Mts.fold (close_right c1) m2 macc
      else macc
    with Not_found -> macc in
  if not trans then insert crc crcmap else
    let crcmap_uc1 = insert crc crcmap in
    let crcmap_uc2 =
      let m1 =
        try Mts.find crc.crc_tar crcmap_uc1 with Not_found -> Mts.empty in
      Mts.fold (close_right crc) m1 crcmap_uc1 in
    Mts.fold (close_left_right crc) crcmap_uc2 crcmap_uc2


let add crcmap ls =
  let c = create_crc ls in
  add_crc crcmap c true

(*
let add crcmap ls = match ls.ls_args, ls.ls_value with
  | [{ty_node = Tyapp (ty1,_)}], Some {ty_node = Tyapp (ty2,_)} ->
    if mem ty2 ty1 crcmap then raise (CoercionCycle ls);
    if ts_equal ty1 ty2 then raise (NotACoercion ls);
    let m1 = try Mts.find ty1 crcmap with Not_found -> Mts.empty in
    if Mts.mem ty2 m1 then
      Warning.emit
        "Coercion %s hides a previous coercion from %s to %s"
        ls.ls_name.id_string ty1.ts_name.id_string ty2.ts_name.id_string;
    let m2 = Mts.add ty2 [ls] m1 in
    Mts.add ty1 m2 crcmap
  | _ ->
    raise (NotACoercion ls)
 *)


let find crcmap ts1 ts2 =
  Mts.find ts2 (Mts.find ts1 crcmap)

let union s1 s2 =
  Mts.fold (fun _ m1 s -> Mts.fold (fun _ c s -> add_crc s c true) m1 s) s2 s1

let print crcmap =
  Mts.iter
       (fun k m ->
         (Mts.iter (fun k2 _ -> Format.eprintf "coercion from %s to %s @."
                                                k.ts_name.id_string
                                                k2.ts_name.id_string)
                   m ))
       crcmap


let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | NotACoercion ls ->
      Format.fprintf fmt "Function %s cannot be used as a coercion"
        ls.ls_name.id_string
  | CoercionCycle ls ->
      Format.fprintf fmt "Coercion %s introduces a cycle" ls.ls_name.id_string
  | _ -> raise exn end
