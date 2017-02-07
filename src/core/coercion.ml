
open Ident
open Ty
open Term

type t = (lsymbol Mts.t) Mts.t
  (** invariant: transitively closed *)

let empty = Mts.empty

exception NotACoercion of lsymbol
exception CoercionCycle of lsymbol

let mem ts1 ts2 crcmap =
  try let m = Mts.find ts1 crcmap in Mts.mem ts2 m
  with Not_found -> false

let add crcmap ls = match ls.ls_args, ls.ls_value with
  | [{ty_node = Tyapp (ty1,_)}], Some {ty_node = Tyapp (ty2,_)} ->
    if mem ty2 ty1 crcmap then raise (CoercionCycle ls);
    if ts_equal ty1 ty2 then raise (NotACoercion ls);
    let m1 = try Mts.find ty1 crcmap with Not_found -> Mts.empty in
    if Mts.mem ty2 m1 then
      Warning.emit
        "Coercion %s hides a previous coercion from %s to %s"
        ls.ls_name.id_string ty1.ts_name.id_string ty2.ts_name.id_string;
    let m2 = Mts.add ty2 ls m1 in
    Mts.add ty1 m2 crcmap
  | _ ->
    raise (NotACoercion ls)

let find crcmap ts1 ts2 =
  Mts.find ts2 (Mts.find ts1 crcmap)

let union s1 s2 =
  Mts.fold (fun _ m1 s -> Mts.fold (fun _ ls s -> add s ls) m1 s) s2 s1

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | NotACoercion ls ->
      Format.fprintf fmt "function %s cannot be used as a coercion"
        ls.ls_name.id_string
  | CoercionCycle ls ->
      Format.fprintf fmt "Coercion %s introduces a cycle" ls.ls_name.id_string
  | _ -> raise exn end

