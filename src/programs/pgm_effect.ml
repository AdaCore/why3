(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why
open Util
open Ident
open Term

type reference = 
  | Rlocal  of Term.vsymbol
  | Rglobal of Term.lsymbol

let name_of_reference = function
  | Rlocal vs -> vs.vs_name
  | Rglobal ls -> ls.ls_name

let type_of_reference = function
  | Rlocal vs -> vs.vs_ty
  | Rglobal { ls_value = Some ty } -> ty
  | Rglobal { ls_value = None } -> assert false

let ref_equal r1 r2 = match r1, r2 with
  | Rlocal vs1, Rlocal vs2 -> vs_equal vs1 vs2
  | Rglobal ls1, Rglobal ls2 -> ls_equal ls1 ls2
  | _ -> false

module Reference = struct
  
  type t = reference

  module Vsym = OrderedHash(struct
			      type t = vsymbol
			      let tag vs = vs.vs_name.id_tag
			    end)

  module Lsym = OrderedHash(struct
			      type t = lsymbol
			      let tag ls = ls.ls_name.id_tag
			    end)

  let compare r1 r2 = match r1, r2 with
    | Rlocal v1, Rlocal v2 -> Vsym.compare v1 v2
    | Rglobal l1, Rglobal l2 -> Lsym.compare l1 l2
    | Rlocal _, Rglobal _ -> -1
    | Rglobal _, Rlocal _ -> 1

  let equal r1 r2 = compare r1 r2 = 0

end

module Sref = Set.Make(Reference)
module Mref = Map.Make(Reference)

module E = Term.Sls

type t = {
  reads  : Sref.t;
  writes : Sref.t;
  raises : E.t;
}

let empty = { reads = Sref.empty; writes = Sref.empty; raises = E.empty }

let add_read  r t = { t with reads  = Sref.add r t.reads  }
let add_write r t = { t with writes = Sref.add r t.writes }
let add_raise e t = { t with raises = E.add e t.raises }

let union t1 t2 =
  { reads  = Sref.union t1.reads  t2.reads;
    writes = Sref.union t1.writes t2.writes;
    raises = E.union t1.raises t2.raises; }

let subst vs r t =
  let add1 r' s = match r' with
    | Rlocal vs' when vs_equal vs' vs -> Sref.add r s
    | _ -> Sref.add r' s
  in
  let apply s = Sref.fold add1 s Sref.empty in
  { reads = apply t.reads; writes = apply t.writes; raises = t.raises }

open Format
open Pp
open Pretty

let print_reference fmt = function
  | Rlocal vs -> print_vs fmt vs
  | Rglobal ls -> print_ls fmt ls

let print_rset fmt s = print_list comma print_reference fmt (Sref.elements s)
let print_eset fmt s = print_list comma print_ls        fmt (E.elements s)

let print fmt e =
  if not (Sref.is_empty e.reads) then 
    fprintf fmt "@ reads %a" print_rset e.reads;
  if not (Sref.is_empty e.writes) then 
    fprintf fmt "@ writes %a" print_rset e.writes;
  if not (E.is_empty e.raises) then 
    fprintf fmt "@ raises %a" print_eset e.raises


