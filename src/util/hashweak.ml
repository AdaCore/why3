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

module Make (S : Util.Tagged) = struct

  type 'a t = {
    table : (int,'a) Hashtbl.t;
    final : S.t -> unit;
  }

  let create n =
    let table = Hashtbl.create n in
    let w = Weak.create 1 in
    Weak.set w 0 (Some table);
    let final x = match Weak.get w 0 with
      | None -> ()
      | Some h -> Hashtbl.remove h (S.tag x)
    in
    { table = table; final = final }

  let add_tag  h = Hashtbl.add  h.table
  let mem_tag  h = Hashtbl.mem  h.table
  let find_tag h = Hashtbl.find h.table

  let add_tag h t e v =
    Gc.finalise h.final e; add_tag h t v

  let add  h e = add_tag  h (S.tag e) e
  let mem  h e = mem_tag  h (S.tag e)
  let find h e = find_tag h (S.tag e)

  let memoize n fn =
    let h = create n in fun e ->
      let t = S.tag e in
      try find_tag h t
      with Not_found ->
        let v = fn e in
        add_tag h t e v;
        v

  let memoize_option n fn =
    let v = fn None in
    let fn e = fn (Some e) in 
    let fn = memoize n fn in
    function
      | Some e -> fn e
      | None -> v

end

