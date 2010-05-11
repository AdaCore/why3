
open Why
open Util
open Ident
open Term
open Pgm_ttree

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

end

module R = Set.Make(Reference)

module E = Term.Sls

type t = {
  reads  : R.t;
  writes : R.t;
  raises : E.t;
}

let empty = { reads = R.empty; writes = R.empty; raises = E.empty }



