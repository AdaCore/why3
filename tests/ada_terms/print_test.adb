(* TODO this is a test for the ada_terms plugin *)

module A1
use int.Int

goal G: forall x [@name:X]. x = 1 && x = 2 /\ x = 3 -> x <> 0

type r = { h [@name:L]: int}

type t = { f [@name:F]: r; g : bool}

goal G1: forall x [@name:Y]: t. x.f.h = 3 /\ x.g

end

module A3

type bar

(* This __t is supposed to be an array type *)

(* The elts part is always of the form a -> b *)
type __t [@syntax:array:elts] = { elts [@syntax:getter:elts] : int -> int; foo: bar}

(* The getter type is always of the type __t -> a -> b *)
function get [@syntax:getter:get] (a: __t) (i: int) : int = a.elts i

function first [@model_trace:'First] [@name:First] (_: __t) : int

end

module A2
use A3
use int.Int

function first [@model_trace:'First] [@name:First] (_: __t) : int
function last [@model_trace:'Last] [@name:Last] (_: __t) : int

let f (a [@name:A] : __t)
  requires { last a = A3.first a + 25 }
  ensures  { first a = result }
=
  83

end


module A4
use A3
use int.Int

(* This should be printed a(i) = a(i+1) *)
goal G6: forall a:__t, i: int. get a i = get a (i + 1)


end

module A5

use int.Int

type t [@name:Mod256] = <range 7 42>

goal G7: forall a: t. a = (41:t)


end