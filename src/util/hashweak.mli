
module Make (X:Util.Sstruct) :
sig

  type 'a t
    
  val create : int -> 'a t
    (* create a hashtbl with weak key*)

  val find : 'a t -> X.t -> 'a
    (* find the value binded to a key.
       raise Not_found if there is no binding *)

  val add : 'a t -> X.t -> 'a -> unit
    (* bind the key with the value given.
       It replace previous binding *)
end
