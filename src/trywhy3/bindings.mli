(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Js_of_ocaml
open Js

val log : string -> unit
val log_time : string -> unit
val check_def : string -> 'a Optdef.t -> 'a
val get_global : string -> 'a

module Url : sig
  class type urlSearchParams =
    object
      method delete : js_string t -> unit meth
      method get : js_string t -> js_string t opt meth
      method has : js_string t -> bool t meth
      method set : js_string t ->js_string t -> unit meth
      method toString : js_string t meth
    end
  class type url =
    object
      method hash : js_string t prop
      method host : js_string t prop
      method hostname : js_string t prop
      method href : js_string t prop
      method origin : js_string t readonly_prop
      method password : js_string t prop
      method pathname : js_string t prop
      method port : js_string t prop
      method protocol : js_string t prop
      method search : js_string t prop
      method searchParams : urlSearchParams t readonly_prop
      method username : js_string t prop
      end
  val _URL : (js_string t -> url t) constr
end

module Promise : sig
  type 'a promise
  class type ['a] inner_promise =
    object
      method _then : ('a -> 'b promise) callback -> 'b promise meth
      method _then_float : ('a -> float) callback -> float promise meth
      method _then_int : ('a -> int) callback -> int promise meth
      method _then_unit : ('a -> unit) callback -> unit promise meth
      method _then_value : ('a -> 'b t) callback -> 'b t promise meth
      method catch : (Unsafe.any -> 'a) callback -> 'a promise meth
    end
  external unwrap : 'a promise -> 'a inner_promise t = "%identity"
  external wrap : 'a inner_promise t -> 'a promise = "%identity"
  val bind : 'a promise -> ('a -> 'b promise) -> 'b promise
  val bind_unit : 'a promise -> ('a -> unit) -> unit promise
  val catch : unit promise -> (Unsafe.any -> unit) -> unit
end

module Fetch : sig
  class type response =
    object
      method ok : bool prop
      method text : js_string t Promise.promise meth
    end
  val fetch : js_string t -> response t Promise.promise
end

module Ace () : sig
  type marker
  class type annotation =
    object
      method _type : js_string t readonly_prop
      method column : int readonly_prop
      method row : int readonly_prop
      method text : js_string t readonly_prop
    end
  class type range = object  end
  class type selection =
    object
      method setSelectionRange : range t -> bool t -> unit meth
    end
  class type undoManager =
    object
      method hasRedo : bool t meth
      method hasUndo : bool t meth
      method isClean : bool t meth
      method markClean : unit meth
      method reset : unit meth
    end
  class type editSession =
    object
      method addMarker : range t -> js_string t -> js_string t -> bool t -> marker meth
      method clearAnnotations : unit meth
      method getLength : int meth
      method getUndoManager : undoManager t meth
      method removeMarker : marker -> unit meth
      method setAnnotations : annotation t js_array t -> unit meth
      method setMode : js_string t -> unit meth
    end
  class type editor =
    object
      method focus : unit meth
      method getSelection : selection t meth
      method getSession : editSession t meth
      method getValue : js_string t meth
      method gotoLine : int -> int -> bool t -> unit meth
      method on : js_string t -> (Unsafe.any -> editor t -> unit) callback -> unit meth
      method redo : unit meth
      method setReadOnly : bool t -> unit meth
      method setTheme : js_string t -> unit meth
      method setValue : js_string t -> int -> unit meth
      method undo : unit meth
    end
  class type ace =
    object
      method edit : js_string t -> editor t optdef meth
      method require : js_string t -> Unsafe.any meth
    end
  val ace : ace t
  val edit : js_string t -> editor t optdef
  val range : (int -> int -> int -> int -> range t) constr
  val annotation : int -> int -> js_string t -> js_string t -> annotation t
end
