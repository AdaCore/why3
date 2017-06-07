open Ident

val clean_name : string -> string

val module_name : ?fname:string -> string list -> string -> string

module ML : sig
  val get_decl_name : Mltree.decl -> ident list

  val iter_deps : (Ident.ident -> unit) -> Mltree.decl -> unit
end

module Translate : sig
  val module_ : Pmodule.pmodule -> Mltree.pmodule

  val pdecl_m : Pmodule.pmodule -> Pdecl.pdecl -> Mltree.decl list
end

module Transform : sig
  val module_ : Mltree.pmodule -> Mltree.pmodule
end
