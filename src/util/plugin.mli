type plugin = string

exception Plugin_Not_Found of plugin * string list

val debug : Debug.flag
(** debug flag for the plugin mechanism (option "--debug
    load_plugin")
    If set [load_plugin] prints on stderr exactly which plugin are loaded.
*)

val load : ?dirs:string list -> plugin -> unit
(* [load_plugin ~dir plugin] looks in the directories [dir] for the
   plugin named [plugin]. It add the extension .cmo or .cmxs to the
   filename according to the compilation used for the main program *)

type ext =
(* not a plugin extension *)
  | Extbad
(* good plugin extension *)
  | Extgood
 (* good plugin extension but not the current compilation used *)
  | Extother

val check_extension : plugin -> ext
