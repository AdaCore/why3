(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

open Why3
open Whyconf

(** Todo do something generic perhaps*)
type conf_replace_prover =
  | CRP_Ask
  | CRP_Not_Obsolete

type t =
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable time_limit : int;
      mutable mem_limit : int;
      mutable verbose : int;
      mutable max_running_processes : int;
      mutable default_editor : string;
      mutable intro_premises : bool;
      mutable show_labels : bool;
      mutable show_locs : bool;
      mutable show_time_limit : bool;
      mutable saving_policy : int;
      mutable premise_color : string;
      mutable goal_color : string;
      mutable error_color : string;
      mutable env : Why3.Env.env;
      mutable config : Whyconf.config;
      original_config : Whyconf.config;
      mutable altern_provers : prover option Mprover.t;
      mutable replace_prover : conf_replace_prover;
    }

val read_config : string option -> string list -> unit
(** None use the default config *)

val save_config : unit -> unit

val config : unit -> t
(** [config ()] raise [invalid_arg "configuration not yet loaded"]
    if load_config is not called *)

val get_main : unit -> Whyconf.main

(*****************)
(* images, icons *)
(*****************)

val why_icon : GdkPixbuf.pixbuf ref

val image_yes : GdkPixbuf.pixbuf ref

(* tree object icons *)
val image_directory : GdkPixbuf.pixbuf ref
val image_file : GdkPixbuf.pixbuf ref
val image_prover : GdkPixbuf.pixbuf ref
val image_transf : GdkPixbuf.pixbuf ref
val image_editor : GdkPixbuf.pixbuf ref
val image_replay : GdkPixbuf.pixbuf ref
val image_cancel : GdkPixbuf.pixbuf ref
val image_reload : GdkPixbuf.pixbuf ref
val image_remove : GdkPixbuf.pixbuf ref
val image_cleaning : GdkPixbuf.pixbuf ref

(* status icons *)
val image_undone : GdkPixbuf.pixbuf ref
val image_scheduled : GdkPixbuf.pixbuf ref
val image_running : GdkPixbuf.pixbuf ref
val image_valid : GdkPixbuf.pixbuf ref
val image_invalid : GdkPixbuf.pixbuf ref
val image_timeout : GdkPixbuf.pixbuf ref
val image_unknown : GdkPixbuf.pixbuf ref
val image_failure : GdkPixbuf.pixbuf ref
val image_valid_obs : GdkPixbuf.pixbuf ref
val image_invalid_obs : GdkPixbuf.pixbuf ref
val image_timeout_obs : GdkPixbuf.pixbuf ref
val image_unknown_obs : GdkPixbuf.pixbuf ref
val image_failure_obs : GdkPixbuf.pixbuf ref

(*************************)
(* miscellaneous dialogs *)
(*************************)

val show_legend_window : unit -> unit
val show_about_window : unit -> unit
val preferences : t -> unit
val unknown_prover :
  t -> 'key Session.env_session -> Whyconf.prover -> Whyconf.prover option

(**)
val replace_prover :
  t -> 'key Session.proof_attempt -> 'key Session.proof_attempt -> bool
(**)


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
