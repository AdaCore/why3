(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

type t =
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable font_size : int;
      mutable current_tab : int;
      mutable verbose : int;
      mutable show_full_context : bool;
      mutable show_attributes : bool;
      mutable show_coercions : bool;
      mutable show_locs : bool;
      mutable show_time_limit : bool;
      mutable max_boxes : int;
      mutable allow_source_editing : bool;
      mutable saving_policy : int;
      mutable premise_color : string;
      mutable neg_premise_color : string;
      mutable goal_color : string;
      mutable error_color : string;
      mutable error_color_bg : string;
      mutable error_line_color : string;
      mutable iconset : string;
      mutable config : Whyconf.config;
      original_config : Whyconf.config;
      (* mutable altern_provers : prover option Mprover.t; *)
      (* mutable replace_prover : conf_replace_prover; *)
      mutable hidden_provers : string list;
      mutable session_time_limit : int;
      mutable session_mem_limit : int;
      mutable session_nb_processes : int;
    }

val load_config : Whyconf.config -> Whyconf.config -> unit
(** [load_config config original_config] creates and saves IDE config *)

val init : unit -> unit

val save_config : unit -> unit

val config : unit -> t
(** [config ()] raise [invalid_arg "configuration not yet loaded"]
    if load_config is not called *)

val get_main : unit -> Whyconf.main

(*******************)
(*   font size     *)
(*******************)

val add_modifiable_sans_font_view : GObj.misc_ops -> unit
val add_modifiable_mono_font_view : GObj.misc_ops -> unit
val enlarge_fonts : unit -> unit
val reduce_fonts : unit -> unit
val set_fonts : unit -> unit

(*****************)
(* images, icons *)
(*****************)

val why_icon : GdkPixbuf.pixbuf ref

val image_yes : GdkPixbuf.pixbuf ref

(* tree object icons *)
val image_file : GdkPixbuf.pixbuf ref
val image_theory : GdkPixbuf.pixbuf ref
val image_goal : GdkPixbuf.pixbuf ref
val image_prover : GdkPixbuf.pixbuf ref
val image_transf : GdkPixbuf.pixbuf ref
val image_metas  : GdkPixbuf.pixbuf ref
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
val image_outofmemory : GdkPixbuf.pixbuf ref
val image_steplimitexceeded : GdkPixbuf.pixbuf ref
val image_unknown : GdkPixbuf.pixbuf ref
val image_failure : GdkPixbuf.pixbuf ref
val image_valid_obs : GdkPixbuf.pixbuf ref
val image_invalid_obs : GdkPixbuf.pixbuf ref
val image_timeout_obs : GdkPixbuf.pixbuf ref
val image_outofmemory_obs : GdkPixbuf.pixbuf ref
val image_steplimitexceeded_obs : GdkPixbuf.pixbuf ref
val image_unknown_obs : GdkPixbuf.pixbuf ref
val image_failure_obs : GdkPixbuf.pixbuf ref

(*************************)
(* miscellaneous dialogs *)
(*************************)

val show_legend_window : parent:#GWindow.window_skel -> unit -> unit
val show_about_window : parent:#GWindow.window_skel -> unit -> unit
val preferences : parent:#GWindow.window_skel -> t -> unit

val uninstalled_prover_dialog :
  parent:#GWindow.window_skel ->
  callback: (Whyconf.prover -> Whyconf.prover_upgrade_policy -> unit) ->
  t -> Whyconf.prover -> unit


(*
val unknown_prover :
  t -> 'key Session.env_session -> Whyconf.prover -> Whyconf.prover option
*)

(* obsolete dialog
val replace_prover :
  t -> 'key Session.proof_attempt -> 'key Session.proof_attempt -> bool
*)


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
