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

let pname = "[Why-rustprover]"

let () = ignore (GtkMain.Main.init ())

open Format
open Why
open Whyconf

(******************************)
(* loading user configuration *)
(******************************)

let config = 
  try 
    Whyconf.read_config None
  with 
      Not_found -> 
        eprintf "%s No config file found.@." pname;
        exit 1
    | Whyconf.Error e ->
        eprintf "%s Error while reading config file: %a@." pname 
          Whyconf.report e;
        exit 1

let () = eprintf "%s Load path is: %a@." pname
  (Pp.print_list Pp.comma Pp.string) config.loadpath

let timelimit = 
  match config.timelimit with
    | None -> 2
    | Some n -> n


(* TODO: put that in config file *)
let window_width = 1024
let window_height = 768
let font_name = "Monospace 10"

let spec = []
let usage_str = "why-rustprover [options] <file>.why"
let file = ref None
let set_file f = match !file with
  | Some _ -> 
      raise (Arg.Bad "only one file")
  | None -> 
      if not (Filename.check_suffix f ".why") then 
	raise (Arg.Bad ("don't know what to do with " ^ f));
      if not (Sys.file_exists f) then begin
	Format.eprintf "%s %s: no such file@." pname f; 
        exit 1
      end;
      file := Some f

let () = Arg.parse spec set_file usage_str

let fname = match !file with
  | None -> 
      Arg.usage spec usage_str; 
      exit 1
  | Some f -> 
      f

let lang =
  let load_path = 
    List.fold_right Filename.concat 
      [Filename.dirname Sys.argv.(0); ".."; "share"] "lang" 
  in
  let languages_manager = 
    GSourceView2.source_language_manager ~default:true 
  in
  languages_manager#set_search_path 
    (load_path :: languages_manager#search_path);
  match languages_manager#language "why" with
    | None -> Format.eprintf "pas trouvé@;"; None
    | Some _ as l -> l

let source_text = 
  let ic = open_in fname in
  let size = in_channel_length ic in
  let buf = String.create size in
  really_input ic buf 0 size;
  close_in ic;
  buf

let env = Why.Env.create_env (Why.Typing.retrieve config.loadpath)


(***********************)
(* Parsing input file  *)
(***********************)
   
let rec report fmt = function
  | Lexer.Error e ->
      fprintf fmt "lexical error: %a" Lexer.report e;
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc report e
  | Parsing.Parse_error ->
      fprintf fmt "syntax error"
  | Denv.Error e ->
      Denv.report fmt e
  | Typing.Error e ->
      Typing.report fmt e
  | Decl.UnknownIdent i ->
      fprintf fmt "anomaly: unknown ident '%s'" i.Ident.id_string
  | Driver.Error e ->
      Driver.report fmt e
  | Config.Dynlink.Error e ->
      fprintf fmt "Dynlink : %s" (Config.Dynlink.error_message e)
  | e -> fprintf fmt "anomaly: %s" (Printexc.to_string e)


let theories : Theory.theory Theory.Mnm.t =
  try
    let cin = open_in fname in
    let m = Env.read_channel env fname cin in
    close_in cin;
    eprintf "Parsing/Typing Ok@.";
    m
  with e -> 
    eprintf "%a@." report e;
    exit 1

(********************)
(* opening database *)
(********************)

let () = Db.init_base (fname ^ ".db")

let get_driver name = 
  let pi = Util.Mstr.find name config.provers in
  Why.Driver.load_driver env pi.Whyconf.driver

type prover_data =
    { prover : Db.prover;
      command : string;
      driver : Why.Driver.driver;
    }

let provers_data =
  printf "===============================@\nProvers: ";
  let l = 
    Util.Mstr.fold
    (fun id conf acc ->
       let name = conf.Whyconf.name in
       printf " %s, " name;
       { prover = Db.get_prover name;
         command = conf.Whyconf.command;
         driver = get_driver id; } :: acc
    ) config.provers []
  in
  printf "@\n===============================@.";
  l 
   
let () = 
  printf "previously known goals:@\n";
  List.iter (fun s -> printf "%s@\n" (Db.goal_task_checksum s)) (Db.root_goals ());
  printf "@."


(***************************)
(* Process input theories  *)
(* add corresponding tasks *)
(***************************)

let add_task (tname : string) (task : Why.Task.task) acc =
  let name = (Why.Task.task_goal task).Why.Decl.pr_name.Why.Ident.id_string in
  eprintf "doing task: tname=%s, name=%s@." tname name;
  Db.add_or_replace_task ~tname ~name task :: acc

let do_theory tname th glist =
  let tasks = Why.Task.split_theory th None in
  List.fold_right (add_task tname) tasks glist


(****************)
(* goals widget *)
(****************)

module Ide_goals = struct

  let cols = new GTree.column_list
  let column = cols#add Gobject.Data.string

  let renderer = GTree.cell_renderer_text [`XALIGN 0.] 
  let vcolumn = 
    GTree.view_column ~title:"Goals" 
      ~renderer:(renderer, ["text", column]) () 

  let () = 
    vcolumn#set_resizable true;
    vcolumn#set_max_width 400

  let create ~packing () =
    let model = GTree.tree_store cols in
    let view = GTree.view ~model ~packing () in
    let _ = view#selection#set_mode `SINGLE in
    let _ = view#set_rules_hint true in
    ignore (view#append_column vcolumn);
    model

  let clear model = model#clear ()

  let add_goals (model : GTree.tree_store) th =
    let rec fill parent ns =
      let add_s k s _ = 
	let row = model#append ~parent () in
	model#set ~row ~column (k ^ s)
      in
(*
      Mnm.iter (add_s "type ")  ns.ns_ts;
      Mnm.iter (add_s "logic ") ns.ns_ls;
*)
      Theory.Mnm.iter (add_s "prop ")  ns.Theory.ns_pr;
(*
      let add_ns s ns =
	let row = model#append ~parent () in
	model#set ~row ~column s;
	fill row ns
      in
      Mnm.iter add_ns ns.ns_ns
*)
    in
    let row = model#append () in
    model#set ~row ~column (th.Theory.th_name.Ident.id_string : string);
    fill row th.Theory.th_export

end


(* windows, etc *)

let main () =
  let w = GWindow.window 
    ~allow_grow:true ~allow_shrink:true
    ~width:window_width ~height:window_height 
    ~title:"why-ide" ()
  in
  let _ = w#connect#destroy ~callback:(fun () -> exit 0) in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  (* Menu *)
  let menubar = GMenu.menu_bar ~packing:vbox#pack () in
  let factory = new GMenu.factory menubar in
  let accel_group = factory#accel_group in
  let file_menu = factory#add_submenu "_File" in
  let file_factory = new GMenu.factory file_menu ~accel_group in
  let _ = 
    file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"_Quit" 
      ~callback:(fun () -> exit 0) () 
  in

  (* horizontal paned *)
  let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in

  (* left tree of namespace *)
  let scrollview = 
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~width:(window_width / 3) ~packing:hp#add () 
  in
  let _ = scrollview#set_shadow_type `ETCHED_OUT in

  let goals_view = Ide_goals.create ~packing:scrollview#add () in
  Theory.Mnm.iter (fun _ th -> Ide_goals.add_goals goals_view th) theories;

  (* source view *)
  let scrolled_win = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~packing:hp#add ()
  in
  let source_view =
    GSourceView2.source_view
      ~auto_indent:true
      ~insert_spaces_instead_of_tabs:true ~tab_width:2
      ~show_line_numbers:true
      ~right_margin_position:80 ~show_right_margin:true
      (* ~smart_home_end:true *)
      ~packing:scrolled_win#add ~height:500 ~width:650
      ()
  in
  source_view#misc#modify_font_by_name font_name;
  source_view#source_buffer#set_language lang;
  source_view#set_highlight_current_line true;
  source_view#source_buffer#set_text source_text;
 
  w#add_accel_group accel_group;
  w#show ()

let () =
  main ();
  GtkThread.main ()

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/whyide.opt"
End: 
*)
