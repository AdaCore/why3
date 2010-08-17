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
(*
      if not (Filename.check_suffix f ".why") then 
	raise (Arg.Bad ("don't know what to do with " ^ f));
*)
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
(*
  | Driver.Error e ->
      Driver.report fmt e
*)
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

let find_prover s =
  match
    List.fold_left
      (fun acc p ->
         if Db.prover_name p.prover = s then Some p else acc)
      None provers_data
  with
    | None -> assert false
    | Some p -> p

let alt_ergo = find_prover "Alt-Ergo"
let simplify = find_prover "simplify"
let z3 = find_prover "Z3"


   
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
  let tasks = Why.Task.split_theory th None None in
  List.fold_right (add_task tname) tasks glist


(****************)
(* goals widget *)
(****************)

module Ide_goals = struct

  let cols = new GTree.column_list
  let name_column = cols#add Gobject.Data.string
  let id_column = cols#add Gobject.Data.caml
  let status_column = cols#add GtkStock.conv

  let renderer = GTree.cell_renderer_text [`XALIGN 0.] 
  let icon_renderer = GTree.cell_renderer_pixbuf [ `STOCK_SIZE `BUTTON ]

  let view_name_column = 
    GTree.view_column ~title:"Theories/Goals" 
      ~renderer:(renderer, ["text", name_column]) () 

  let () = 
    view_name_column#set_resizable true;
    view_name_column#set_max_width 400

  let view_status_column = 
    GTree.view_column ~title:"Status" 
      ~renderer:(icon_renderer, ["stock_id", status_column]) ()

  let () = 
    view_status_column#set_resizable false;
    view_status_column#set_visible true


  let create ~packing () =
    let model = GTree.tree_store cols in
    let view = GTree.view ~model ~packing () in
    let _ = view#selection#set_mode `SINGLE in
    let _ = view#set_rules_hint true in
    ignore (view#append_column view_name_column);
    ignore (view#append_column view_status_column);
    model,view

  let clear model = model#clear ()

  let goal_table = Ident.Hid.create 17

  let get_goal id = fst (Ident.Hid.find goal_table id)

  let add_goals (model : GTree.tree_store) th =
    let tname = th.Theory.th_name.Ident.id_string in
    let parent = model#append () in
    model#set ~row:parent ~column:name_column tname;
    model#set ~row:parent ~column:id_column th.Theory.th_name;
    (* model#set ~row:parent ~column:status_column `REMOVE; *)
    let tasks = Task.split_theory th None None in
    List.iter
      (fun t->
         let id = (Task.task_goal t).Decl.pr_name in
         let name = id.Ident.id_string in
         let g = Db.add_or_replace_task ~tname ~name t in
	 let row = model#append ~parent () in
         Ident.Hid.add goal_table id (g,row);
	 model#set ~row ~column:name_column name;
	 model#set ~row ~column:id_column id;
(*         model#set ~row ~column:status_column `REMOVE; *)
      )
      tasks

end

(****************)
(* windows, etc *)
(****************)

let move_to_line (v : GText.view) line = 
  if line <= v#buffer#line_count && line <> 0 then begin
    let it = v#buffer#get_iter (`LINE line) in 
    let mark = `MARK (v#buffer#create_mark it) in
    v#scroll_to_mark ~use_align:true ~yalign:0.5 mark
  end

(* to be run when a row in the tree view is selected *)
let select_goals (goals_view:GTree.tree_store) (task_view:GSourceView2.source_view) 
   (_source_view:GSourceView2.source_view) selected_rows = 
  List.iter
    (fun p ->
       let row = goals_view#get_iter p in
       let id = goals_view#get ~row ~column:Ide_goals.id_column in
       Format.eprintf "You clicked on %s@." id.Ident.id_string;
       let g = Ide_goals.get_goal id in
       let task_text = Pp.string_of Pretty.print_task (Db.goal_task g) in
       task_view#source_buffer#set_text task_text;
       task_view#scroll_to_mark `INSERT

(*
       match origin with
         | Ident.User (_loc,_) -> ()
             move_to_line source_view#as_view loc.Lexing.pos_lnum
         | _ -> ()
*)
    )
    selected_rows


let stock_of_result = function
  | Db.Scheduled -> `ADD
  | Db.Running -> `EXECUTE
  | Db.Success -> `YES
  | Db.Timeout -> `CUT
  | Db.Unknown -> `DIALOG_QUESTION
  | Db.HighFailure -> `PREFERENCES

let count = ref 0

let async f = GtkThread.async f ()

let prover_on_all_goals ~(model:GTree.tree_store) ~(view:GTree.view) p () =
  Ident.Hid.iter
    (fun id (g,row) ->
       let name = Db.prover_name p.prover in
       Format.eprintf "running %s on goal %s@." name id.Ident.id_string;
       let prover_row = model#append ~parent:row () in
       model#set ~row:prover_row ~column:Ide_goals.name_column name;
       view#expand_row (model#get_path row);
       incr count;
       let c = !count in
       let callback result =
         printf "Scheduled task #%d: status set to %a@." c
           Db.print_status result;         
         model#set ~row:prover_row ~column:Ide_goals.status_column (stock_of_result result);         
       in
       Scheduler.schedule_proof_attempt
         ~async
         ~debug:true ~timelimit ~memlimit:0 
         ~prover:p.prover ~command:p.command ~driver:p.driver 
         ~callback
         g
    )
    Ide_goals.goal_table

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
  let tools_menu = factory#add_submenu "_Tools" in
  let tools_factory = new GMenu.factory tools_menu ~accel_group in

  (* horizontal paned *)
  let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in

  (* left tree of namespace *)
  let scrollview = 
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~width:(window_width / 3) ~packing:hp#add () 
  in
  let _ = scrollview#set_shadow_type `ETCHED_OUT in

  let goals_model,goals_view = Ide_goals.create ~packing:scrollview#add () in
  Theory.Mnm.iter (fun _ th -> Ide_goals.add_goals goals_model th) theories;
  let _ = 
    tools_factory#add_image_item ~key:GdkKeysyms._A 
      ~label:"Alt-Ergo on all goals" 
      ~callback:(fun () -> 
                   prover_on_all_goals ~model:goals_model ~view:goals_view 
                     alt_ergo ();
                   prover_on_all_goals ~model:goals_model ~view:goals_view 
                     simplify ();
                   prover_on_all_goals ~model:goals_model ~view:goals_view 
                     z3 ()) () 
  in
  let _ = 
    tools_factory#add_image_item ~key:GdkKeysyms._E 
      ~label:"Expand all" ~callback:(fun () -> goals_view#expand_all ()) () 
  in


  (* horizontal paned *)
  let vp = GPack.paned `VERTICAL  ~border_width:3 ~packing:hp#add () in

  (* goal text view *)
  let scrolled_task_view = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~packing:vp#add ()
  in
  let task_view =
    GSourceView2.source_view
      ~editable:false
      ~show_line_numbers:true
      ~packing:scrolled_task_view#add ~height:500 ~width:650
      ()
  in
  task_view#source_buffer#set_language lang;
  task_view#set_highlight_current_line true;
  
  (* source view *)
  let scrolled_source_view = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~packing:vp#add ()
  in
  let source_view =
    GSourceView2.source_view
      ~auto_indent:true
      ~insert_spaces_instead_of_tabs:true ~tab_width:2
      ~show_line_numbers:true
      ~right_margin_position:80 ~show_right_margin:true
      (* ~smart_home_end:true *)
      ~packing:scrolled_source_view#add ~height:500 ~width:650
      ()
  in
(*
  source_view#misc#modify_font_by_name font_name;
*)
  source_view#source_buffer#set_language lang;
  source_view#set_highlight_current_line true;
  source_view#source_buffer#set_text source_text;

(* Bind event: row selection on tree view on the left *) 
  let _ =
    goals_view#selection#connect#after#changed ~callback:
      begin fun () ->
	let list = goals_view#selection#get_selected_rows in
        select_goals goals_model task_view source_view list
      end
  in

  w#add_accel_group accel_group;
  w#show ()

let () =
  main ();
  GtkThread.main ()

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/why-ide.byte"
End: 
*)
