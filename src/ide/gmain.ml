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

let pname = "[Why Ide]"

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
(*
let font_name = "Monospace 10"
*)

let spec = [
]

let usage_str = "whyide [options] <file>.why"
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

(*
let () = Db.init_base (fname ^ ".db")
*)

let get_driver name = 
  let pi = Util.Mstr.find name config.provers in
  Why.Driver.load_driver env pi.Whyconf.driver

type prover_data =
    { prover : string (* Db.prover *);
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
       { prover = (* Db.get_prover *) name;
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
         if (* Db.prover_name *) p.prover = s then Some p else acc)
      None provers_data
  with
    | None -> assert false
    | Some p -> p

let alt_ergo = find_prover "Alt-Ergo"
let simplify = find_prover "simplify"
let z3 = find_prover "Z3"


   
(*
let () = 
  printf "previously known goals:@\n";
  List.iter (fun s -> printf "%s@\n" (Db.goal_task_checksum s)) (Db.root_goals ());
  printf "@."
*)


(*

  boomy icons

*)

let image ?size f =
  let n = Filename.concat "" (* todo: libdir *) (Filename.concat "images" (f^".png"))
  in
  match size with
    | None ->
        GdkPixbuf.from_file n
    | Some s ->
        GdkPixbuf.from_file_at_size ~width:s ~height:s n

let iconname_default = "pause32"
let iconname_scheduled = "pause32"
let iconname_running = "play32"
let iconname_valid = "accept32"
let iconname_unknown = "help32"
let iconname_invalid = "delete32"
let iconname_timeout = "clock32"
let iconname_failure = "bug32"
let iconname_yes = "accept32"
let iconname_no = "delete32"
let iconname_directory = "folder32"
let iconname_file = "file32"
let iconname_prover = "wizard32"
let iconname_transf = "cutb32"

let image_default = ref (image ~size:20 iconname_default)
let image_scheduled = ref !image_default
let image_running = ref !image_default
let image_valid = ref !image_default
let image_unknown = ref !image_default
let image_invalid = ref !image_default
let image_timeout = ref !image_default
let image_failure = ref !image_default
let image_yes = ref !image_default
let image_no = ref !image_default
let image_directory = ref !image_default
let image_file = ref !image_default
let image_prover = ref !image_default
let image_transf = ref !image_default

let resize_images size =
  image_default := image ~size iconname_default;
  image_scheduled := image ~size iconname_scheduled;
  image_running := image ~size iconname_running;
  image_valid := image ~size iconname_valid;
  image_unknown := image ~size iconname_unknown;
  image_invalid := image ~size iconname_invalid;
  image_timeout := image ~size iconname_timeout;
  image_failure := image ~size iconname_failure;
  image_yes := image ~size iconname_yes;
  image_no := image ~size iconname_no;
  image_directory := image ~size iconname_directory;
  image_file := image ~size iconname_file;
  image_prover := image ~size iconname_prover;
  image_transf := image ~size iconname_transf;
  ()

let () = resize_images 20

(****************)
(* goals widget *)
(****************)


module Model = struct


  type proof_attempt =
      { prover : prover_data;
        status : Scheduler.proof_attempt_status;
        time : float;
        output : string;
      }

  type goal_parent =
    | Theory of theory
    | Transf of transf

  and goal =
      { parent : goal_parent;
        task: Task.task;
        goal_row : Gtk.tree_iter;
        mutable proved : bool;
        mutable external_proofs: proof_attempt list;
        mutable transformations : transf list;
      }

  and transf =
      { parent_goal : goal;
(*
        transf : Task.task Trans.trans;
*)
        transf_row : Gtk.tree_iter;
        mutable subgoals : goal list;
      }
        
  and theory =
      { theory : Theory.theory;
        theory_row : Gtk.tree_iter;
        mutable goals : goal list;
        mutable verified : bool;
      }

  let all : theory list ref = ref [] 

  let cols = new GTree.column_list
  let name_column = cols#add Gobject.Data.string
  let icon_column = cols#add Gobject.Data.gobject
  let id_column = cols#add Gobject.Data.caml
  let status_column = cols#add Gobject.Data.gobject
  let time_column = cols#add Gobject.Data.string
  let visible_column = cols#add Gobject.Data.boolean
(*
  let bg_column = cols#add (Gobject.Data.unsafe_boxed (Gobject.Type.from_name "GdkColor"))
*)

  let name_renderer = GTree.cell_renderer_text [`XALIGN 0.] 
  let renderer = GTree.cell_renderer_text [`XALIGN 0.] 
  let image_renderer = GTree.cell_renderer_pixbuf [ ] 
  let icon_renderer = GTree.cell_renderer_pixbuf [ ]

  let view_name_column = 
    GTree.view_column ~title:"Theories/Goals" ()

  let () = 
    view_name_column#pack icon_renderer ;
    view_name_column#add_attribute icon_renderer "pixbuf" icon_column ;
    view_name_column#pack name_renderer;
    view_name_column#add_attribute name_renderer "text" name_column;
    view_name_column#set_resizable true;
    view_name_column#set_max_width 400;
(*
    view_name_column#add_attribute name_renderer "background-gdk" bg_column
*)
    ()

  let view_status_column = 
    GTree.view_column ~title:"Status" 
      ~renderer:(image_renderer, ["pixbuf", status_column]) 
      ()

  let view_time_column = 
    GTree.view_column ~title:"Time" 
      ~renderer:(renderer, ["text", time_column]) ()

  let () = 
    view_status_column#set_resizable false;
    view_status_column#set_visible true;
    view_time_column#set_resizable false;
    view_time_column#set_visible true


  let create ~packing () =
    let model = GTree.tree_store cols in
    let model_filter = GTree.model_filter model in
    model_filter#set_visible_column visible_column;
    let view = GTree.view ~model:model_filter ~packing () in
    let _ = view#selection#set_mode `SINGLE in
    let _ = view#set_rules_hint true in
    ignore (view#append_column view_name_column);
    ignore (view#append_column view_status_column);
    ignore (view#append_column view_time_column);
    model,model_filter,view

  let clear model = model#clear ()

  let goal_table = Ident.Hid.create 17

  let get_goal id = fst (Ident.Hid.find goal_table id)

end

(***************)
(* Main window *)
(***************)

let w = GWindow.window 
  ~allow_grow:true ~allow_shrink:true
  ~width:window_width ~height:window_height 
  ~title:"why-ide" ()

let (_ : GtkSignal.id) = w#connect#destroy ~callback:(fun () -> exit 0) 

let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () 

(* Menu *)

let menubar = GMenu.menu_bar ~packing:vbox#pack () 

let factory = new GMenu.factory menubar 

let accel_group = factory#accel_group 

(* horizontal paned *)

let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () 

(* tree view *)
let scrollview = 
  GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~width:(window_width / 3) ~packing:hp#add () 

let () = scrollview#set_shadow_type `ETCHED_OUT 

let goals_model,filter_model,goals_view = Model.create ~packing:scrollview#add () 

module Helpers = struct

  open Model

  let set_theory_proved t =
    t.verified <- true;
    let row = t.theory_row in
    goals_model#set ~row ~column:Model.status_column !image_yes;
    goals_view#collapse_row (goals_model#get_path row)
    
  let rec set_proved g =
    let row = g.goal_row in
    g.proved <- true;
    goals_view#collapse_row (goals_model#get_path row);
    goals_model#set ~row ~column:Model.status_column !image_yes;
    match g.parent with
      | Theory t ->
          if List.for_all (fun g -> g.proved) t.goals then
            set_theory_proved t
      | Transf t ->
          if List.for_all (fun g -> g.proved) t.subgoals then
            begin
              set_proved t.parent_goal;
            end
              

  let add_theory th =
    let tname = th.Theory.th_name.Ident.id_string in
    let parent = goals_model#append () in
    let mth = { theory = th; 
                theory_row = parent; 
                goals = [] ; 
                verified = false } 
    in
    all := !all @ [mth];
    goals_model#set ~row:parent ~column:name_column tname;
    goals_model#set ~row:parent ~column:icon_column !image_directory;
    goals_model#set ~row:parent ~column:id_column th.Theory.th_name;
    goals_model#set ~row:parent ~column:visible_column true;
    let tasks = Task.split_theory th None None in
    let goals =
      List.fold_left
        (fun acc t ->
           let id = (Task.task_goal t).Decl.pr_name in
           let name = id.Ident.id_string in
           let row = goals_model#append ~parent () in
           Ident.Hid.add goal_table id (t,row);
	   goals_model#set ~row ~column:name_column name;
           goals_model#set ~row ~column:icon_column !image_file;
	   goals_model#set ~row ~column:id_column id;
           goals_model#set ~row ~column:visible_column true;
           let goal = { parent = Theory mth; 
                        task = t ; 
                        goal_row = row;
                        external_proofs = [];
                        transformations = [];
                        proved = false;
                      }
           in
           goal :: acc
        )
        []
        (List.rev tasks)
    in
    mth.goals <- List.rev goals;
    if goals = [] then set_theory_proved mth
    

end

let () = 
  Theory.Mnm.iter (fun _ th -> Helpers.add_theory th) theories


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
let select_goals (filter_model : GTree.model_filter) 
    (task_view:GSourceView2.source_view) 
    (_source_view:GSourceView2.source_view) selected_rows = 
  List.iter
    (fun p ->
       let row = filter_model#get_iter p in
       let id = filter_model#get ~row ~column:Model.id_column in
       Format.eprintf "You clicked on %s@." id.Ident.id_string;
       try
         let g = Model.get_goal id in
         let task_text = Pp.string_of Pretty.print_task g in
         task_view#source_buffer#set_text task_text;
         task_view#scroll_to_mark `INSERT
       with Not_found -> ()

(*
       match origin with
         | Ident.User (_loc,_) -> ()
             move_to_line source_view#as_view loc.Lexing.pos_lnum
         | _ -> ()
*)
    )
    selected_rows


let image_of_result = function
  | Scheduler.Scheduled -> !image_scheduled
  | Scheduler.Running -> !image_running
  | Scheduler.Success -> !image_valid
  | Scheduler.Timeout -> !image_timeout
  | Scheduler.Unknown -> !image_unknown
  | Scheduler.HighFailure -> !image_failure

let () = 
  begin
    Scheduler.async := GtkThread.async;
    match config.running_provers_max with
      | None -> ()
      | Some n -> 
          if n >= 1 then Scheduler.maximum_running_proofs := n
  end 

(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

let rec prover_on_goal p g =
  let row = g.Model.goal_row in
  let name = p.prover in
  let prover_row = goals_model#append ~parent:row () in
  goals_model#set ~row:prover_row ~column:Model.icon_column !image_prover;
  goals_model#set ~row:prover_row ~column:Model.name_column ("prover: " ^name);
  goals_model#set ~row:prover_row ~column:Model.visible_column true;
  goals_view#expand_row (goals_model#get_path row);
  let callback result time =
    goals_model#set ~row:prover_row ~column:Model.status_column 
      (image_of_result result);
    let t = if time > 0.0 then Format.sprintf "%.2f" time else "" in
    goals_model#set ~row:prover_row ~column:Model.time_column t;
    if result = Scheduler.Success then
      Helpers.set_proved g
  in
  callback Scheduler.Scheduled 0.0;
  Scheduler.schedule_proof_attempt
    ~debug:false ~timelimit ~memlimit:0 
    ~prover:p.prover ~command:p.command ~driver:p.driver 
    ~callback
    g.Model.task;
  List.iter
    (fun t -> List.iter (prover_on_goal p) t.Model.subgoals)
    g.Model.transformations
    
let prover_on_unproved_goals p () =
  List.iter
    (fun th ->
       List.iter
         (fun g -> if not g.Model.proved then prover_on_goal p g)
         th.Model.goals;
    )
    !Model.all

(*****************************************************)
(* method: split all unproved goals *)
(*****************************************************)

let split_transformation = Trans.lookup_transform_l "split_goal" env

let split_unproved_goals () =
  List.iter
    (fun th ->
       List.iter
         (fun g ->
            if not g.Model.proved then         
              let row = g.Model.goal_row in
              let goal_name = goals_model#get ~row ~column:Model.name_column in
              let callback subgoals =
                if List.length subgoals >= 2 then
                  let split_row = goals_model#append ~parent:row () in
                  goals_model#set ~row:split_row ~column:Model.visible_column true;
                  goals_model#set ~row:split_row ~column:Model.name_column "split";
                  goals_model#set ~row:split_row ~column:Model.icon_column !image_transf;
                  let tr =
                    { Model.parent_goal = g;
(*
                      Model.transf = split_transformation;
*)
                      Model.transf_row = split_row;
                      subgoals = [];
                    }
                  in
                  g.Model.transformations <- tr :: g.Model.transformations;
                  let goals,_ = List.fold_left
                    (fun (acc,count) subtask ->
                       let id = (Task.task_goal subtask).Decl.pr_name in
                       let subtask_row = goals_model#append ~parent:split_row () in
                       Ident.Hid.add Model.goal_table id (subtask,subtask_row);
	               goals_model#set ~row:subtask_row ~column:Model.id_column id;
                       goals_model#set ~row:subtask_row ~column:Model.visible_column true;
                       goals_model#set ~row:subtask_row ~column:Model.name_column 
                         (goal_name ^ "." ^ (string_of_int count));
                       goals_model#set ~row:subtask_row ~column:Model.icon_column !image_file;
                       let goal = { Model.parent = Model.Transf tr; 
                                    Model.task = subtask ; 
                                    Model.goal_row = subtask_row;
                                    Model.external_proofs = [];
                                    Model.transformations = [];
                                    Model.proved = false;
                                  }
                       in
                       (goal :: acc, count+1))
                    ([],1) subgoals 
                  in
                  tr.Model.subgoals <- List.rev goals;
                  goals_view#expand_row (goals_model#get_path row)           
              in
              
              Scheduler.apply_transformation ~callback split_transformation g.Model.task
         )
         th.Model.goals
    )
    !Model.all


(*************)
(* File menu *)
(*************)

let file_menu = factory#add_submenu "_File" 
let file_factory = new GMenu.factory file_menu ~accel_group 
let (_ : GMenu.image_menu_item) = 
  file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"_Quit" 
    ~callback:(fun () -> exit 0) () 

(*************)
(* View menu *)
(*************)

let view_menu = factory#add_submenu "_View" 
let view_factory = new GMenu.factory view_menu ~accel_group 
let (_ : GMenu.image_menu_item) = 
  view_factory#add_image_item ~key:GdkKeysyms._E 
    ~label:"Expand all" ~callback:(fun () -> goals_view#expand_all ()) () 

let rec hide_proved_goal g =
  if g.Model.proved then
    begin
      let row = g.Model.goal_row in
      goals_view#collapse_row (goals_model#get_path row);
      goals_model#set ~row ~column:Model.visible_column false
    end
  else
    List.iter 
      (fun t -> List.iter hide_proved_goal t.Model.subgoals)
      g.Model.transformations

let hide_verified_theories () =
  List.iter
    (fun th ->
       if th.Model.verified then
         begin
           let row = th.Model.theory_row in
           goals_view#collapse_row (goals_model#get_path row);
           goals_model#set ~row ~column:Model.visible_column false
         end
       else
         List.iter hide_proved_goal th.Model.goals)
    !Model.all
    
let show_all_goals () = ()

let (_ : GMenu.check_menu_item) = view_factory#add_check_item 
  ~callback:(function 
               | true -> hide_verified_theories ()
               | false -> show_all_goals ())
  "Hide proved goals"
  

(**************)
(* Tools menu *)
(**************)

let tools_menu = factory#add_submenu "_Tools" 
let tools_factory = new GMenu.factory tools_menu ~accel_group 

let (_ : GMenu.image_menu_item) = 
  tools_factory#add_image_item ~key:GdkKeysyms._S
    ~label:"Simplify on unproved goals" 
    ~callback:(fun () -> prover_on_unproved_goals simplify ()) 
    () 

let (_ : GMenu.image_menu_item) = 
  tools_factory#add_image_item ~key:GdkKeysyms._A 
    ~label:"Alt-Ergo on unproved goals" 
    ~callback:(fun () -> prover_on_unproved_goals alt_ergo ()) 
    () 

let (_ : GMenu.image_menu_item) = 
  tools_factory#add_image_item ~key:GdkKeysyms._Z 
    ~label:"Z3 on unproved goals" 
    ~callback:(fun () -> prover_on_unproved_goals z3 ()) 
    () 
  
let (_ : GMenu.image_menu_item) = 
  tools_factory#add_image_item 
    ~label:"Split unproved goals" 
    ~callback:split_unproved_goals
    () 

(*************)
(* Help menu *)
(*************)

let info_window t s () =
  let d = GWindow.message_dialog
    ~message:s
    ~message_type:`INFO
    ~buttons:GWindow.Buttons.close
    ~title:t
    ~show:true () 
  in
  let (_ : GtkSignal.id) =
    d#connect#response 
      ~callback:(function `CLOSE | `DELETE_EVENT -> d#destroy ())
  in
  ()

let help_menu = factory#add_submenu "_Help" 
let help_factory = new GMenu.factory help_menu ~accel_group 

let (_ : GMenu.image_menu_item) = 
  help_factory#add_image_item 
    ~label:"Legend" 
    ~callback:(info_window "Legend" "This is the legend")
    () 

let (_ : GMenu.image_menu_item) = 
  help_factory#add_image_item 
    ~label:"About" 
    ~callback:(info_window "About" 
                 "This is Why3 preliminary version
Copyright 2010 
Francois Bobot
Jean-Christophe Filliatre
Johannes Kanig
Claude Marche
Andrei Paskevich"
              )
    () 


(******************************)
(* vertical paned on the right*)
(******************************)

let vp = GPack.paned `VERTICAL  ~border_width:3 ~packing:hp#add () 

(******************)
(* goal text view *)
(******************)

let scrolled_task_view = GBin.scrolled_window
  ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
  ~packing:vp#add ()
  
let task_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add ~height:500 ~width:650
    ()

let () = task_view#source_buffer#set_language lang
let () = task_view#set_highlight_current_line true
  
(***************)
(* source view *)
(***************)

let scrolled_source_view = GBin.scrolled_window
  ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
  ~packing:vp#add 
  ()
  
let source_view =
  GSourceView2.source_view
    ~auto_indent:true
    ~insert_spaces_instead_of_tabs:true ~tab_width:2
    ~show_line_numbers:true
    ~right_margin_position:80 ~show_right_margin:true
    (* ~smart_home_end:true *)
    ~packing:scrolled_source_view#add ~height:500 ~width:650
    ()

(*
  source_view#misc#modify_font_by_name font_name;
*)
let () = source_view#source_buffer#set_language lang
let () = source_view#set_highlight_current_line true
let () = source_view#source_buffer#set_text source_text

(***************)
(* Bind events *)
(***************)

(* row selection on tree view on the left *) 
let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    begin fun () ->
      let list = goals_view#selection#get_selected_rows in
      select_goals filter_model task_view source_view list
    end

let () = w#add_accel_group accel_group
let () = w#show () 
let () = GtkThread.main ()

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/whyide.opt"
End: 
*)
