
open Format
open Why3
open Gconfig
open Stdlib
open Session_itp
open Controller_itp

let debug = Debug.lookup_flag "ide_info"

(************************)
(* parsing command line *)
(************************)

let files = Queue.create ()
let opt_parser = ref None

let spec = Arg.align [
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
(*
  "-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<file> add file to the project (ignored if it is already there)";
*)
  Termcode.arg_extra_expl_prefix
]

let usage_str = sprintf
  "Usage: %s [options] [<file.why>|<project directory>]..."
  (Filename.basename Sys.argv.(0))

let gconfig = try
  let config, base_config, env =
    Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str in
  if Queue.is_empty files then Whyconf.Args.exit_with_usage spec usage_str;
  Gconfig.load_config config base_config env;
  Gconfig.config ()

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let task_driver =
  let main = Whyconf.get_main gconfig.config in
  let d = Filename.concat (Whyconf.datadir main)
                          (Filename.concat "drivers" "why3_itp.drv")
  in
  Driver.load_driver gconfig.env d []


let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers gconfig.config

let cont =
  Session_user_interface.cont_from_files spec usage_str gconfig.env files provers

let () =
  Debug.dprintf debug "[GUI] Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  Debug.dprintf debug " done.@.";
  Gconfig.init ()


(**********************)
(* Graphical elements *)
(**********************)

let main_window =
  let w = GWindow.window
            ~allow_grow:true ~allow_shrink:true
            ~width:gconfig.window_width
            ~height:gconfig.window_height
            ~title:"Why3 Interactive Proof Session" ()
  in
  (* callback to record the new size of the main window when changed, so
   that on restart the window size is the same as the last session *)
  let (_ : GtkSignal.id) =
    w#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=h} ->
       gconfig.window_height <- h;
       gconfig.window_width <- w)
  in w

(* the main window contains a vertical box, containing:
   1. the menu
   2. an horizontal box
 *)

let vbox = GPack.vbox ~packing:main_window#add ()

let menubar = GMenu.menu_bar
  ~packing:(vbox#pack ?from:None ?expand:None ?fill:None ?padding:None)
  ()

let hb = GPack.hbox ~packing:vbox#add ()

(* 1. Menu *)

let factory = new GMenu.factory menubar

let accel_group = factory#accel_group

let file_menu = factory#add_submenu "_File"
let file_factory = new GMenu.factory file_menu ~accel_group

let exit_function ~destroy () =
  ignore(destroy); GMain.quit ()

let (_ : GtkSignal.id) = main_window#connect#destroy
  ~callback:(exit_function ~destroy:true)

let (_ : GMenu.menu_item) =
  file_factory#add_item ~key:GdkKeysyms._Q "_Quit"
    ~callback:(exit_function ~destroy:false)

(* 2. horizontal box contains:
   2.1 TODO: a tool box ?
   2.2 a horizontal paned containing:
     2.2.1 a scrolled window to hold the tree view of the session
     2.2.2 a vertical box
*)

let hp = GPack.paned `HORIZONTAL ~packing:hb#add ()

let scrollview =
  let sv =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~width:gconfig.tree_width ~shadow_type:`ETCHED_OUT
      ~packing:hp#add ()
  in
  let (_ : GtkSignal.id) =
    sv#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=_h} ->
       gconfig.tree_width <- w)
  in sv

let vbox222 = GPack.vbox ~packing:hp#add ()

(*  the scrolled window 2.2.1 contains a GTK tree

*)


(* view for the session tree *)
let scrolled_session_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:scrollview#add
    ()

let cols = new GTree.column_list
let name_column = cols#add Gobject.Data.string
let index_column = cols#add Gobject.Data.int

let name_renderer = GTree.cell_renderer_text [`XALIGN 0.]
let view_name_column = GTree.view_column ~title:"Theories/Goals" ()
let () =
  view_name_column#pack name_renderer;
  view_name_column#add_attribute name_renderer "text" name_column

let goals_model,goals_view =
  Debug.dprintf debug "[GUI] Creating tree model...@?";
  let model = GTree.tree_store cols in
  let view = GTree.view ~model ~packing:scrolled_session_view#add () in
(*
  let () = view#selection#set_mode (* `SINGLE *) `MULTIPLE in
  let () = view#set_rules_hint true in
 *)
  ignore (view#append_column view_name_column);
(*
  ignore (view#append_column view_status_column);
  ignore (view#append_column view_time_column);
*)
  Debug.dprintf debug " done@.";
  model,view

(* vbox222 contains:
   2.2.2.1 a view of the current task
   2.2.2.2 a input field to type commands
 *)

let scrolled_task_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:(vbox222#pack ?from:None ~expand:true ~fill:true ?padding:None)
    ()

let task_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ()


let command_entry = GEdit.entry ~packing:vbox222#add ()
let message_zone =
  GText.view ~editable:false ~cursor_visible:false
             ~packing:(vbox222#pack ?from:None ~expand:true ~fill:true ?padding:None) ()


(********************************************)
(* controller instance on the GTK scheduler *)
(********************************************)


module S = struct
    let idle ~prio f =
      let (_ : GMain.Idle.id) = GMain.Idle.add ~prio f in ()

    let timeout ~ms f =
      let (_ : GMain.Timeout.id) = GMain.Timeout.add ~ms ~callback:f in
      ()
end

module C = Controller_itp.Make(S)


(***********************************)
(* Mapping session to the GTK tree *)
(***********************************)

type index =
  | Inone
  | IproofAttempt of proofAttemptID
  | IproofNode of proofNodeID
  | Itransformation  of transID
  | Ifile of file
  | Itheory of theory

let model_index : index Hint.t = Stdlib.Hint.create 17
(* To each proofnodeid we have the corresponding row_reference *)
let pn_id_to_gtree : GTree.row_reference Hpn.t = Hpn.create 17
let pan_id_to_gtree : GTree.row_reference Hpan.t = Hpan.create 17


let new_node =
  let cpt = ref (-1) in
  fun ?parent ?(collapse=false) name ind ->
  incr cpt;
  Hint.add model_index !cpt ind;
  let parent = Opt.map (fun x -> x#iter) parent in
  let iter = goals_model#append ?parent () in
  goals_model#set ~row:iter ~column:name_column name;
  goals_model#set ~row:iter ~column:index_column !cpt;
  let new_ref = goals_model#get_row_reference (goals_model#get_path iter) in
  (* By default expand_path when creating a new node *)
  if not collapse then goals_view#expand_to_path (goals_model#get_path iter);
  begin
    match ind with
    | IproofAttempt panid ->
       Hpan.add pan_id_to_gtree panid new_ref
    | IproofNode pnid ->
       Hpn.add pn_id_to_gtree pnid new_ref
    | _ -> ()
  end;
  new_ref

let build_subtree_proof_attempt_from_goal ses row_ref id =
  Whyconf.Hprover.iter
    (fun pa panid ->
     let name = Pp.string_of Whyconf.print_prover pa in
      ignore(new_node ~parent:row_ref name
                 (IproofAttempt panid)))
    (get_proof_attempt_ids ses id)

let rec build_subtree_from_goal ses th_row_reference id =
  let name = get_proof_name ses id in
  let row_ref =
    new_node ~parent:th_row_reference name.Ident.id_string
             (IproofNode id)
  in
  List.iter
    (fun trans_id ->
      build_subtree_from_trans ses row_ref trans_id)
    (get_transformations ses id);
  build_subtree_proof_attempt_from_goal ses row_ref id

and build_subtree_from_trans ses goal_row_reference trans_id =
  let name = get_transf_name ses trans_id in
  let row_ref =
    new_node ~parent:goal_row_reference name (Itransformation trans_id) in
  List.iter
    (fun goal_id ->
      (build_subtree_from_goal ses row_ref goal_id))
    (get_sub_tasks ses trans_id)

let build_tree_from_session ses =
  let files = get_files ses in
  Stdlib.Hstr.iter
    (fun _ file ->
       let file_row_reference = new_node file.file_name (Ifile file) in
       List.iter (fun th ->
                  let th_row_reference =
                    new_node ~parent:file_row_reference
                             (theory_name th).Ident.id_string
                             (Itheory th)
                  in
                  List.iter (build_subtree_from_goal ses th_row_reference)
                            (theory_goals th))
                 file.file_theories)
    files

(******************)
(*    actions     *)
(******************)

(* TODO We currently use this for transformations etc... With strategies, we sure
   do not want to move the current index with the computing of strategy. *)
let current_selected_index = ref Inone

let run_strategy_on_task s =
  match !current_selected_index with
  | IproofNode id ->
     let l = Session_user_interface.strategies
               cont.controller_env gconfig.config
     in
     let st = List.filter (fun (_,c,_,_) -> c=s) l in
     begin
       match st with
       | [(n,_,_,st)] ->
          printf "running strategy '%s'@." n;
          let callback sts =
            printf "Strategy status: %a@." print_strategy_status sts
          in
          C.run_strategy_on_goal cont id st ~callback
    | _ -> printf "Strategy '%s' not found@." s
     end
  | _ -> ()


(* TODO maybe an other file for callbacks *)
(* Callback of a transformation *)
let callback_update_tree_transform ses row_reference = fun status ->
  match status with
  | TSdone trans_id ->
      build_subtree_from_trans ses row_reference trans_id;
      (match Session_itp.get_sub_tasks ses trans_id with
      | first_goal :: _ ->
          (* Put the selection on the first goal *)
          goals_view#selection#select_iter (Hpn.find pn_id_to_gtree first_goal)#iter
      | [] -> ())
  | _ -> ()

let apply_transform ses t args =
  match !current_selected_index with
  | IproofNode id ->
    let row_ref = Hpn.find pn_id_to_gtree id in (* TODO exception *)
    let callback =
         callback_update_tree_transform ses row_ref
       in
       C.schedule_transformation cont id t args ~callback
    | _ -> printf "Error: Give the name of the transformation@."


let remove_children iter =
  if (goals_model#iter_has_child iter) then
    ignore (goals_model#remove (goals_model#iter_children (Some iter)))
  else ()

(*
  match (goals_model#iter_children row_reference) with
  | None -> ()
  | iter -> goals_model#remove iter
*)

(* Callback of a proof_attempt *)
let callback_update_tree_proof _ses row_ref _id name =
  fun panid pa_status ->
  match pa_status with
    | Scheduled ->
       begin
       try
         let _new_row_ref = Hpan.find pan_id_to_gtree panid in
         () (* TODO: set icon to 'pause' *)
       with Not_found ->
            ignore(new_node ~parent:row_ref (name ^ " scheduled") (IproofAttempt panid))
       end
  | Done _pr ->
       begin
       try
         let r = Hpan.find pan_id_to_gtree panid in
         goals_model#set ~row:r#iter ~column:name_column (name ^ " done")
       with Not_found -> assert false
       end
  | Running -> () (* TODO: set icon to 'play' *)
  | _ ->  () (* TODO ? *)

(* TODO to be replaced *)
(* Return the prover corresponding to given name. name is of the form
  | name
  | name, version
  | name, altern
  | name, version, altern *)
let return_prover fmt name =
  let fp = Whyconf.parse_filter_prover name in
  (** all provers that have the name/version/altern name *)
  let provers = Whyconf.filter_provers gconfig.config fp in
  if Whyconf.Mprover.is_empty provers then begin
    fprintf fmt "Prover corresponding to %s has not been found@." name;
    None
  end else
    Some (snd (Whyconf.Mprover.choose provers))

let test_schedule_proof_attempt ses =
  match !current_selected_index with
  | IproofNode id ->
    let row_ref = Hpn.find pn_id_to_gtree id in
    (* TODO put this somewhere else *)
    let name, limit = match ["Alt-Ergo,1.01"; "10"] with
    (* TODO recover this
      | [name] ->
        let default_limit = Call_provers.{limit_time = Whyconf.timelimit main;
                                          limit_mem = Whyconf.memlimit main;
                                          limit_steps = 0} in
        name, default_limit*)
    | [name; timeout] -> name, Call_provers.{empty_limit with
                                           limit_time = int_of_string timeout}
    | [name; timeout; oom ] ->
        name, Call_provers.{limit_time = int_of_string timeout;
                            limit_mem = int_of_string oom;
                            limit_steps = 0}
  | _ -> printf "Bad arguments prover_name, version timeout memlimit@.";
      "", Call_provers.empty_limit
  in
  let np = return_prover Format.std_formatter name in (* TODO std_formatter dummy argument *)
  (match np with
  | None -> ()
  | Some p ->
     let np = Pp.string_of Whyconf.print_prover p.Whyconf.prover in
     let callback = callback_update_tree_proof ses row_ref id np in
      C.schedule_proof_attempt
        cont id p.Whyconf.prover
        ~limit ~callback)
  | _ -> () (* TODO *)
(*    | _ -> printf "Give the prover name@."*)


let clear_command_entry () = command_entry#set_text ""

open Session_user_interface

let interp cmd =
  match interp cont.controller_env cmd with
    | Transform(s,_t,args) ->
       clear_command_entry ();
       apply_transform cont.controller_session s args
    | Query s ->
       message_zone#buffer#set_text s
    | Other(s,_args) ->
       match s with
       | "s" -> clear_command_entry ();
                run_strategy_on_task "1"
       | "c" -> clear_command_entry ();
                test_schedule_proof_attempt cont.controller_session
       | _ -> message_zone#buffer#set_text ("unknown command '"^s^"'")

let (_ : GtkSignal.id) =
  command_entry#connect#activate
    ~callback:(fun () -> interp command_entry#text)


let get_selected_row_references () =
  List.map
    (fun path -> goals_model#get_row_reference path)
    goals_view#selection#get_selected_rows

let on_selected_row r =
  let index = goals_model#get ~row:r#iter ~column:index_column in
  try
    let session_element = Hint.find model_index index in
    let () = match session_element with
             | IproofNode id -> Hpn.add pn_id_to_gtree id r (* TODO maybe not the good place to fill
                                                                    this table *)
             | _ -> () in
    current_selected_index := session_element;
    match session_element with
    | IproofNode id ->
       let task = get_task cont.controller_session id in
       let s = Pp.string_of
                 (Driver.print_task ~cntexample:false task_driver)
                 task
       in task_view#source_buffer#set_text s
    | _ -> task_view#source_buffer#set_text ""
  with
    | Not_found -> task_view#source_buffer#set_text ""

let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    (fun () ->
      match get_selected_row_references () with
        | [r] -> on_selected_row r
        | _ -> ())

(***********************)
(* start the interface *)
(***********************)

let () =
  build_tree_from_session cont.controller_session;
  (* temporary *)
  goals_view#expand_all ();
  main_window#add_accel_group accel_group;
  main_window#set_icon (Some !Gconfig.why_icon);
  main_window#show ();
  GMain.main ()
