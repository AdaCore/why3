
open Format
open Why3
open Gconfig

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

let () =
  Debug.dprintf debug "[GUI] Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  Debug.dprintf debug " done.@.";
  Gconfig.init ()

(***************)
(* Main window *)
(***************)

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

(* temporary *)
let _ = GMisc.label ~text:"scrollview" ~packing:scrollview#add ()

let vbox222 = GPack.vbox ~packing:hp#add ()

(* vbox222 contains:
   2.2.2.1 a view of the current task
   2.2.2.2 a input field to type commands
 *)

let scrolled_task_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:vbox222#add
    ()

let task_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ()

(* temporary *)
let () =
  task_view#source_buffer#set_text "this is the current proof task"

let command_entry =
  let e = GEdit.entry ~packing:vbox222#add () in
  let (_ : GtkSignal.id) =
    e#connect#activate ~callback:
      (fun () -> task_view#source_buffer#set_text e#text)
  in e


(* start the interface *)

let () =
  main_window#add_accel_group accel_group;
  main_window#set_icon (Some !Gconfig.why_icon);
  main_window#show ();
  GMain.main ()
