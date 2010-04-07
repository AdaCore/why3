
(* POUR L'INSTANT, CE NE SONT ICI QUE DES EXPÉRIENCES 
   MERCI DE NE PAS CONSIDÉRER CE CODE COMME DÉFINITIF
   -- jcf
*)

open Why
open Theory

let () = ignore (GtkMain.Main.init ())

(* config *)
let window_width = 1024
let window_height = 768
let font_name = "Monospace 10"

(* command line *)
let font_size = ref 10
let font_family = "Monospace"

let file = ref None
let set_file f = match !file with
  | Some _ -> 
      raise (Arg.Bad "only one file, please")
  | None -> 
      if not (Filename.check_suffix f ".why") then 
	raise (Arg.Bad ("don't know what to do with " ^ f));
      if not (Sys.file_exists f) then begin
	Format.eprintf "why-ide: %s: no such file@." f; exit 1
      end;
      file := Some f
let loadpath = ref []

let spec = 
  [
    "-I", Arg.String (fun s -> loadpath := s :: !loadpath), 
    "<dir> Add <dir> to the library search path";
  ]
let usage_str = "why-ide [options] file.why"
let () = Arg.parse spec set_file usage_str

let fname = match !file with
  | None -> 
      Arg.usage spec usage_str; exit 1
  | Some f -> 
      f

let lang =
  let file = 
    List.fold_right Filename.concat 
      [Filename.dirname Sys.argv.(0); ".."; "share"; "lang"] "why.lang" 
  in
  if Sys.file_exists file then 
    let languages_manager = GSourceView.source_languages_manager () in
    GSourceView.source_language_from_file ~languages_manager file
  else begin
    Format.eprintf "could not find lang file (%S)@.";
    None
  end

let text = 
  let ic = open_in fname in
  let size = in_channel_length ic in
  let buf = String.create size in
  really_input ic buf 0 size;
  close_in ic;
  buf

let env = Env.create_env (Typing.retrieve !loadpath)

let theories = 
  let cin = open_in fname in
  let m = Typing.read_channel env fname cin in
  close_in cin;
  m

(* namespace widget *)
module Ide_namespace = struct

  let cols = new GTree.column_list
  let column = cols#add Gobject.Data.string

  let renderer = GTree.cell_renderer_text [`XALIGN 0.] 
  let vcolumn = 
    GTree.view_column ~title:"theories" 
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

  let clear model = 
    model#clear ()

  let add_theory (model : GTree.tree_store) th =
    let rec fill parent ns =
      let add_s k s _ = 
	let row = model#append ~parent () in
	model#set ~row ~column (k ^ s)
      in
      Mnm.iter (add_s "type ")  ns.ns_ts;
      Mnm.iter (add_s "logic ") ns.ns_ls;
      Mnm.iter (add_s "prop ")  ns.ns_pr;
      let add_ns s ns =
	let row = model#append ~parent () in
	model#set ~row ~column s;
	fill row ns
      in
      Mnm.iter add_ns ns.ns_ns
    in
    let row = model#append () in
    model#set ~row ~column (th.th_name.Ident.id_short : string);
    fill row th.th_export

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

  (* top line *)
  let top_box = GPack.hbox ~packing:vbox#pack () in
  (* Replay *)
  let button = 
    GButton.button ~label:"repousser le front d'obsolescence" 
      ~packing:top_box#add ()
  in
  ignore (button#connect#clicked
	    (fun () -> Format.printf "Andrei, tu es trop fort !@."));

  (* horizontal paned *)
  let hp = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in

  (* left tree of namespace *)
  let scrollview = 
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~width:(window_width / 3) ~packing:hp#add () 
  in
  let _ = scrollview#set_shadow_type `ETCHED_OUT in

  let namespace_view = Ide_namespace.create ~packing:scrollview#add () in
  Mnm.iter (fun _ th -> Ide_namespace.add_theory namespace_view th) theories;

  (* source view *)
  let scrolled_win = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~packing:hp#add ()
  in
  let source_view =
    GSourceView.source_view
      ~auto_indent:true
      ~insert_spaces_instead_of_tabs:true ~tabs_width:2
      ~show_line_numbers:true
      ~margin:80 ~show_margin:true
      ~smart_home_end:true
      ~packing:scrolled_win#add ~height:500 ~width:650
      ()
  in
  source_view#misc#modify_font_by_name font_name;
  begin match lang with
    | Some lang -> source_view#source_buffer#set_language lang
    | None -> () 
  end;
  source_view#source_buffer#set_highlight true;
  source_view#source_buffer#set_text text;
 
  w#add_accel_group accel_group;
  w#show ()

let () =
  main ();
  GtkThread.main ()

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. why-ide-yes"
End: 
*)
