
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

let spec = []
let () = Arg.parse spec set_file "why-ide [options] file.why"

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

  (* source view *)
  let scrolled_win = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~packing:vbox#add ()
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
