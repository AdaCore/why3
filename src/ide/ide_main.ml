
let () = ignore (GtkMain.Main.init ())

(* config *)
let window_width = 1024
let window_height = 768

let font_size = ref 10
let font_family = "Monospace"


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
  (* le bouton Replay *)
  let button = 
    GButton.button ~label:"repousser le front d'obsolescence" 
    ~packing:top_box#add ()
  in
  ignore (button#connect#clicked
	    (fun () -> Format.printf "Andrei, tu es trop fort !@."));


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
