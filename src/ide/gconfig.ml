
open Format
open Why

type t = 
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
    }

let default = 
  { window_width = 1024;
    window_height = 768;
    tree_width = 512;
    task_height = 384;
  }

let conf_file = Filename.concat (Rc.get_home_dir ()) ".whyide.conf"

let save_config config =
  let ch = open_out conf_file in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "[main]@\n";
  fprintf fmt "width = %d@\n" config.window_width;
  fprintf fmt "height = %d@\n" config.window_height;
  fprintf fmt "tree_width = %d@\n" config.tree_width;
  fprintf fmt "task_height = %d@\n" config.task_height;
  fprintf fmt "@.";
  close_out ch

let load_main c (key, value) = 
  match key with
    | "width" -> c.window_width <- Rc.int value
    | "height" -> c.window_height <- Rc.int value
    | "tree_width" -> c.tree_width <- Rc.int value
    | "task_height" -> c.task_height <- Rc.int value
    | s -> 
        eprintf "Warning: ignore unknown key [%s] in whyide config file@." s
        
let load c (key, al) = 
  match key with
    | "main" :: _ ->
        List.iter (load_main c) al
    | s :: _ -> 
        eprintf "Warning: ignored unknown section [%s] in whyide config file@." s
    | [] -> assert false
        
let read_config () =
  try
    let rc = Rc.from_file conf_file in
    let c = default in
    List.iter (load c) rc;
    c
  with
    | Failure "lexing" -> 
        eprintf "Warning: syntax error in whyide config file@.";
        default
    | Not_found ->
        eprintf "Warning: no whyide config file, using default values@.";
        default
    

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



let show_legend_window () =
  let dialog = GWindow.dialog ~title:"Why: legend of icons" () in      
  let vbox = dialog#vbox in
  let text = GText.view ~packing:vbox#add () in
  let b = text#buffer in
  let i s = b#insert ~iter:b#end_iter s in
  let ib i = b#insert_pixbuf ~iter:b#end_iter ~pixbuf:!i in
  i "== icons in the tree view on the left ==\n";
  i "\n";
  ib image_directory;
  i "A theory, containing a set of goals\n";
  ib image_file;
  i "A goal\n";
  ib image_prover;
  i "An external prover\n";
  ib image_transf;
  i "A split transformation\n";
  i "\n";
  i "== icons in the satatus column\n";
  i "\n";
  ib image_scheduled;
  i "external proof scheduled by not started yet\n";
  ib image_running;
  i "external proof is running\n";
  ib image_valid;
  i "goal is proved/theory is fully verified\n";
  ib image_timeout;
  i "external prover reached the time limit\n";
  ib image_unknown;
  i "external prover answer was not conclusive\n";
  ib image_failure;
  i "external prover call failed\n";
  i "\n";
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  dialog#destroy ()


let show_about_window () =
  let about_dialog = 
    GWindow.about_dialog 
      ~name:"Why" 
      ~authors:["Francois Bobot";
                "Jean-Christophe Filliatre";
                "Johannes Kanig";
                "Claude Marche";
                "Andrei Paskevich"
               ]
      ~copyright:"Copyright 2010"
      ~license:"Gnu Lesser General Public License"
      ~website:"http://why.lri.fr"
      ~website_label:"Click here for the web site"
      ~version:"3.0 alpha"
      ()
  in      
  let ( _ : GWindow.Buttons.about) = about_dialog#run () in
  about_dialog#destroy ()

let preferences () =
  let dialog = GWindow.dialog ~title:"Why: legend of icons" () in      
  let vbox = dialog#vbox in
  let notebook = GPack.notebook ~packing:vbox#add () in
  let button = GButton.button ~label:"Page 1" 
    ~packing:(fun w -> ignore (notebook#append_page w)) () in
  let (_ : GtkSignal.id) = button#connect#clicked 
    ~callback:(fun () -> prerr_endline "Hello again - cool button 1 was pressed") 
  in
  let button = GButton.button ~label:"Page 2" 
    ~packing:(fun w -> ignore (notebook#append_page w))
    () in
  button#connect#clicked ~callback:
    (fun () -> prerr_endline "Hello again - cool button 2 was pressed");
  notebook#connect#switch_page 
    ~callback:(fun i -> prerr_endline ("Page switch to " ^ string_of_int i));
  button#connect#clicked ~callback:
    (fun () -> prerr_endline "Coucou");
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  dialog#destroy ()
  
(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/whyide.opt"
End: 
*)
