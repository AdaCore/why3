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

(* simple helpers *)
open Worker_proto

module Js = Js_of_ocaml.Js
module JSU = Js_of_ocaml.Js.Unsafe
module Dom = Js_of_ocaml.Dom
module File = Js_of_ocaml.File
module Sys_js = Js_of_ocaml.Sys_js
module Worker = Js_of_ocaml.Worker
module Dom_html = Js_of_ocaml.Dom_html
module XmlHttpRequest = Js_of_ocaml.XmlHttpRequest

let get_opt o = Js.Opt.get o (fun () -> assert false)

let check_def s o =
  Js.Optdef.get o (fun () -> log ("Object " ^ s ^ " is undefined or null");
			     assert false)
let get_global ident =
  let res : 'a Js.optdef = JSU.(get global) (Js.string ident) in
  check_def ident res

let int_of_js_string s = int_of_string (Js.to_string s)

let blob_url_of_string s =
  let s = JSU.inject (Js.string (Sys_js.read_file ~name:s)) in
  let _Blob  = get_global "Blob" in
  let blob =
    new%js _Blob (Js.array [| s |])
  in
  let _URL = JSU.(get (get_global "window") (Js.string "URL")) in
  let url : Js.js_string Js.t =
    JSU.(meth_call _URL "createObjectURL" [| JSU.inject blob |])
  in
  Js.to_string url


module XHR =
  struct
    include XmlHttpRequest

    let load_embedded_files =
      Js.to_bool (get_global "load_embedded_files") ||
	Js.to_string (Dom_html.window ##. location ##. protocol) = "file:"

    let make_url =
      if load_embedded_files then
	fun u ->
	Js.string (blob_url_of_string ("/" ^ (Js.to_string u)))
      else fun u -> u

    let update_file ?(date=0.) cb url =
      let xhr = create () in
      xhr ##. onreadystatechange :=
        Js.wrap_callback
          (fun () ->
           if xhr ##. readyState == DONE then
	     if xhr ##. status = 200 || (xhr ##. status = 0 && load_embedded_files) then
               let date_str = Js.Opt.get (xhr ## getResponseHeader (Js.string "Last-Modified"))
                                         (fun () -> Js.string "01/01/2100") (* far into the future *)
               in
               log (Printf.sprintf "File %s has date %s" (Js.to_string url) (Js.to_string date_str));
               let document_date = Js.date ## parse (date_str) in
               if document_date < date then
                 cb `UpToDate
               else
                 let () = xhr ##. onreadystatechange :=
                            Js.wrap_callback
                              (fun () ->
                               if xhr ##. readyState == DONE then
	                         if xhr ##. status = 200 then
                                   cb (`New xhr ##. responseText)
                                 else
                                   cb `NotFound)
                 in
                 let () = xhr ## _open (Js.string "GET") (make_url url) Js._true in
                 xhr ## send (Js.null)
             else
               cb `NotFound
          );
      xhr ## _open (Js.string "HEAD") (make_url url) Js._true;
      xhr ## send (Js.null)

  end

module AsHtml =
  struct
    include Dom_html.CoerceTo
    let span e = element e
  end


let select e cls =
  Dom.list_of_nodeList (e ## querySelectorAll (Js.string cls))

let getElement_exn cast id =
  Js.Opt.get (cast (Dom_html.getElementById id)) (fun () -> raise Not_found)

let getElement cast id =
  try
    getElement_exn cast id
  with
    Not_found ->
    log ("Element " ^ id ^ " does not exist or has invalid type");
    assert false

let appendChild o c =
  ignore (o ## appendChild ( (c :> Dom.node Js.t)))

let addMouseEventListener prevent o e f =
  let cb = Js.wrap_callback
	     (fun (e : Dom_html.mouseEvent Js.t) ->
	      if prevent then ignore (JSU.(meth_call e "preventDefault" [| |]));
	      f e;
	      Js._false)
  in
  ignore JSU.(meth_call o "addEventListener"
			[| inject (Js.string e);
			   inject cb;
			   inject Js._false |])




module Editor =
  struct
    type range
    type marker
    let name = ref (Js.string "")
    let saved = ref false
    let ace = get_global "ace"

    let _Range : (int -> int -> int -> int -> range Js.t) Js.constr =
      let r =
	JSU.(get (meth_call ace "require" [| inject (Js.string "ace/range") |])
		 (Js.string "Range"))
      in
      check_def "Range" r

    let editor =
      let e =
	JSU.(meth_call ace "edit" [| inject (Js.string "why3-editor") |])
      in
      check_def "why3-editor" e

    let task_viewer =
      let e =
	JSU.(meth_call ace "edit" [| inject (Js.string "why3-task-viewer") |])
      in
      check_def "why3-task-viewer" e

    let get_session ed =
      JSU.(meth_call ed "getSession" [| |])


    let mk_annotation row col text kind =
      JSU.(obj [| "row", inject row; "column", inject col;
		  "text", inject text; "type", inject kind |])

    let set_annotations l =
      let a =
	Array.map (fun (r,c,t,k) -> mk_annotation r c t k) (Array.of_list l)
      in
      let a = Js.array a in
      JSU.(meth_call (get_session editor) "setAnnotations" [| inject a |])

    let clear_annotations () =
      ignore (JSU.(meth_call (get_session editor) "clearAnnotations" [| |]))

    let _Infinity = get_global "Infinity"

    let scroll_to_end e =
      let len : int  = JSU.(meth_call (get_session e) "getLength" [| |]) in
      let last_line = len - 1 in
      ignore JSU.(meth_call e "gotoLine" [| inject last_line; inject _Infinity; inject Js._false |])

    let () =
      let editor_theme : Js.js_string Js.t = get_global "editor_theme" in
      let editor_mode : Js.js_string Js.t = get_global "editor_mode" in
      let task_viewer_mode : Js.js_string Js.t = get_global "task_viewer_mode" in

      ignore (JSU.(meth_call editor "setTheme" [| inject editor_theme |]));
      ignore (JSU.(meth_call (get_session editor) "setMode" [| inject editor_mode |]));
      JSU.(set editor (Js.string "$blockScrolling") _Infinity);

      ignore (JSU.(meth_call task_viewer "setTheme" [| inject editor_theme |]));
      ignore (JSU.(meth_call (get_session task_viewer) "setMode" [| inject task_viewer_mode |]));
      JSU.(set task_viewer (Js.string "$blockScrolling") _Infinity);

      JSU.(meth_call task_viewer "setReadOnly" [| inject Js._true|])

    let undo () =
      ignore JSU.(meth_call editor "undo" [| |])

    let redo () =
      ignore JSU.(meth_call editor "redo" [| |])

    let get_value ?(editor=editor) () : Js.js_string Js.t =
      JSU.meth_call editor "getValue" [| |]

    let set_value ?(editor=editor) (str : Js.js_string Js.t) =
      ignore JSU.(meth_call editor "setValue" [| inject (str); inject ~-1 |])

    let mk_range l1 c1 l2 c2 =
      new%js _Range l1 c1 l2 c2

    let set_selection_range r =
      let selection = JSU.meth_call editor "getSelection" [| |] in
      ignore JSU.(meth_call selection "setSelectionRange" [| inject r |])

    let add_marker cls r : marker =
      JSU.(meth_call (get_session editor) "addMarker"
                     [| inject r;
			inject (Js.string cls);
			inject (Js.string "text") |])

    let remove_marker m =
      ignore JSU.(meth_call  (get_session editor) "removeMarker" [| inject  m|])

    let get_char buffer i = int_of_float (buffer ## charCodeAt(i))
    let why3_loc_to_range buffer loc =
      let goto_line lstop =
        let rec loop lcur i =
          if lcur >= lstop then i
          else
            let c = get_char buffer i in
            loop (if c == 10 then lcur+1 else lcur) (i+1)
        in
        loop 1 0
      in
      let rec convert_range l c i n =
        if n == 0 then (l, c) else
          if (get_char buffer i) == 10
          then convert_range (l+1) 0 (i+1) (n-1)
          else convert_range l (c+1) (i+1) (n-1)
      in
      let l1, b, e = loc in
      let c1 = b in
      let i = goto_line l1 in
      let l2, c2 = convert_range l1 b (i+b) (e-b) in
      mk_range (l1-1) c1 (l2-1) c2

    let focus e =
      ignore JSU.(meth_call e "focus" [| |])

      let set_on_event e f =
	ignore JSU.(meth_call editor "on" [| inject (Js.string e);
					   inject f|])


      let editor_bg = getElement AsHtml.div "why3-editor-bg"

      let disable () =
        ignore JSU.(meth_call editor "setReadOnly" [| inject Js._true|]);
        editor_bg ##. style ##. display := Js.string "block"


      let enable () =
        ignore JSU.(meth_call editor "setReadOnly" [| inject Js._false|]);
        editor_bg ##. style ##. display := Js.string "none"


      let confirm_unsaved () =
        if not !saved then
          Js.to_bool
            (Dom_html.window ## confirm (Js.string "You have unsaved changes in your editor, proceed anyway ?"))
        else
          true

  end

module Tabs =
  struct

    let () =
      let tab_groups = select Dom_html.document ".why3-tab-group" in
      List.iter
	(fun tab_group ->
	 let labels = select tab_group ".why3-tab-label" in
	 List.iter
	     (fun tab ->
	      tab ##. onclick :=
		Dom.handler
                    (fun _ev ->
                   let () = if Js.to_bool
                       (tab ##. classList ## contains (Js.string "why3-inactive")) then
		       List.iter
	                  (fun t ->
                            ignore (t ##. classList ## toggle (Js.string "why3-inactive")))
		            labels
                   in
		   Js._false)
      ) labels)
      tab_groups
    let focus id =
      (Dom_html.getElementById id) ## click
  end

module ContextMenu =
  struct
    let task_menu = getElement AsHtml.div "why3-task-menu"
    let split_menu_entry = getElement AsHtml.li "why3-split-menu-entry"
    let prove_menu_entry = getElement AsHtml.li "why3-prove-menu-entry"
    let prove100_menu_entry = getElement AsHtml.li "why3-prove100-menu-entry"
    let prove1000_menu_entry = getElement AsHtml.li "why3-prove1000-menu-entry"
    let prove5000_menu_entry = getElement AsHtml.li "why3-prove5000-menu-entry"
    let clean_menu_entry = getElement AsHtml.li "why3-clean-menu-entry"
    let enabled = ref true

    let enable () = enabled := true
    let disable () = enabled := false

    let show_at x y =
      if !enabled then begin
          task_menu ##. style ##. display := Js.string "block";
          task_menu ##. style ##. left := Js.string ((string_of_int x) ^ "px");
          task_menu ##. style ##. top := Js.string ((string_of_int y) ^ "px")
        end
    let hide () =
      if !enabled then
        task_menu ##. style ##. display := Js.string "none"

    let add_action b f =
      b ##. onclick := Dom.handler (fun _ ->
				   hide ();
				   f ();
				   Editor.(focus editor);
				   Js._false)
    let () = addMouseEventListener false task_menu "mouseleave"
	(fun _ -> hide())


  end
module ExampleList =
  struct

    let select_example = getElement AsHtml.select "why3-select-example"
    let example_label = getElement AsHtml.span "why3-example-label"
    let set_loading_label b =
      select_example ##. disabled := Js.bool b;
      if b then
	example_label ##. className := Js.string "fas fa-spin fa-refresh why3-icon"
      else
	example_label ##. className := Js.string "fas fa-book why3-icon"

    let selected_index = ref 0
    let unselect () =
      selected_index := 0;
      select_example ##. selectedIndex := 0

    let () =
      let sessionStorage : Dom_html.storage Js.t =
	get_global "sessionStorage"
      in
      let filename url =
	let arr = url ## split (Js.string "/") in
	let arr = Js.to_array (Js.str_array arr) in
	arr.(Array.length arr - 1)
      in
      select_example ##. onchange :=
	Dom.handler (fun _ ->
                     if Editor.confirm_unsaved () then begin
                         selected_index := select_example ##. selectedIndex;
		         let url = select_example ##. value in
		         let name = filename url in
		         begin
		           match Js.Opt.to_option (sessionStorage ## getItem (url)) with
			     Some s -> Editor.set_value s; Editor.name := name
		           | None ->
                              XHR.update_file
                                (function `New mlw ->
				          sessionStorage ## setItem url mlw;
				          Editor.name := name;
				          Editor.set_value mlw;
				          set_loading_label false
                                        | _ -> ()
			        ) url
                         end
                       end
                     else
                       select_example ##. selectedIndex := !selected_index;
		     Js._false
		    )
    let add_example text url =
      let option = Dom_html.createOption Dom_html.document in
      option ##. value := url;
      option ##. innerHTML := text;
      appendChild select_example option

    let enable () =
      select_example ##. disabled := Js._false

    let disable () =
      select_example ##. disabled := Js._true
  end

module TaskList =
  struct


    let task_list = getElement AsHtml.div "why3-task-list"

    let print cls msg =
      task_list ##. innerHTML :=
        (Js.string ("<p class='" ^ cls ^ "'>" ^
                      msg ^ "</p>"))

    let print_error = print "why3-error"

    let print_msg = print "why3-msg"

    let print_alt_ergo_output id res =
      let span_msg = getElement AsHtml.span (id ^ "_msg") in
      match res with
        Valid -> span_msg ##. innerHTML := Js.string ""
      | Unknown msg -> span_msg ##. innerHTML := Js.string (" (" ^ msg ^ ")")
      | Invalid msg -> span_msg ##. innerHTML := Js.string (" (" ^ msg ^ ")")

    let mk_li_content id expl =
      Js.string (Format.sprintf
		   "<span id='%s_container'><span id='%s_icon'></span> %s <span id='%s_msg'></span></span><ul id='%s_ul'></ul>"
		   id id expl id id)

    let clean_task id =
      try
	let ul = getElement_exn AsHtml.ul (id ^ "_ul") in
	ul ##. innerHTML := Js.string ""
      with
	Not_found -> ()

    let attach_to_parent id parent_id expl _loc =
      let doc = Dom_html.document in
      let ul =
        try
          getElement_exn AsHtml.ul parent_id
        with
          Not_found ->
          let ul = Dom_html.createUl doc in
          ul ##. id := Js.string parent_id;
          appendChild task_list ul;
          ul
      in
      let li = Dom_html.createLi doc in
      li ##. id := Js.string id;
      appendChild ul li;
      li ##. innerHTML := mk_li_content id expl


    let task_selection = Hashtbl.create 17
    let is_selected id = Hashtbl.mem task_selection id
    let select_task id span loc pretty =
      span ##. classList ## add (Js.string "why3-task-selected");
      let markers = List.map (fun (cls, range) -> Editor.add_marker cls range) loc in
      Hashtbl.add task_selection id (span, loc, markers);
      Editor.set_value ~editor:Editor.task_viewer (Js.string pretty);
      Editor.scroll_to_end Editor.task_viewer

    let deselect_task id =
      try
        let span, _loc, markers = Hashtbl.find task_selection id in
        span ##. classList ## remove (Js.string "why3-task-selected");
        List.iter Editor.remove_marker markers;
        Hashtbl.remove task_selection id
      with
        Not_found -> ()

    let clear_task_selection () =
      let l = Hashtbl.fold (fun id _ acc -> id :: acc) task_selection [] in
      List.iter deselect_task l


    let clear () =
      clear_task_selection ();
      task_list ##. innerHTML := Js.string "";
      Editor.set_value ~editor:Editor.task_viewer (Js.string "")

    let error_marker = ref None

    let update_error_marker new_m =
      begin match !error_marker with
      | Some (m, _) -> Editor.remove_marker m
      | None -> ()
      end;
      error_marker := new_m

    let () =
      Editor.set_on_event
        "change"
        (Js.wrap_callback (fun () -> clear ();
                                  Editor.saved := false;
                                  ExampleList.unselect ();
				  Editor.clear_annotations ();
                                  update_error_marker None))

    let () =
      Editor.set_on_event
        "focus"
        (Js.wrap_callback  clear_task_selection )


    let print_why3_output o =
      let doc = Dom_html.document in
      (* see why3_worker.ml *)
      match o with
      | Idle | Warning [] -> ()
      | Warning lst ->
         let annot =
           List.map (fun ((l1, c1), msg) ->
                     (l1,c1, Js.string msg, Js.string "warning")) lst
         in
         Editor.set_annotations annot

      | Error s -> print_error s

      | ErrorLoc ((l1, b, l2, e), s) ->
         let r = Editor.mk_range l1 b l2 e in
         update_error_marker (Some (Editor.add_marker "why3-error" r, r));
         print_error s;
	 Editor.set_annotations [ (l1, b, Js.string s, Js.string "error") ]

      | Result sl ->
         clear ();
         let ul = Dom_html.createUl doc in
         appendChild task_list ul;
         List.iter (fun (s : string) ->
                    let li = Dom_html.createLi doc in
                    li ##. innerHTML := (Js.string s);
                    appendChild ul li;) sl

      | Theory (th_id, th_name) ->
	 attach_to_parent th_id "why3-theory-list" th_name []

      | Task (id, parent_id, expl, _code, locs, pretty, _) ->
	 begin
	   try
	     ignore (Dom_html.getElementById id)
	   with Not_found ->
		attach_to_parent id (parent_id ^ "_ul") expl locs;
		let span = getElement AsHtml.span (id ^ "_container") in
                let buffer = Editor.get_value () in
                let locs =
		  List.map (fun (k, loc) -> k, Editor.why3_loc_to_range buffer loc) locs
		in
		span ##. onclick :=
		  Dom.handler
		    (fun ev ->
		     let ctrl = Js.to_bool (ev ##. ctrlKey) in
		     if is_selected id then
                       if ctrl then deselect_task id else
			 clear_task_selection ()
		     else begin
			 if not ctrl then clear_task_selection ();
                         select_task id span locs pretty
                       end;
		     Js._false);
		addMouseEventListener
		  true span "contextmenu"
		  (fun e ->
		   clear_task_selection ();
                   select_task id span locs pretty;
		   let x = max 0 (e ##. clientX - 2) in
		   let y = max 0 (e ##. clientY - 2) in
		   ContextMenu.show_at x y)
	 end



      | UpdateStatus(st, id) ->
         try
           let span_icon = getElement AsHtml.span (id ^ "_icon") in
	   let span_msg = getElement AsHtml.span (id ^ "_msg") in
           let cls =
             match st with
               `New -> "fas fa-fw fa-cog fa-spin fa-fw why3-task-pending"
             | `Valid -> span_msg ##. innerHTML := Js.string "";
			 "fas fa-check-circle why3-task-valid"
             | `Unknown -> "fas fa-question-circle why3-task-unknown"
           in
           span_icon ##. className := Js.string cls
         with
           Not_found -> ()

  end


module ToolBar =
  struct
    let button_open = getElement AsHtml.button "why3-button-open"
    let real_save = getElement AsHtml.a "why3-save-as"
    let button_save = getElement AsHtml.button "why3-button-save"

    let button_undo = getElement AsHtml.button "why3-button-undo"
    let button_redo = getElement AsHtml.button "why3-button-redo"

    let button_execute = getElement AsHtml.button "why3-button-execute"
    let button_compile = getElement AsHtml.button "why3-button-compile"
    let button_stop = getElement AsHtml.button "why3-button-stop"

    let button_settings = getElement AsHtml.button "why3-button-settings"
    let button_help = getElement AsHtml.button "why3-button-help"
    let button_about = getElement AsHtml.button "why3-button-about"

    let disable b  =
      b ##. disabled := Js._true;
      b ##. classList ## add (Js.string "why3-inactive")

    let enable b =
      b ##. disabled := Js._false;
      b ##. classList ## remove (Js.string "why3-inactive")


    let toggle (b : <disabled : bool Js.t Js.prop; ..> Js.t) =
      if Js.to_bool (b ##. disabled) then enable b else disable b


    let add_action b f =
      let cb = fun _ ->
	f ();
	Editor.(focus editor);
	Js._false
      in
      b ##. onclick := Dom.handler cb


    let disable_compile () =
      Editor.disable ();
      ContextMenu.disable ();
      ExampleList.disable ();
      disable button_open;
      disable button_undo;
      disable button_redo;
      disable button_execute;
      disable button_compile

    let enable_compile () =
      Editor.enable ();
      ContextMenu.enable ();
      ExampleList.enable ();
      enable button_open;
      enable button_undo;
      enable button_redo;
      enable button_execute;
      enable button_compile




    let mk_save =
      let _Blob  = get_global "Blob" in
      fun () ->
      let blob =
        new%js _Blob (Js.array [| (Editor.get_value ()) |],
                     JSU.(obj [| "type", inject (Js.string "application/octet-stream") |]))
      in
      let name =
	if !Editor.name ##. length == 0 then Js.string "test.mlw" else !Editor.name
      in
      blob, name

    let save_default  =
      let _URL = JSU.(get Dom_html.window (Js.string "URL")) in
      fun () ->
      let blob, name = mk_save () in
      let url = JSU.(meth_call _URL "createObjectURL" [| inject blob |]) in
      real_save ##. href := url;
      JSU.(set real_save (Js.string "download") name);
      ignore JSU.(meth_call real_save "click" [| |])
    (* does not work with firefox *)
    (*ignore JSU.(meth_call _URL "revokeObjectURL" [| inject url |]) *)


    let save =
      match Js.Optdef.to_option JSU.(get (Dom_html.window ##. navigator) (Js.string "msSaveBlob"))
      with
        None -> save_default
      | Some _f ->
         fun () ->
         let blob, name = mk_save () in
         ignore JSU.(meth_call (Dom_html.window ##. navigator) "msSaveBlob" [| inject blob; inject name |])

    let open_ = getElement AsHtml.input "why3-open"
    let () =
      open_ ##. onchange := Dom.handler (fun _e ->
        ExampleList.unselect ();
	match Js.Optdef.to_option (open_ ##. files) with
	| None -> Js._false
	| Some (f) ->
          match Js.Opt.to_option (f ## item (0)) with
	  | None -> Js._false
	  | Some f ->
            let reader = new%js File.fileReader in
            reader ##. onloadend := Dom.handler (fun _ ->
              match Js.Opt.to_option (File.CoerceTo.string (reader ##. result)) with
              | None -> Js._true
              | Some content ->
                Editor.name := File.filename f;
                Editor.set_value content;
                Js._true);
            reader##readAsText ((f :> File.blob Js.t));
	    Js._true
          )
    let open_ () = if Editor.confirm_unsaved () then open_ ## click

  end

module Panel =
  struct
    let main_panel = getElement AsHtml.div "why3-main-panel"
    let editor_container = getElement AsHtml.div "why3-editor-container"
    let resize_bar = getElement AsHtml.div "why3-resize-bar"
    let reset () =
      let edit_style = editor_container ##. style in
      JSU.(set edit_style (Js.string "flexGrow") (Js.string "2"));
      JSU.(set edit_style (Js.string "flexBasis") (Js.string ""))

    let set_wide b =
      reset ();
      main_panel ##. classList ## remove (Js.string "why3-wide-view");
      main_panel ##. classList ## remove (Js.string "why3-column-view");
      if b then
	main_panel ##. classList ## add (Js.string "why3-wide-view")
      else
	main_panel ##. classList ## add (Js.string "why3-column-view")

    let is_wide () =
      Js.to_bool (main_panel ##. classList ## contains (Js.string "why3-wide-view"))

    let () =
      let mouse_down = ref false in
      resize_bar ##. onmousedown := Dom.handler (fun _ -> mouse_down := true; Js._false);
      resize_bar ##. ondblclick := Dom.handler (fun _ -> reset (); Js._false);
      main_panel ##. onmouseup := Dom.handler (fun _ -> mouse_down := false; Js._false);
      main_panel ##. onmousemove :=
	Dom.handler (fun e ->
		     if !mouse_down then begin
			 let offset =
			   if is_wide ()
			   then (e ##. clientX) - (main_panel ##. offsetLeft)
			   else (e ##. clientY) - (main_panel ##. offsetTop)
			 in
			 let offset = Js.string ((string_of_int offset) ^ "px") in
			 let edit_style = editor_container ##. style in
			 JSU.(set edit_style (Js.string "flexGrow") (Js.string "0"));
			     JSU.(set edit_style (Js.string "flexBasis") offset);
			     Js._false
		       end
		     else Js._true)
  end

module Dialogs =
  struct
    let dialog_panel = getElement AsHtml.div "why3-dialog-panel"
    let setting_dialog = getElement AsHtml.div "why3-setting-dialog"
    let about_dialog = getElement AsHtml.div "why3-about-dialog"
    let button_close = getElement AsHtml.button "why3-close-dialog-button"
    let input_num_threads = getElement AsHtml.input "why3-input-num-threads"
    let input_num_steps = getElement AsHtml.input "why3-input-num-steps"
    let radio_wide = getElement AsHtml.input "why3-radio-wide"
    let radio_column = getElement AsHtml.input "why3-radio-column"

    let all_dialogs = [ setting_dialog; about_dialog ]
    let show diag () =
      dialog_panel ##. style ##. display := Js.string "flex";
      diag ##. style ##. display := Js.string "inline-block";
      ignore JSU.(meth_call diag "focus" [| |])

    let close () =
      List.iter (fun d -> d ##. style ##. display := Js.string "none") all_dialogs;
      dialog_panel ##. style ##. display := Js.string "none"

    let set_onchange o f =
      o ##. onchange := Dom.handler (fun _ -> f o; Js._false)
  end

module KeyBinding =
  struct

    let callbacks = Array.init 255 (fun _ -> Array.make 16 None)
    let bool_to_int b =
      if Js.to_bool b then 1 else 0
    let pack a b c d =
      ((bool_to_int a) lsl 3) lor
        ((bool_to_int b) lsl 2) lor
          ((bool_to_int c) lsl 1) lor
            (bool_to_int d)

    let () =
      Dom_html.document ##. onkeydown :=
        Dom.handler
          (fun ev ->
           let i = min (Array.length callbacks) (max 0 ev ##. keyCode) in
           let t = callbacks.(i) in
           match t.(pack (ev ##. ctrlKey) (ev ##. shiftKey) (ev ##. metaKey) (ev ##. altKey)) with
             None -> Js._true
           | Some f ->
              ignore JSU.(meth_call ev "preventDefault" [| |]);
              f ();
              Js._false)

    let add_global ?(ctrl=Js._false) ?(shift=Js._false) ?(alt=Js._false) ?(meta=Js._false) keycode f =
      let i = min (Array.length callbacks) (max 0 keycode) in
      let t = callbacks.(i) in
      t.(pack ctrl shift meta alt) <- Some f

  end


module Session =
  struct

    let localStorage : Dom_html.storage Js.t =
      get_global "localStorage"

    let save_num_threads i =
      localStorage ## setItem (Js.string "why3-num-threads") (Js.string (string_of_int i))

    let save_num_steps i =
      localStorage ## setItem (Js.string "why3-num-steps") (Js.string (string_of_int i))


    let save_view_mode m =
      localStorage ## setItem (Js.string "why3-view-mode") m

    let save_buffer name content =
      localStorage ## setItem (Js.string "why3-buffer-name") name;
      localStorage ## setItem (Js.string "why3-buffer-content") content

    let load_num_threads () =
      int_of_js_string (Js.Opt.get (localStorage ## getItem (Js.string "why3-num-threads"))
                                (fun () -> Js.string "4"))

    let load_num_steps () =
      int_of_js_string (Js.Opt.get (localStorage ## getItem (Js.string "why3-num-steps"))
                                (fun () -> Js.string "100"))

    let load_view_mode () =
      Js.Opt.get (localStorage ## getItem (Js.string "why3-view-mode"))
                 (fun () -> Js.string "wide")

    let load_buffer () =
      let name = Js.Opt.get  (localStorage ## getItem (Js.string "why3-buffer-name"))
                             (fun () -> Js.string "")
      in
      let buffer = Js.Opt.get  (localStorage ## getItem (Js.string "why3-buffer-content"))
                               (fun () -> Js.string "")
      in
      (name, buffer)




  end


module Controller =
  struct
    let task_queue  = Queue.create ()
    let array_for_all a f =
      let rec loop i n =
	if i < n then (f a.(i)) && loop (i+1) n
	else true
      in
      loop 0 (Array.length a)

    let first_task = ref true
    type 'a status = Free of 'a | Busy of 'a | Absent
    let num_workers = Session.load_num_threads ()
    let alt_ergo_steps = ref (Session.load_num_steps ())
    let alt_ergo_workers = ref (Array.make num_workers Absent)
    let why3_busy = ref false
    let why3_worker = ref None

    let get_why3_worker () =
      match !why3_worker with
	Some w -> w
      | None -> log ("Why3 Worker not initialized !"); assert false


    let alt_ergo_not_running () =
      array_for_all !alt_ergo_workers (function Busy _ -> false | _ -> true)

    let is_idle () =
      alt_ergo_not_running () && Queue.is_empty task_queue && not (!why3_busy)



    let rec init_alt_ergo_worker i =
      let worker = Worker.create (blob_url_of_string "/alt_ergo_worker.js") in
      worker ##. onmessage :=
	(Dom.handler (fun ev ->
                      let (id, result) as res = unmarshal (ev ##. data) in
                      TaskList.print_alt_ergo_output id result;
		      let status_update = status_of_result res in
		      let () = match status_update with
			  SetStatus(v, id) ->
			  TaskList.print_why3_output (UpdateStatus(v, id))
			| _ -> ()
		      in
                      (get_why3_worker()) ## postMessage (marshal status_update);
                      !alt_ergo_workers.(i) <- Free(worker);
                      process_task ();
                      Js._false));
      Free (worker)

    and process_task () =
      let rec find_free_worker_slot i =
	if i < num_workers then
	  match !alt_ergo_workers.(i) with
            Free _ as w -> i, w
	  | _ -> find_free_worker_slot (i+1)
	else -1, Absent
      in
      let idx, w = find_free_worker_slot 0 in
      match w with
	Free w when not (Queue.is_empty task_queue) ->
	let task = Queue.take task_queue in
	!alt_ergo_workers.(idx) <- Busy (w);
	w ## postMessage (marshal (OptionSteps !alt_ergo_steps));
	w ## postMessage (marshal task)
      | _ -> if is_idle () then ToolBar.enable_compile ()

    let reset_workers () =
      Array.iteri
	(fun i w ->
	 match w with
	   Busy (w)  ->
           w ## terminate;
           !alt_ergo_workers.(i) <- init_alt_ergo_worker i
	 | Absent -> !alt_ergo_workers.(i) <- init_alt_ergo_worker i
	 | Free _ -> ()
	) !alt_ergo_workers

    let push_task task =
      Queue.add  task task_queue;
      process_task ()

    let init_why3_worker () =
      let worker = Worker.create (blob_url_of_string "/why3_worker.js") in
      worker ##. onmessage :=
	(Dom.handler (fun ev ->
                      let msg = unmarshal (ev ##. data) in
                      if !first_task then begin
			  first_task := false;
			  TaskList.clear ()
			end;
                      TaskList.print_why3_output msg;
                      let () =
			match msg with
			  Task (id,_,_,code,_, _, steps) ->
			  push_task (Goal (id,code, steps))
			| Idle -> why3_busy := false; if is_idle () then ToolBar.enable_compile ()
			| _ -> ()
                      in Js._false));
      worker

    let () = why3_worker := Some (init_why3_worker ())

    let why3_parse () =
      Tabs.focus "why3-task-list-tab";
      ToolBar.disable_compile ();
      why3_busy := true;
      TaskList.clear ();
      TaskList.print_msg "<span class='fas fa-cog fa-spin'></span> Generating tasks … ";
      reset_workers ();
      first_task := true;
      let code = Js.to_string (Editor.get_value ()) in
      let msg = marshal (ParseBuffer code) in
      (get_why3_worker()) ## postMessage (msg)

    let why3_execute () =
      Tabs.focus "why3-task-list-tab";
      ToolBar.disable_compile ();
      why3_busy := true;
      TaskList.clear ();
      TaskList.print_msg "<span class='fas fa-cog fa-spin'></span> Compiling buffer … ";
      reset_workers ();
      let code = Js.to_string (Editor.get_value ()) in
      (get_why3_worker()) ## postMessage (marshal (ExecuteBuffer code))



    let why3_transform tr f () =
      if is_idle () then
	begin
          why3_busy := true;
          ToolBar.disable_compile ();
	  Hashtbl.iter
            (fun id _ ->
	     f id;
	     (get_why3_worker()) ## postMessage (marshal (Transform(tr, id))))
	    TaskList.task_selection;
	  TaskList.clear_task_selection ()
	end

    let why3_prove_all () =
      if is_idle () then begin
          why3_busy := true;
	  (get_why3_worker()) ## postMessage (marshal ProveAll)
        end

    let force_stop () =
      log ("Called force_stop");
      (get_why3_worker()) ## terminate;
      why3_worker := Some (init_why3_worker ());
      reset_workers ();
      TaskList.clear ();
      ToolBar.enable_compile ()

    let stop () =
      if not (is_idle ()) then force_stop ();


end

(* Initialisation *)
let () =
  ToolBar.(add_action button_open open_);
  KeyBinding.add_global ~ctrl:Js._true 79 ToolBar.open_;

  ToolBar.(add_action button_save save);
  KeyBinding.add_global ~ctrl:Js._true 83 ToolBar.save;

  ToolBar.(add_action button_undo Editor.undo);
  KeyBinding.add_global ~ctrl:Js._true 90 Editor.undo;

  ToolBar.(add_action button_redo Editor.redo);
  KeyBinding.add_global ~ctrl:Js._true 89 Editor.redo;


  ToolBar.(add_action button_execute Controller.why3_execute);
  ToolBar.(add_action button_compile Controller.why3_parse);
  ToolBar.(add_action button_stop Controller.stop);
  ToolBar.(add_action button_settings Dialogs.(show setting_dialog));
  ToolBar.(add_action button_help (fun () ->
                                   Dom_html.window ## open_ (Js.string "trywhy3_help.html")
                                                            (Js.string "_blank")
                                                            Js.null));
  ToolBar.(add_action button_about Dialogs.(show about_dialog));
  ContextMenu.(add_action split_menu_entry
			  Controller.(why3_transform `Split ignore));
  ContextMenu.(add_action prove_menu_entry
			  Controller.(why3_transform (`Prove(-1)) ignore));
  ContextMenu.(add_action prove100_menu_entry
			  Controller.(why3_transform (`Prove(100)) ignore));
  ContextMenu.(add_action prove1000_menu_entry
			  Controller.(why3_transform (`Prove(1000)) ignore));
  ContextMenu.(add_action prove5000_menu_entry
			  Controller.(why3_transform (`Prove(5000)) ignore));
  ContextMenu.(add_action clean_menu_entry
			  Controller.(why3_transform (`Clean) TaskList.clean_task));
  Dialogs.(set_onchange input_num_threads
			 (fun o ->
			  let open Controller in
			  let len = int_of_js_string (o ##. value) in
                          force_stop ();
			  alt_ergo_workers := Array.make len Absent));

  Dialogs.(set_onchange input_num_steps
			 (fun o ->
			  let steps = int_of_js_string (o ##. value) in
                          Controller.alt_ergo_steps := steps;
			  Controller.force_stop ()
	                 ));

  ToolBar.add_action Dialogs.button_close Dialogs.close;
  (*KeyBinding.add_global Keycode.esc  Dialogs.close;*)

  Dialogs.(set_onchange radio_wide (fun _ -> Panel.set_wide true));
  Dialogs.(set_onchange radio_column (fun _ -> Panel.set_wide false))


let () =
  XHR.update_file (function `New content ->
	                    let examples = content ## split (Js.string "\n") in
	                    let examples = Js.to_array (Js.str_array examples) in
	                    for i = 0 to ((Array.length examples) / 2) - 1 do
	                      ExampleList.add_example
	                        examples.(2*i)
	                        ((Js.string "examples/") ## concat (examples.(2*i+1)))
	                    done;
	                    ExampleList.set_loading_label false
                          | _ ->
	                     ExampleList.set_loading_label false
                  ) (Js.string "examples/index.txt");
  ExampleList.set_loading_label true


let () =
  Dom_html.window ##. onunload := Dom.handler (fun _ -> Js._false);
  (* restore the session *)
  let name, buffer = Session.load_buffer () in
  Editor.name := name;
  Editor.set_value buffer;
  Panel.set_wide (Session.load_view_mode () = (Js.string "wide"));
  ExampleList.unselect();
  Dom_html.window ##. onbeforeunload :=
    Dom.handler (Obj.magic (fun _ ->
                   Session.save_buffer !Editor.name (Editor.get_value ());
                   Session.save_num_threads (Array.length !Controller.alt_ergo_workers);
                   Session.save_num_steps !Controller.alt_ergo_steps;
                   Session.save_view_mode (if Panel.is_wide () then Js.string "wide"
                                           else Js.string "column");

                   (Js.string "Do you wish to quit TryWhy3 (your current session will be saved to your browser local storage) ?"))
                )

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. trywhy3"
End:
*)
