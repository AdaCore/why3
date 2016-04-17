(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* simple helpers *)
open Worker_proto

module JSU = Js.Unsafe
module XHR = XmlHttpRequest

let get_opt o = Js.Opt.get o (fun () -> assert false)

module AsHtml =
  struct
    include Dom_html.CoerceTo
    let span e = element e
  end

(* Each group of UI element is encpasulated in a module *)

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
  ignore (JSU.(meth_call o "addEventListener"
			 [| inject (Js.string e);
			    inject cb;
			    inject Js._false |]))



let check_def s o =
  Js.Optdef.get o (fun () -> log ("Object " ^ s ^ " is undefined or null");
			     assert false)
let get_global ident =
  let res : 'a Js.optdef = JSU.(get global) (Js.string ident) in
  check_def ident res


module Editor =
  struct
    type range
    type marker
    let name = ref (Js.string "")
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

    let () =
      let editor_theme : Js.js_string Js.t = get_global "editor_theme" in
      let editor_mode : Js.js_string Js.t = get_global "editor_mode" in
      let _Infinity = get_global "Infinity" in
      List.iter (fun e ->
		 ignore (JSU.(meth_call e "setTheme" [| inject editor_theme |]));
		 ignore (JSU.(meth_call (get_session e) "setMode" [| inject editor_mode |]));
		 JSU.(set e (Js.string "$blockScrolling") _Infinity)
		) [ editor; task_viewer ];
      JSU.(meth_call task_viewer "setReadOnly" [| inject Js._true|])


    let get_value ?(editor=editor) () : Js.js_string Js.t =
      JSU.meth_call editor "getValue" [| |]

    let set_value ?(editor=editor) (str : Js.js_string Js.t) =
      ignore JSU.(meth_call editor "setValue" [| inject (str); inject ~-1 |])

    let mk_range l1 c1 l2 c2 =
      jsnew _Range (l1, c1, l2, c2)

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
          if lcur == lstop then i
          else
            let c = get_char buffer i in
            loop (if c == 0 then lcur+1 else lcur) (i+1)
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
  end

module Tabs =
  struct
    let () =
      let labels =
	Dom.list_of_nodeList (
	    Dom_html.document ## getElementsByClassName (Js.string "why3-tab-label")
	  )
      in
      List.iter
	(fun t ->
	 t ## onclick <-
	   Dom.handler
	     (fun _ ->
	      List.iter
		(fun l -> ignore (l ## classList ## toggle (Js.string "why3-inactive")))
		labels;
	      Js._false)
	)
	labels
  end

module ContextMenu =
  struct
    let task_menu = getElement AsHtml.div "why3-task-menu"
    let split_menu_entry = getElement AsHtml.li "why3-split-menu-entry"
    let prove_menu_entry = getElement AsHtml.li "why3-prove-menu-entry"
    let prove100_menu_entry = getElement AsHtml.li "why3-prove100-menu-entry"
    let prove1000_menu_entry = getElement AsHtml.li "why3-prove1000-menu-entry"
    let clean_menu_entry = getElement AsHtml.li "why3-clean-menu-entry"

    let show_at x y =
      task_menu ## style ## display <- Js.string "block";
      task_menu ## style ## left <- Js.string ((string_of_int x) ^ "px");
      task_menu ## style ## top <- Js.string ((string_of_int y) ^ "px")
    let hide () =
      task_menu ## style ## display <- Js.string "none"
    let add_action b f =
      b ## onclick <- Dom.handler (fun _ ->
				   hide ();
				   f ();
				   Editor.(focus editor);
				   Js._false)
    let () =
      addMouseEventListener
	false task_menu "mouseleave"
	(fun _ -> hide())


  end

module TaskList =
  struct


    let task_list = getElement AsHtml.div "why3-task-list"

    let print cls msg =
      task_list ## innerHTML <-
        (Js.string ("<p class='" ^ cls ^ "'>" ^
                      msg ^ "</p>"))

    let print_error = print "why3-error"

    let print_msg = print "why3-msg"

    let print_alt_ergo_output id res =
      let span_msg = getElement AsHtml.span (id ^ "_msg") in
      match res with
        Valid -> span_msg ## innerHTML <- Js.string ""
      | Unknown msg -> span_msg ## innerHTML <- (Js.string (" (" ^ msg ^ ")"))
      | Invalid msg -> span_msg ## innerHTML <- (Js.string (" (" ^ msg ^ ")"))

    let mk_li_content id expl =
      Js.string (Format.sprintf
		   "<span id='%s_container'><span id='%s_icon'></span> %s <span id='%s_msg'></span></span><ul id='%s_ul'></ul>"
		   id id expl id id)

    let clean_task id =
      try
	let ul = getElement_exn AsHtml.ul (id ^ "_ul") in
	ul ## innerHTML <- Js.string ""
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
          ul ## id <- Js.string parent_id;
          appendChild task_list ul;
          ul
      in
      let li = Dom_html.createLi doc in
      li ## id <- Js.string id;
      appendChild ul li;
      li ## innerHTML <- mk_li_content id expl


    let task_selection = Hashtbl.create 17
    let is_selected id = Hashtbl.mem task_selection id
    let select_task id span loc pretty =
      (span ## classList) ## add (Js.string "why3-task-selected");
      let markers = List.map (fun (cls, range) -> Editor.add_marker cls range) loc in
      Hashtbl.add task_selection id (span, loc, markers);
      Editor.set_value ~editor:Editor.task_viewer (Js.string pretty)

    let deselect_task id =
      try
        let span, _loc, markers = Hashtbl.find task_selection id in
        (span ## classList) ## remove (Js.string "why3-task-selected");
        List.iter Editor.remove_marker markers;
        Hashtbl.remove task_selection id
      with
        Not_found -> ()

    let clear_task_selection () =
      let l = Hashtbl.fold (fun id _ acc -> id :: acc) task_selection [] in
      List.iter deselect_task l


    let clear () =
      clear_task_selection ();
      task_list ## innerHTML <- Js.string "";
      Editor.set_value ~editor:Editor.task_viewer (Js.string "")

    let error_marker = ref None
    let () =
      Editor.set_on_event
        "change"
        (Js.wrap_callback (fun () -> clear ();
				     Editor.clear_annotations ();
                                     match !error_marker with
                                       None -> ()
                                     | Some (m, _) -> Editor.remove_marker m))

    let () =
      Editor.set_on_event
        "focus"
        (Js.wrap_callback (fun () ->
                           clear_task_selection ();
                           match !error_marker with
                             None -> ()
                           | Some (_, r) -> Editor.set_selection_range r))


    let print_why3_output o =
      let doc = Dom_html.document in
      (* see why3_worker.ml *)
      match o with
        Error s -> print_error s

      | ErrorLoc ((l1, b, l2, e), s) ->
         let r = Editor.mk_range l1 b l2 e in
         error_marker := Some (Editor.add_marker "why3-error" r, r);
         print_error s;
	 Editor.set_annotations [ (l1, b, Js.string s, Js.string "error") ]

      | Result sl ->
         clear ();
         let ul = Dom_html.createUl doc in
         appendChild task_list ul;
         List.iter (fun (s : string) ->
                    let li = Dom_html.createLi doc in
                    li ## innerHTML <- (Js.string s);
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
		span ## onclick <-
		  Dom.handler
		    (fun ev ->
		     let ctrl = Js.to_bool (ev ## ctrlKey) in
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
		   let x = max 0 ((e ##clientX) - 2) in
		   let y = max 0 ((e ##clientY) - 2) in
		   ContextMenu.show_at x y)
	 end



      | UpdateStatus(st, id) ->
         try
           let span_icon = getElement AsHtml.span (id ^ "_icon") in
	   let span_msg = getElement AsHtml.span (id ^ "_msg") in
           let cls =
             match st with
               `New -> "fa fa-fw fa-cog fa-spin fa-fw why3-task-pending"
             | `Valid -> span_msg ## innerHTML <- Js.string "";
			 "fa-check-circle why3-task-valid"
             | `Unknown -> "fa-question-circle why3-task-unknown"
           in
           span_icon ## className <- Js.string cls
         with
           Not_found -> ()

  end

module ExampleList =
  struct

    let select_example = getElement AsHtml.select "why3-select-example"
    let example_label = getElement AsHtml.span "why3-example-label"
    let set_loading_label b =
      select_example ## disabled <- (Js.bool b);
      if b then
	example_label ## className <- Js.string "fa fa-spin fa-refresh why3-icon"
      else
	example_label ## className <- Js.string "fa-book why3-icon"

    let () =
      let sessionStorage : Dom_html.storage Js.t =
	get_global "sessionStorage"
      in
      let filename url =
	let arr = url ## split (Js.string "/") in
	let arr = Js.to_array (Js.str_array arr) in
	arr.(Array.length arr - 1)
      in
      select_example ## onchange <-
	Dom.handler (fun _ ->
		     let url = select_example ## value in
		     let name = filename url in
		     begin
		       match Js.Opt.to_option (sessionStorage ## getItem (url)) with
			 Some s -> Editor.set_value s; Editor.name := name
		       | None ->
			  let xhr = XHR.create () in
			  xhr ## onreadystatechange <-
			    Js.wrap_callback
			      (fun () ->
			       if xhr ## status = 200 &&
				    xhr ## readyState == XHR.DONE
			       then
				 let mlw = xhr ## responseText in
				 sessionStorage ## setItem (url, mlw);
				 Editor.name := name;
				 Editor.set_value mlw;
				 set_loading_label false
			      );
			  xhr ## _open (Js.string "GET", url, Js._true);
			  xhr ## send (Js.null);
			  set_loading_label true
		     end;
		     Js._false
		    )
    let add_example text url =
      let option = Dom_html.createOption Dom_html.document in
      option ## value <- url;
      option ## innerHTML <- text;
      appendChild select_example option

  end
module ToolBar =
  struct
    let button_open = getElement AsHtml.button "why3-button-open"
    let real_save = getElement AsHtml.a "why3-save-as"
    let button_save = getElement AsHtml.button "why3-button-save"
    let button_execute = getElement AsHtml.button "why3-button-execute"
    let button_compile = getElement AsHtml.button "why3-button-compile"
    let button_stop = getElement AsHtml.button "why3-button-stop"

    let button_settings = getElement AsHtml.button "why3-button-settings"
    let button_help = getElement AsHtml.button "why3-button-help"
    let button_about = getElement AsHtml.button "why3-button-about"

    let disable (b : <disabled : bool Js.t Js.prop; ..> Js.t) =
     b ## disabled <- Js._true

    let enable (b : <disabled : bool Js.t Js.prop; ..> Js.t) =
     b ## disabled <- Js._false

    let toggle (b : <disabled : bool Js.t Js.prop; ..> Js.t) =
      if Js.to_bool (b##disabled) then enable b else disable b

    let add_action b f =
      b ## onclick <- Dom.handler (fun _ ->
				   f ();
				   Editor.(focus editor);
				   Js._false)

    let disable_compile () =
      disable button_execute;
      disable button_compile

    let enable_compile () =
      enable button_execute;
      enable button_compile


    let save () =
      let data : Js.js_string Js.t =
	let buffer = JSU.(fun_call (get_global "btoa") [| inject (Editor.get_value ()) |]) in
	(Js.string "data:application/octet-stream;bas64,") ## concat (buffer)
      in
      real_save ## href <- data;
      let name =
	if !Editor.name ## length == 0 then Js.string "test.mlw" else !Editor.name
      in
      JSU.(set real_save (Js.string "download") name);
      ignore (JSU.(meth_call real_save "click" [| |]))

    let open_ = getElement AsHtml.input "why3-open"
    let () =
      open_ ## onchange <-
	Dom.handler
	  (fun _e ->
	   log "Here";
	   match Js.Optdef.to_option (open_ ## files) with
	     None -> Js._false
	   | Some (f) -> match Js.Opt.to_option (f ## item (0)) with
			   None -> Js._false
			 | Some f ->
			    ignore (
				Lwt.bind (File.readAsText f)
					 (fun str ->
					  Editor.name := File.filename f;
					  Editor.set_value str;
					  Lwt.return_unit));
			    Js._true)

  end

module Panel =
  struct
    let main_panel = getElement AsHtml.div "why3-main-panel"
    let editor_container = getElement AsHtml.div "why3-editor-container"
    let resize_bar = getElement AsHtml.div "why3-resize-bar"
    let reset () =
      let edit_style = editor_container ## style in
      JSU.(set edit_style (Js.string "flexGrow") (Js.string "2"));
      JSU.(set edit_style (Js.string "flexBasis") (Js.string ""))
    let set_wide b =
      main_panel ## classList ## remove (Js.string "why3-wide-view");
      main_panel ## classList ## remove (Js.string "why3-column-view");
      if b then
	main_panel ## classList ## add (Js.string "why3-wide-view")
      else
	main_panel ## classList ## add (Js.string "why3-column-view")

    let is_wide () =
      Js.to_bool (main_panel ## classList ## contains (Js.string "why3-wide-view"))
    let () =
      let mouse_down = ref false in
      resize_bar ## onmousedown <- Dom.handler (fun _ -> mouse_down := true; Js._false);
      resize_bar ## ondblclick <- Dom.handler (fun _ -> reset (); Js._false);
      main_panel ## onmouseup <- Dom.handler (fun _ -> mouse_down := false; Js._false);
      main_panel ## onmousemove <-
	Dom.handler (fun e ->
		     if !mouse_down then begin
			 let offset =
			   if is_wide ()
			   then (e ## clientX) - (main_panel ## offsetLeft)
			   else (e ## clientY) - (main_panel ## offsetTop)
			 in
			 let offset = Js.string ((string_of_int offset) ^ "px") in
			 let edit_style = editor_container ## style in
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
      log ("HERE");
      dialog_panel ## style ## display <- Js.string "flex";
      diag ## style ## display <- Js.string "inline-block"

    let close () =
      List.iter (fun d -> d ## style ## display <- Js.string "none") all_dialogs;
      dialog_panel ## style ## display <- Js.string "none"

    let set_onchange o f =
      o ## onchange <- Dom.handler (fun _ -> f o; Js._false)

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
    let num_workers = 4
    let alt_ergo_steps = ref 100
    let alt_ergo_workers = ref (Array.make num_workers Absent)
    let why3_busy = ref false
    let why3_worker = ref None
    let get_why3_worker () =
      match !why3_worker with
	Some w -> w
      | None -> log ("Why3 Worker not initialized !"); assert false


    let alt_ergo_not_running () =
      array_for_all !alt_ergo_workers (function Busy _ -> false | _ -> true)


    let rec init_alt_ergo_worker i =
      let worker = Worker.create "alt_ergo_worker.js" in
      worker ## onmessage <-
	(Dom.handler (fun ev ->
                      let (id, result) as res = unmarshal (ev ## data) in
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
      | _ -> if Queue.is_empty task_queue && alt_ergo_not_running ()
	     then ToolBar.enable_compile ()

    let reset_workers () =
      Array.iteri
	(fun i w ->
	 match w with
	   Busy (w)  ->
           w ## terminate ();
           !alt_ergo_workers.(i) <- init_alt_ergo_worker i
	 | Absent -> !alt_ergo_workers.(i) <- init_alt_ergo_worker i
	 | Free _ -> ()
	) !alt_ergo_workers

    let push_task task =
      Queue.add  task task_queue;
      process_task ()

    let init_why3_worker () =
      let worker = Worker.create "why3_worker.js" in
      worker ## onmessage <-
	(Dom.handler (fun ev ->
                      let msg = unmarshal (ev ## data) in
                      if !first_task then begin
			  first_task := false;
			  TaskList.clear ()
			end;
                      TaskList.print_why3_output msg;
                      let () =
			match msg with
			  Task (id,_,_,code,_, _, steps) ->
			  push_task (Goal (id,code, steps))
			| Result _ | Error _ | ErrorLoc _ -> ToolBar.enable_compile ()
			| _ -> ()
                      in Js._false));
      worker

    let () = why3_worker := Some (init_why3_worker ())

    let why3_parse () =
      ToolBar.disable_compile ();
      TaskList.clear ();
      TaskList.print_msg "<span class='fa fa-cog fa-spin'></span> Generating tasks … ";
      reset_workers ();
      first_task := true;
      let code = Js.to_string (Editor.get_value ()) in
      let msg = marshal (ParseBuffer code) in
      (get_why3_worker()) ## postMessage (msg)

    let why3_execute () =
      ToolBar.disable_compile ();
      TaskList.clear ();
      TaskList.print_msg "<span class='fa fa-cog fa-spin'></span> Compiling buffer … ";
      reset_workers ();
      let code = Js.to_string (Editor.get_value ()) in
      (get_why3_worker()) ## postMessage (marshal (ExecuteBuffer code))



    let why3_transform tr f () =
      if alt_ergo_not_running () then
	begin
	  Hashtbl.iter
            (fun id _ ->
	     f id;
	     (get_why3_worker()) ## postMessage (marshal (Transform(tr, id))))
	    TaskList.task_selection;
	  TaskList.clear_task_selection ()
	end

    let why3_prove_all () =
      if alt_ergo_not_running () then
	(get_why3_worker()) ## postMessage (marshal ProveAll)

    let stop () =
      (get_why3_worker()) ## terminate ();
      why3_worker := Some (init_why3_worker ());
      reset_workers ();
      TaskList.clear ();
      ToolBar.enable_compile ()

end

(* Initialisation *)
let () =
  ToolBar.(add_action button_open (fun _ ->  open_ ## click()));
  ToolBar.(add_action button_save save);
  ToolBar.(add_action button_execute Controller.why3_execute);
  ToolBar.(add_action button_compile Controller.why3_parse);
  ToolBar.(add_action button_stop Controller.stop);
  ToolBar.(add_action button_settings Dialogs.(show setting_dialog));
  ToolBar.(add_action button_about Dialogs.(show about_dialog));
  ContextMenu.(add_action split_menu_entry
			  Controller.(why3_transform `Split ignore));
  ContextMenu.(add_action prove_menu_entry
			  Controller.(why3_transform (`Prove(-1)) ignore));
  ContextMenu.(add_action prove100_menu_entry
			  Controller.(why3_transform (`Prove(100)) ignore));
  ContextMenu.(add_action prove1000_menu_entry
			  Controller.(why3_transform (`Prove(1000)) ignore));
  ContextMenu.(add_action clean_menu_entry
			  Controller.(why3_transform (`Clean) TaskList.clean_task));
  Dialogs.(set_onchange input_num_threads
			 (fun o ->
			  let open Controller in
			  let len = int_of_string (Js.to_string (o ## value)) in
			  reset_workers ();
			  Array.iter
			    (function Busy (w) | Free (w) -> w ## terminate () | _ -> ())
			    !alt_ergo_workers;
			  alt_ergo_workers := Array.make len Absent));

  Dialogs.(set_onchange input_num_steps
			 (fun o ->
			  let open Controller in
			  let steps = int_of_string (Js.to_string (o ## value)) in
			  alt_ergo_steps := steps;
			  reset_workers ()));
  ToolBar.add_action Dialogs.button_close Dialogs.close;
  Dialogs.(set_onchange radio_wide (fun _ -> Panel.set_wide true));
  Dialogs.(set_onchange radio_column (fun _ -> Panel.set_wide false))

let () =
  let xhr = XHR.create () in
  xhr ## onreadystatechange <-
    Js.wrap_callback
      (fun () ->
       if xhr ## readyState == XHR.DONE then
	 if xhr ## status = 200 then
	   let examples = xhr ## responseText ## split (Js.string "\n") in
	   let examples = Js.to_array (Js.str_array examples) in
	   for i = 0 to ((Array.length examples) / 2) - 1 do
	     ExampleList.add_example examples.(2*i) ((Js.string "examples/") ## concat (examples.(2*i+1)))
	   done;
	   ExampleList.set_loading_label false
	 else
	   ExampleList.set_loading_label false
      );
  xhr ## _open (Js.string "GET", Js.string "examples/index.txt", Js._true);
  xhr ## send (Js.null);
  ExampleList.set_loading_label true

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. trywhy3"
End:
*)
