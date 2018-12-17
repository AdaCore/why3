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


open Why3
open Itp_communication

module Js = Js_of_ocaml.Js
module JSU = Js_of_ocaml.Js.Unsafe
module Dom = Js_of_ocaml.Dom
module Form = Js_of_ocaml.Form
module Firebug = Js_of_ocaml.Firebug
module Dom_html = Js_of_ocaml.Dom_html
module XmlHttpRequest = Js_of_ocaml.XmlHttpRequest

let log s = ignore (Firebug.console ## log (Js.string s))

let get_opt o = Js.Opt.get o (fun () -> assert false)

let check_def s o =
  Js.Optdef.get o (fun () -> log ("ERROR in check_def(): object " ^ s ^ " is undefined or null");
			     assert false)

let get_global ident =
  let res : 'a Js.optdef = JSU.(get global) (Js.string ident) in
  check_def ident res

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

(**********)

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
    log ("ERROR in getElement(): element " ^ id ^ " does not exist or has invalid type");
    assert false

(**********)

module PE = struct
  let log_panel = getElement AsHtml.div "why3-log-bg"
  let doc = Dom_html.document
  let error_container = getElement AsHtml.div "why3-error-container"

  let print _cls msg =
    let node = doc##createElement (Js.string "P") in
    let textnode = doc##createTextNode (Js.string msg) in
    appendChild node textnode;
    appendChild log_panel node

  let log_print_error = print "why3-error"

  let log_print_msg = print "why3-msg"

  let error_print_msg s =
    error_container ##. innerHTML := Js.string s;
    log_print_msg s

end

let readBody (xhr: XmlHttpRequest.xmlHttpRequest Js.t) =
  let data = ref None in
  data := Some (xhr ##. responseText);
  match !data with
  | None -> raise Not_found
  | Some data -> Js.to_string data

module Tabs =
  struct

    let () =
      let tab_groups = select Dom_html.document ".why3-tab-group" in
      List.iter
	(fun tab_group ->
	 let labels = select tab_group ".why3-tab-label" in
	 List.iter (
	     (fun tab ->
	      tab ##. onclick :=
		Dom.handler
		  (fun _ev ->
		   List.iter
		     (fun t ->
		      ignore (t ##. classList ## add (Js.string "why3-inactive")))
		     labels;
                   tab ##. classList ## remove (Js.string "why3-inactive");
		   Js._false))
	       ) labels)
	tab_groups

  end


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

      List.iter (fun e ->
		 ignore (JSU.(meth_call e "setTheme" [| inject editor_theme |]));
		 ignore (JSU.(meth_call (get_session e) "setMode" [| inject editor_mode |]));
		 JSU.(set e (Js.string "$blockScrolling") _Infinity)
		) [ editor; task_viewer ];
      JSU.(meth_call task_viewer "setReadOnly" [| inject Js._true|])

    let undo () =
      ignore JSU.(meth_call editor "undo" [| |])

    let redo () =
      ignore JSU.(meth_call editor "redo" [| |])

    let get_value ?(editor=editor) () : Js.js_string Js.t =
      JSU.meth_call editor "getValue" [| |]

    let set_value ~editor (str : Js.js_string Js.t) =
      ignore JSU.(meth_call editor "setValue" [| inject (str); inject ~-1 |])

    let _Range = Js.Unsafe.global##._Range

    let mk_range l1 c1 l2 c2 =
      new%js _Range (l1, c1, l2, c2)

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

(*
      let editor_bg = getElement AsHtml.div "why3-editor-bg"

      let disable () =
        ignore JSU.(meth_call editor "setReadOnly" [| inject Js._true|]);
        editor_bg ##. style ##. display := (Js.string "block")


      let enable () =
        ignore JSU.(meth_call editor "setReadOnly" [| inject Js._false|]);
        editor_bg ##. style ##. display := Js.string "none"
 *)

      let confirm_unsaved () =
        if not !saved then
          Js.to_bool
            (Dom_html.window ## confirm (Js.string "You have unsaved changes in your editor, proceed anyway ?"))
        else
          true

  end

(* TODO This is not necessary yet ???? *)
module ContextMenu =
  struct
    let task_menu = getElement AsHtml.div "why3-task-menu"
    let split_menu_entry = getElement AsHtml.li "why3-split-menu-entry"
    let prove_menu_entry = getElement AsHtml.li "why3-prove-menu-entry"
    let prove100_menu_entry = getElement AsHtml.li "why3-prove100-menu-entry"
    let prove1000_menu_entry = getElement AsHtml.li "why3-prove1000-menu-entry"
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

(*
    let add_action b f =
      b ##. onclick := Dom.handler (fun _ ->
				   hide ();
				   f ();
				   Editor.(focus editor);
				   Js._false)
 *)
    let () = addMouseEventListener false task_menu "mouseleave"
	(fun _ -> hide())


  end

module ToolBar =
  struct

    (* add_action to a button *)
    let add_action b f =
      let cb = fun _ ->
	f ();
(*
	Editor.(focus editor);
 *)
	Js._false
      in
      b ##. onclick := Dom.handler cb


    (* Current buttons *)
    (* TODO rename buttons *)
    let button_open = getElement AsHtml.button "why3-button-open"

    let button_save = getElement AsHtml.button "why3-button-save"

    let button_reload = getElement AsHtml.button "why3-button-undo"

    let button_redo = getElement AsHtml.button "why3-button-redo"

  end

type httpRequest =
  | Command of int * string
  | Get_task of string
  | Reload

let sendRequest r =
   let xhr = XmlHttpRequest.create () in
   let onreadystatechange () =
     if xhr ##. readyState == XmlHttpRequest.DONE then
       if xhr ##. status == 200 then
         PE.log_print_msg ("Http request '" ^ r ^ "' returned " ^ readBody xhr)
       else
         PE.log_print_msg ("Http request '" ^ r ^ "' failed with status " ^ string_of_int (xhr ##. status)) in
   xhr ## overrideMimeType (Js.string "text/json");
   let _ = xhr ## _open (Js.string "GET")
                (Js.string ("http://localhost:6789/request?"^r))  Js._true in
   xhr ##. onreadystatechange := (Js.wrap_callback onreadystatechange);
   xhr ## send (Js.null)

let sendRequest r =
  match r with
  | Reload -> sendRequest "reload"
  | Get_task n -> sendRequest ("gettask_"^n)
  | Command (n, c) ->
      sendRequest ("command=" ^ (string_of_int n)^","^c)

module Panel =
  struct
    let main_panel = getElement AsHtml.div "why3-main-panel"
    let task_list_container = getElement AsHtml.div "why3-task-list-container"
    let tab_container = getElement AsHtml.div "why3-tab-container"
    let resize_bar = getElement AsHtml.div "why3-resize-bar"
    let reset () =
      let edit_style = tab_container ##. style in
      JSU.(set edit_style (Js.string "flexGrow") (Js.string "2"));
      JSU.(set edit_style (Js.string "flexBasis") (Js.string ""))

    let () =
      let mouse_down = ref false in
      resize_bar ##. onmousedown := Dom.handler (fun _ -> mouse_down := true; Js._false);
      resize_bar ##. ondblclick := Dom.handler (fun _ -> reset (); Js._false);
      main_panel ##. onmouseup := Dom.handler (fun _ -> mouse_down := false; Js._false);
      main_panel ##. onmousemove :=
	Dom.handler (fun e ->
		     if !mouse_down then begin
			 let offset =
			   (e ##. clientX) - (main_panel ##. offsetLeft)
			 in
			 let offset = Js.string ((string_of_int offset) ^ "px") in
			 let edit_style = task_list_container ##. style in
			 JSU.(set edit_style (Js.string "flexGrow") (Js.string "0"));
			     JSU.(set edit_style (Js.string "flexBasis") offset);
			     Js._false
		       end
		     else Js._true)
  end


module TaskList =
  struct

    let selected_task = ref "0"

    let task_list = getElement AsHtml.div "why3-task-list"

    (* Task list as we get them from the server *)
    let printed_task_list = Hashtbl.create 16

    let print cls msg =
      task_list ##. innerHTML :=
        (Js.string ("<p class='" ^ cls ^ "'>" ^
                      msg ^ "</p>"))

    let print_error = print "why3-error"

    let print_msg = print "why3-msg"

    let mk_li_content id expl =
      Js.string (Format.sprintf
		   "<span id='%s_container'><span id='%s_icon'></span> %s <span id='%s_msg'></span></span><ul id='%s_ul'></ul>"
		   id id expl id id)

    let attach_to_parent id parent_id expl =
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

    let select_task id (span: Dom_html.element Js.t) pretty =
      (span ##. classList) ## add (Js.string "why3-task-selected");
      Hashtbl.add task_selection id span;
      selected_task := id;
      Editor.set_value ~editor:Editor.task_viewer (Js.string pretty);
      Editor.scroll_to_end Editor.task_viewer

    let deselect_task id =
      try
        let span= Hashtbl.find task_selection id in
        (span ##. classList) ## remove (Js.string "why3-task-selected");
        Hashtbl.remove task_selection id
      with
        Not_found -> ()

    let clear_task_selection () =
      let l = Hashtbl.fold (fun id _ acc -> id :: acc) task_selection [] in
      List.iter deselect_task l


    let clear () =
      clear_task_selection ();
      task_list ##. innerHTML := Js.string "";
      selected_task := "0";
      Hashtbl.clear printed_task_list;
      Editor.set_value ~editor:Editor.task_viewer (Js.string "")

    let () =
      Editor.set_on_event
        "focus"
        (Js.wrap_callback  clear_task_selection )

let onclick_do_something id =
  let span = getElement AsHtml.span (id ^ "_container") in
  span ##. onclick :=
    Dom.handler
      (fun ev ->
	let ctrl = Js.to_bool (ev ##. ctrlKey) in
	if is_selected id then
          if ctrl then deselect_task id else
	  clear_task_selection ()
	else begin
	  if not ctrl then clear_task_selection ();
          let pretty =
            try Hashtbl.find printed_task_list id
            with Not_found ->
              (sendRequest (Get_task id);
               "loading task, please wait")
          in (* TODO dummy value *)
          select_task id span pretty
        end;
	Js._false);
  addMouseEventListener
    true span "contextmenu"
    (fun e ->
      clear_task_selection ();
      let pretty =
        try Hashtbl.find printed_task_list id
        with Not_found -> (sendRequest (Get_task id); "")
      in
      select_task id span pretty;
      let x = max 0 ((e ##.clientX) - 2) in
      let y = max 0 ((e ##.clientY) - 2) in
      ContextMenu.show_at x y)

let update_status st id =
  try
    let span_icon = getElement AsHtml.span (id ^ "_icon") in
    let span_msg = getElement AsHtml.span (id ^ "_msg") in
    let cls =
      match st with
      | `Scheduled -> "fas fa-fw fa-cog why3-task-pending"
      | `Running -> "fas fa-fw fa-cog fa-spin why3-task-pending"
      | `Valid -> span_msg ##. innerHTML := Js.string "";
	  "fas fa-check-circle why3-task-valid"
      | `Unknown -> "fas fa-question-circle why3-task-unknown"
      | `Timeout -> "fas fa-clock-o why3-task-unknown"
      | `Failure -> "fas fa-bomb why3-task-unknown"
    in
    span_icon ##. className := Js.string cls
  with
    Not_found -> ()

(* Attach a new node to the task tree if it does not already exists *)
let attach_new_node nid parent (_ntype: node_type) name (_detached: bool) =
  let parent = string_of_int parent in
  let nid = string_of_int nid in
  try ignore (getElement_exn AsHtml.ul (nid^"_ul")) with
  | Not_found ->
      if nid != parent then
        attach_to_parent nid (parent^"_ul") name
      else
        attach_to_parent nid (parent^"_ul") name

let remove_node n =
  let element = getElement AsHtml.span n in
  let parent = element ##. parentNode in
  let parent = Js.Opt.to_option parent in
  match parent with
  | None -> failwith "TODO"
  | Some parent ->
      Dom.removeChild parent element

end

let interpNotif (n: notification) =
  PE.log_print_msg (Format.asprintf "interpNotif: %a@\n@." Itp_communication.print_notify n);
  match n with
  | Reset_whole_tree ->  TaskList.clear ()
  | Initialized _g ->
      PE.error_print_msg "Initialized"
  | New_node (nid, parent, ntype, name, detached) ->
      TaskList.attach_new_node nid parent ntype name detached;
      TaskList.onclick_do_something (string_of_int nid);
      sendRequest (Get_task (string_of_int nid))
  | File_contents (_f,_s) ->
     PE.error_print_msg "Notification File_contents not handled yet"
  | Source_and_ce _ ->
     PE.error_print_msg "Notification Source_and_ce not handled yet"
  | Next_Unproven_Node_Id (_nid1,_nid2) ->
     PE.error_print_msg "Notification Next_Unproven_Node_Id not handled yet"
  | Task (nid, task, _list_loc) -> (* TODO add color on sources *)
      Hashtbl.add TaskList.printed_task_list (string_of_int nid) task
  | Remove nid ->
      TaskList.remove_node (string_of_int nid)
  | Saved ->
      PE.error_print_msg "Saved"
  | Saving_needed _b ->
      PE.error_print_msg "Saving_needed"
  | Message m ->
    begin
      match m with
      | Proof_error (_nid, s) ->
        PE.error_print_msg
          (Format.asprintf "Proof error on selected node: \"%s\"" s)
      | Transf_error (_b, _ids, _tr, _args, _loc, s, _d) ->
        PE.error_print_msg
          (Format.asprintf "Transformation error on selected node: \"%s\"" s)
      | Strat_error (_nid, s) ->
        PE.error_print_msg
          (Format.asprintf "Strategy error on selected node: \"%s\"" s)
      | Query_Error (_nid, s) ->
        PE.error_print_msg
          (Format.asprintf "Query error on selected node: \"%s\"" s)
      | Query_Info (_nid, s) -> PE.error_print_msg s
      | Information s -> PE.error_print_msg s
      | Error s ->
          PE.error_print_msg
            (Format.asprintf "Error: \"%s\"" s)
      | Open_File_Error s ->
          PE.error_print_msg
            (Format.asprintf "Error while opening file: \"%s\"" s)
      | _ -> ();
      let s = Format.asprintf "%a" Json_util.print_notification n in
      PE.log_print_msg s
    end
  | Dead s ->
      PE.error_print_msg s
  | Node_change (nid, up) ->
    begin
      match up with
      | Proved true -> TaskList.update_status `Valid (string_of_int nid)
      | Proved false -> TaskList.update_status `Unknown (string_of_int nid)
      | Name_change _n -> assert false (* TODO *)
      | Proof_status_change (c, _obsolete, _rl) ->
        begin
        (* TODO complete other tests *)
          match c with
          | Controller_itp.Done pr ->
             TaskList.update_status
               Call_provers.(match pr.pr_answer with
                              | Valid -> `Valid
                              | Unknown _ -> `Unknown
                              | Timeout -> `Timeout
                              | _ -> `Failure)
               (string_of_int nid)
          | Controller_itp.Running -> TaskList.update_status `Running (string_of_int nid)
          | Controller_itp.Scheduled -> TaskList.update_status `Scheduled (string_of_int nid)
          | _ -> TaskList.update_status `Failure (string_of_int nid)
        end
    end

exception NoNotification

let interpNotifications l =
  match l with
  | [] -> ()
  | l -> List.iter interpNotif l

let getNotification2 () =
  let xhr = XmlHttpRequest.create () in
  let onreadystatechange () =
    if xhr ##. readyState == XmlHttpRequest.DONE then
      let stat = xhr ##. status in
      if stat == 200 then
        let r = readBody xhr in
        let nl =
          try Json_util.parse_list_notification r
          with e ->
               let s = "ERROR in getNotification2: Json_util.parse_list_notification raised " ^
                         Printexc.to_string e ^ " on the following notification: " ^ r in
               log s;
               PE.log_print_msg s;
               []
        in
        interpNotifications nl
      else
        if stat == 0 then
          PE.log_print_msg "Why3 Web server not responding (HttpRequest got answer with status 0)"
        else
          begin
            let s = "getNotification2: state changed to unknown status " ^ string_of_int stat in
            log s;
            PE.log_print_msg s
          end
  in
  (xhr ##. onreadystatechange :=
    (Js.wrap_callback onreadystatechange));
  xhr ## overrideMimeType (Js.string "text/json");
  let _ = xhr ## _open (Js.string "GET")
                (Js.string "http://localhost:6789/getNotifications") Js._true in
  xhr ## send (Js.null)

let notifHandler = ref None

let startNotificationHandler () =
   if (!notifHandler = None) then
     notifHandler := Some (Dom_html.window ## setInterval
                       (Js.wrap_callback getNotification2)  (Js.float 1000.0))

let () = startNotificationHandler ()

let stopNotificationHandler () =
   match !notifHandler with
   | None -> ()
   | Some n -> Dom_html.window ## clearInterval (n); notifHandler := None


(* TODO make a module *)
(* Form for commands *)
let form = getElement AsHtml.form "why3-form"

let () = Js.Unsafe.set form "target" "form-answer"

let () =  form ##. onsubmit := Dom.full_handler
    (fun _ _ -> let a = Form.get_form_contents form in
    List.iter (fun x -> match x with
    | (c, s) when c = "command" ->
        sendRequest
          (Command
             (int_of_string !TaskList.selected_task, s))
    | _ -> ()) a; Js._false)

let () =
  ToolBar.(add_action button_open
    (fun () -> PE.log_print_msg "Open"; startNotificationHandler ()))

let () =
  ToolBar.(add_action button_save
    (fun () -> PE.log_print_msg "Save"; stopNotificationHandler ()))

let () =
  ToolBar.(add_action button_reload
    (fun () -> PE.log_print_msg "Reload"; TaskList.clear (); sendRequest Reload))

(* TODO Server handling *)
(*let () = Js.Unsafe.global##stopNotificationHandler <-
   Js.wrap_callback stopNotificationHandler

let () = Js.Unsafe.global##startNotificationHandler <-
   Js.wrap_callback startNotificationHandler
*)

(* let () = Js.Unsafe.global##sendRequest <- Js.wrap_callback sendRequest *)

let () = Js.Unsafe.global##.getNotification1 := Js.wrap_callback getNotification2
(*
let () = Js.Unsafe.global## PE.printAnswer1 <-
  Js.wrap_callback (fun s -> PE.printAnswer s)
*)
