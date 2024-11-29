(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* simple helpers *)
open Worker_proto
open Bindings

module Js = Js_of_ocaml.Js
module JSU = Js_of_ocaml.Js.Unsafe
module Dom = Js_of_ocaml.Dom
module File = Js_of_ocaml.File
module Worker = Js_of_ocaml.Worker
module Dom_html = Js_of_ocaml.Dom_html

let (!!) = Js.string

let int_of_js_string = Js.parseInt
let js_string_of_int n = (Js.number_of_float (float_of_int n)) ## toString

module AsHtml = struct
    include Dom_html.CoerceTo
    let span e = element e
  end


let select e cls =
  Dom.list_of_nodeList (e ## querySelectorAll cls)

let getElement_exn cast id =
  Js.Opt.get (cast (Dom_html.getElementById id)) (fun () -> raise Not_found)

let getElement cast id =
  try
    getElement_exn cast id
  with
    Not_found ->
    log ("Element " ^ id ^ " does not exist or has invalid type");
    assert false

let addMouseEventListener prevent o (e : Js.js_string Js.t) f =
    let cb =
      Js.wrap_callback (fun (e : Dom_html.mouseEvent Js.t) ->
          if prevent then Dom.preventDefault e;
          f e;
          Js._false
        ) in
    ignore JSU.(meth_call o "addEventListener"
                  [| inject e;
                    inject cb;
                    inject Js._false |])

module Session = struct

  let localStorage =
    check_def "localStorage" (Dom_html.window ##. localStorage)

  let save_view_mode m =
    localStorage ## setItem !!"why3-view-mode" m

  let save_buffer lang name content =
    localStorage ## setItem !!"why3-buffer-lang" lang;
    localStorage ## setItem !!"why3-buffer-name" name;
    localStorage ## setItem !!"why3-buffer-content" content

  let get_item s def =
    Js.Opt.get (localStorage ## getItem s) (fun () -> def)

  let load_view_mode () =
    get_item !!"why3-view-mode" !!"wide"

  let load_buffer () =
    let lang = get_item !!"why3-buffer-lang" !!"" in
    let name = get_item !!"why3-buffer-name" !!"" in
    let buffer = get_item !!"why3-buffer-content" !!"" in
    (lang, name, buffer)

  let to_save = ref []

  let attach input store =
    let default = input ##. value in
    to_save := (input, store, default) :: !to_save;
    let v = get_item store default in
    input ##. value := v;
    v

  let save () =
    List.iter (fun (input, store, default) ->
        let v = input ##. value in
        if Js.to_string v = Js.to_string default then
          localStorage ## removeItem store
        else
          localStorage ## setItem store v;
        (* some browsers remember values upon reload, thus corrupting default settings *)
        input ##. value := default
      ) !to_save

end

module Buttons = struct

  let button_open = getElement AsHtml.button "why3-button-open"
  let real_save = getElement AsHtml.a "why3-save-as"
  let button_save = getElement AsHtml.button "why3-button-save"
  let button_export = getElement AsHtml.button "why3-button-export"

  let button_undo = getElement AsHtml.button "why3-button-undo"
  let button_redo = getElement AsHtml.button "why3-button-redo"

  let button_execute = getElement AsHtml.button "why3-button-execute"
  let button_compile = getElement AsHtml.button "why3-button-compile"
  let button_stop = getElement AsHtml.button "why3-button-stop"

  let button_settings = getElement AsHtml.button "why3-button-settings"
  let button_help = getElement AsHtml.button "why3-button-help"
  let button_about = getElement AsHtml.button "why3-button-about"

  let disable b =
    b ##. disabled := Js._true;
    b ##. classList ## add !!"why3-inactive"

  let enable b =
    b ##. disabled := Js._false;
    b ##. classList ## remove !!"why3-inactive"

  let change b v =
    if v = Js.to_bool (b ##. disabled) then
      if v then enable b
      else disable b

end

module Ace = Ace ()

module Editor = struct

    let name = ref !!""
    let callback = ref (fun () -> ())

    let editor =
      let e = Ace.edit !!"why3-editor" in
      check_def "why3-editor" e

    let task_viewer =
      let e = Ace.edit !!"why3-task-viewer" in
      check_def "why3-task-viewer" e

    let set_annotations l =
      let a =
        Array.map (fun (r,c,t,k) -> Ace.annotation r c t k) (Array.of_list l)
      in
      let a = Js.array a in
      editor ## getSession ## setAnnotations a

    let clear_annotations () =
      editor ## getSession ## clearAnnotations

    let scroll_to_end e =
      let len = e ## getSession ## getLength in
      let last_line = len - 1 in
      e ## gotoLine last_line 0 Js._false

    let () =
      let editor_theme : Js.js_string Js.t = get_global "editor_theme" in
      let task_viewer_mode : Js.js_string Js.t = get_global "task_viewer_mode" in

      editor ## setTheme editor_theme;

      task_viewer ## setTheme editor_theme;
      task_viewer ## getSession ## setMode task_viewer_mode;

      task_viewer ## setReadOnly Js._true

    let undo () =
      editor ## undo

    let redo () =
      editor ## redo

    let update_undo () =
      let manager = editor ## getSession ## getUndoManager in
      Buttons.(change button_undo) (Js.to_bool (manager ## hasUndo));
      Buttons.(change button_redo) (Js.to_bool (manager ## hasRedo))

    let get_value ?(editor=editor) () =
      editor ## getValue

    let set_value ?(editor=editor) ?(active_callback=true) str =
      editor ## setValue str ~-1;
      editor ## getSession ## getUndoManager ## markClean;
      if active_callback then !callback ()

    let mk_range l1 c1 l2 c2 =
      new%js Ace.range l1 c1 l2 c2

    let add_marker cls r =
      editor ## getSession ## addMarker r cls !!"text" Js._false

    let remove_marker m =
      editor ## getSession ## removeMarker m

    (* old code, left for reference
      let get_char buffer i = int_of_float (buffer ## charCodeAt(i))
     *)
    let why3_loc_to_range buffer loc =
      (* old code, left for reference
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
       *)
      ignore buffer;
      let bl, bc, el, ec = loc in
      mk_range (bl-1) bc (el-1) ec


      let editor_bg = getElement AsHtml.div "why3-editor-bg"

      let disable () =
        editor ## setReadOnly Js._true;
        editor_bg ##. style ##. display := !!"block"


      let enable () =
        editor ## setReadOnly Js._false;
        editor_bg ##. style ##. display := !!"none"

      let is_clean () =
        Js.to_bool (editor ## getSession ## getUndoManager ## isClean)

      let confirm_unsaved () =
        is_clean () ||
          Js.to_bool (Dom_html.window ## confirm
                        !!"You have unsaved changes in your editor, proceed anyway ?")

    let error_marker = ref None

    let update_error_marker new_m =
      begin match !error_marker with
      | Some (m, _) -> remove_marker m
      | None -> ()
      end;
      error_marker := new_m

  end

module Tabs = struct

  let () =
    let tab_groups = select Dom_html.document !!".why3-tab-group" in
    List.iter (fun tab_group ->
        let labels = select tab_group !!".why3-tab-label" in
        List.iter (fun tab ->
            tab ##. onclick :=
              Dom.handler (fun _ev ->
                  if Js.to_bool (tab ##. classList ## contains !!"why3-inactive") then begin
                      List.iter (fun t ->
                          ignore (t ##. classList ## add !!"why3-inactive")
                        ) labels;
                      tab ##. classList ## remove !!"why3-inactive"
                    end;
                  Js._false)
          ) labels)
      tab_groups

  let focus id =

    (Dom_html.getElementById id) ## click

end

module Dialogs = struct

  let dialog_panel = getElement AsHtml.div "why3-dialog-panel"
  let setting_dialog = getElement AsHtml.div "why3-setting-dialog"
  let about_dialog = getElement AsHtml.div "why3-about-dialog"
  let button_close = getElement AsHtml.button "why3-close-dialog-button"
  let input_num_threads = getElement AsHtml.input "why3-input-num-threads"
  let input_num_steps = getElement AsHtml.input "why3-input-num-steps"
  let input_min_steps = getElement AsHtml.input "why3-input-min-steps"
  let radio_wide = getElement AsHtml.input "why3-radio-wide"
  let radio_column = getElement AsHtml.input "why3-radio-column"

  let input_context_steps =
    let t = Array.make 3 input_num_steps in
    for i = 0 to 2 do
      let id = Printf.sprintf "why3-input-context-steps%d" (i+1) in
      t.(i) <- getElement AsHtml.input id
    done;
    t


  let all_dialogs = [ setting_dialog; about_dialog ]
  let show diag () =
    dialog_panel ##. style ##. display := !!"flex";
    diag ##. style ##. display := !!"inline-block";
    diag ## focus

  let close () =
    List.iter (fun d -> d ##. style ##. display := !!"none") all_dialogs;
    dialog_panel ##. style ##. display := !!"none"

  let set_onchange o f =
    o ##. onchange := Dom.handler (fun _ -> f o; Js._false)
end

module ContextMenu = struct

    let task_menu = getElement AsHtml.div "why3-task-menu"
    let split_menu_entry = getElement AsHtml.li "why3-split-menu-entry"
    let prove_menu_entry = getElement AsHtml.li "why3-prove-menu-entry"
    let clean_menu_entry = getElement AsHtml.li "why3-clean-menu-entry"
    let enabled = ref true

    let alt_ergo_context_steps =
      let get i =
        let v =
          Session.attach Dialogs.input_context_steps.(i)
            (Js.string (Printf.sprintf "why3-context-steps%d" i)) in
        int_of_js_string v in
      Array.init 3 get

    let prove_menu_entries =
      let t = Array.make 3 prove_menu_entry in
      for i = 0 to 2 do
        let id = Printf.sprintf "why3-prove%d-menu-entry" (i+1) in
        t.(i) <- getElement AsHtml.li id
      done;
      t


    let enable () = enabled := true
    let disable () = enabled := false

    let show_at x y =
      if !enabled then begin
          task_menu ##. style ##. display := !!"block";
          task_menu ##. style ##. left := (js_string_of_int x) ## concat !!"px";
          task_menu ##. style ##. top := (js_string_of_int y) ## concat !!"px"
        end

    let hide () =
      if !enabled then
        task_menu ##. style ##. display := !!"none"

    let add_action b f =
      b ##. onclick :=
        Dom.handler (fun _ ->
            hide ();
            f ();
            Editor.editor ## focus;
            Js._false)

    let change_prove_context () =
      let span = "<span class='fas fa-magic why3-icon'></span>" in
      for i = 0 to 2 do
        prove_menu_entries.(i) ##. innerHTML :=
          Js.string (Printf.sprintf "%s Prove (%d steps)" span alt_ergo_context_steps.(i))
      done

    let get_context_step i =
      alt_ergo_context_steps.(i)

    let () =
      change_prove_context ();
      addMouseEventListener false task_menu !!"mouseleave" (fun _ -> hide())

  end

module FormatList = struct

  let select_format = getElement AsHtml.select "why3-select-format"
  let format_label = getElement AsHtml.span "why3-format-label"

  let selected_format = ref ""

  let formats = ref []

  let change_mode lang =
    let mode =
      match lang with
      | "python" -> !!"python"
      | "micro-C" -> !!"c_cpp"
      | _ -> !!"why3" in
    let mode = !!"ace/mode/" ## concat mode in
    Editor.editor ## getSession ## setMode mode

  let change_url lang =
    let url = new%js Url._URL (Dom_html.window ##. location ##. href) in
    let search = url ##. searchParams in
    if Js.to_bool (search ## has !!"lang") && lang <> "" then
      begin
        search ## set !!"lang" (Js.string lang);
        Dom_html.window ##. history ## replaceState Js.null !!"" (Js.some (url ##. href))
      end

  let handle _ =
    let i = select_format ##. selectedIndex in
    let name =
      match List.nth_opt !formats i with
      | Some (name, ext :: _) ->
          Editor.name := Js.string ("test." ^ ext);
          name
      | Some (name, []) -> name
      | _ -> "" in
    change_mode name;
    selected_format := name;
    change_url name

  let add_format text =
    let option = Dom_html.createOption Dom_html.document in
    option ##. value := text;
    option ##. innerHTML := text;
    Dom.appendChild select_format option

  let set_format name idx =
    selected_format := name;
    select_format ##. selectedIndex := idx;
    change_mode name;
    change_url name

  let set_format name idx =
    if idx = -1 then
      match !formats with
      | (name, _) :: _ ->
          if select_format ##. selectedIndex = -1 then
            set_format name 0
      | [] -> ()
    else set_format name idx

  let resolve_format name =
    let ext =
      let arr = name ## split !!"." in
      let arr = Js.to_array (Js.str_array arr) in
      let l = Array.length arr in
      Js.to_string arr.(l - 1) in
    let rec aux i = function
      | (name, exts) :: l ->
          if List.mem ext exts then (name, i)
          else aux (i + 1) l
      | [] -> ("", -1) in
    let (name, idx) = aux 0 !formats in
    set_format name idx

  let set_format name =
    let rec aux i = function
      | (n, _) :: l ->
          if n = name then (name, i)
          else aux (i + 1) l
      | _ -> ("", -1) in
    let (name, idx) = aux 0 !formats in
    set_format name idx

  let add_formats l =
    let fresh = !formats = [] in
    formats := l;
    List.iter (fun (name, _) -> add_format (Js.string name)) l;
    format_label ##. className := !!"fas fa-code why3-icon";
    if fresh then
      if !selected_format <> "" then
        if String.contains !selected_format '.' then
          resolve_format (Js.string !selected_format)
        else
          set_format !selected_format
      else
        let () = select_format ##. selectedIndex := 0 in
        ignore (handle ())

  let enable () =
    select_format ##. disabled := Js._false

  let disable () =
    select_format ##. disabled := Js._true

  let set_onchange o f =
      o ##. onchange := Dom.handler (fun _ -> handle (); f (); Js._false)

end

module ExampleList = struct

    let select_example = getElement AsHtml.select "why3-select-example"
    let example_label = getElement AsHtml.span "why3-example-label"
    let set_loading_label b =
      select_example ##. disabled := Js.bool b;
      if b then
        example_label ##. className := !!"fas fa-spin fa-spinner why3-icon"
      else
        example_label ##. className := !!"fas fa-book why3-icon"

    let config = ref Json_base.Null

    let selected_index = ref (-1)
    let unselect () =
      selected_index := -1;
      select_example ##. selectedIndex := -1

    let handle () =
      let filename url =
        let arr = url ## split !!"/" in
        let arr = Js.to_array (Js.str_array arr) in
        arr.(Array.length arr - 1) in
      let sessionStorage =
        check_def "sessionStorage" (Dom_html.window ##. sessionStorage) in
      selected_index := select_example ##. selectedIndex;
      let url = select_example ##. value in
      let name = filename url in
      FormatList.resolve_format name;
      let set_content s =
        Editor.set_value s;
        Editor.name := name;
        Editor.editor ## focus in
      begin match Js.Opt.to_option (sessionStorage ## getItem url) with
      | Some s -> set_content s
      | None ->
          let upd mlw =
            sessionStorage ## setItem url mlw;
            set_content mlw;
            set_loading_label false
          in
          set_loading_label true;
          Promise.catch
            (Promise.bind_unit
               (Promise.bind (Fetch.fetch url)
                  (fun r -> r ## text))
               (fun s -> upd s))
            (fun _ -> set_loading_label false)
      end

    let handle _ =
      if Editor.confirm_unsaved () then handle ()
      else select_example ##. selectedIndex := !selected_index;
      Js._false

    let add_example text url =
      let option = Dom_html.createOption Dom_html.document in
      option ##. value := url;
      option ##. innerHTML := text;
      Dom.appendChild select_example option

    let update () =
      select_example ##. innerHTML := !!"";
      let i = ref 0 in
      begin match Json_base.get_field !config !FormatList.selected_format with
      | Json_base.Record list ->
          List.iter (fun (s, url) ->
              let url = !!"examples/" ## concat (Js.string (Json_base.get_string url)) in
              add_example (Js.string s) url;
              incr i
            ) list
      | _ -> log "no example list"
      | exception Not_found -> log "no example list"
      end;
      set_loading_label false;
      select_example ##. disabled := Js.bool (!i = 0);
      unselect ()

    let () =
      select_example ##. onchange := Dom.handler handle

    let enable () =
      select_example ##. disabled := Js._false

    let disable () =
      select_example ##. disabled := Js._true
  end

module TaskList = struct

    let task_list = getElement AsHtml.div "why3-task-list"
    let theory_id_list = ref ([]: int list)
    let add_theory_id id = theory_id_list := id::!theory_id_list
    let clear_theory_id_list () = theory_id_list := []
    let is_theory id = List.mem id !theory_id_list

    let has_to_be_splitted = ref ([]: int list)
    let add_has_to_be_splitted id = has_to_be_splitted := id::!has_to_be_splitted
    let remove_has_to_be_splitted id =
      has_to_be_splitted := List.fold_left (fun acc e -> if e <> id then e::acc else acc) [] !has_to_be_splitted
    let clear_has_to_be_splitted () = has_to_be_splitted := []
    let has_to_be_split id = List.mem id !has_to_be_splitted

    let print cls msg =
      task_list ##. innerHTML :=
        (Js.string ("<p class='" ^ cls ^ "'>" ^
                      msg ^ "</p>"))

    let print_error = print "why3-error"

    let print_msg = print "why3-msg"

    let print_alt_ergo_output id res =
      let span_msg = getElement AsHtml.span (Printf.sprintf "id%d_msg" id) in
      match res with
        Valid -> span_msg ##. innerHTML := !!""
      | Unknown msg -> span_msg ##. innerHTML := Js.string (" (" ^ msg ^ ")")
      | Invalid msg -> span_msg ##. innerHTML := Js.string (" (" ^ msg ^ ")")


    let mk_li_content id expl isTheory =
      if isTheory then
        Js.string (Format.sprintf
                     "<span id='%s_container'> <span id='%s_icon'></span> \
                        %s \
                        <span id='%s_msg'></span> </span> <ul id='%s_ul'></ul>"
                     id id expl id id)
      else begin
        let btnProve =
          Format.sprintf
            "<span id='%s_prove_button' title='Prove'> \
              <i class='fas fa-magic why3-task-button-i'></i></span>" id in
        let btnSplit =
          Format.sprintf
            "<span id='%s_split_button' title='Split'> \
              <i class='fas fa-project-diagram why3-task-button-i'></i></span>" id in

        Js.string (Format.sprintf
                     "<span id='%s_container'> <span id='%s_icon'></span> \
                        %s %s %s \
                        <span id='%s_msg'></span> </span> <ul id='%s_ul'></ul>"
                     id id btnProve btnSplit expl id id)
      end

    let clean_task id =
      try
        let ul = getElement_exn AsHtml.ul (Printf.sprintf "id%d_ul" id) in
        ul ##. innerHTML := !!""
      with
        Not_found -> ()

    let task_selection : (int, _) Hashtbl.t = Hashtbl.create 17
    let is_selected id = Hashtbl.mem task_selection id
    let select_task id span loc pretty =
      span ##. classList ## add !!"why3-task-selected";
      let markers = List.map (fun (cls, range) -> Editor.add_marker (Js.string cls) range) loc in
      Hashtbl.add task_selection id (span, loc, markers);
      Editor.set_value ~editor:Editor.task_viewer (Js.string pretty);
      Editor.scroll_to_end Editor.task_viewer

    let deselect_task id =
      try
        let span, _loc, markers = Hashtbl.find task_selection id in
        span ##. classList ## remove !!"why3-task-selected";
        List.iter Editor.remove_marker markers;
        Hashtbl.remove task_selection id
      with
        Not_found -> ()

    let clear_task_selection () =
      let l = Hashtbl.fold (fun id _ acc -> id :: acc) task_selection [] in
      List.iter deselect_task l

    let attach_to_parent id parent_id expl locs pretty =
      let doc = Dom_html.document in
      let ul =
        try
          getElement_exn AsHtml.ul parent_id
        with
          Not_found ->
          let ul = Dom_html.createUl doc in
          ul ##. id := Js.string parent_id;
          Dom.appendChild task_list ul;
          ul
      in
      let li = Dom_html.createLi doc in
      li ##. id := Js.string id;
      Dom.appendChild ul li;

      match pretty with
      | None ->
        li ##. innerHTML := mk_li_content id expl true
      | Some (pretty) ->
        li ##. innerHTML := mk_li_content id expl false;
        let buttonProve = getElement AsHtml.span (Printf.sprintf "%s_prove_button" id) in
        let buttonSplit = getElement AsHtml.span (Printf.sprintf "%s_split_button" id) in
        let idInt = int_of_string (String.sub id 2 (String.length id - 2)) in

        let span = getElement AsHtml.span (Printf.sprintf "%s_container" id) in
        let buffer = Editor.get_value () in
        let locs = List.map (fun (k, loc) -> k, Editor.why3_loc_to_range buffer loc) locs in

        buttonProve ##. onclick :=
          Dom.handler
          (fun _ ->
            clear_task_selection ();
            select_task idInt span locs pretty;
            ContextMenu.prove_menu_entry ## click;
            Js._false);

        buttonSplit ##. onclick :=
          Dom.handler
          (fun _ ->
            clear_task_selection ();
            select_task idInt span locs pretty;
            ContextMenu.split_menu_entry ## click;
            Js._false)

    let clear () =
      clear_theory_id_list ();
      clear_has_to_be_splitted ();
      clear_task_selection ();
      task_list ##. innerHTML := !!"";
      Editor.set_value ~editor:Editor.task_viewer ~active_callback:false !!""

    let add_task id parent_id expl locs pretty =
      attach_to_parent (Printf.sprintf "id%d" id) (Printf.sprintf "id%d_ul" parent_id) expl locs (Some pretty) ;
      let span = getElement AsHtml.span (Printf.sprintf "id%d_container" id) in
      let buffer = Editor.get_value () in
      let locs = List.map (fun (k, loc) -> k, Editor.why3_loc_to_range buffer loc) locs in
      span ##. onclick :=
        Dom.handler (fun ev ->
            let ctrl = Js.to_bool (ev ##. ctrlKey) || Js.to_bool (ev ##. metaKey) in
            if is_selected id then
              if ctrl then deselect_task id
              else clear_task_selection ()
            else
              begin
                if not ctrl then clear_task_selection ();
                select_task id span locs pretty
              end;
            Js._false);
      addMouseEventListener true span !!"contextmenu" (fun e ->
          clear_task_selection ();
          select_task id span locs pretty;
          let x = max 0 (e ##. clientX - 2) in
          let y = max 0 (e ##. clientY - 2) in
          ContextMenu.show_at x y)

    let () =
      Editor.editor ## on !!"change"
        (Js.wrap_callback (fun _ _ ->
             clear ();
             Editor.clear_annotations ();
             Editor.update_error_marker None))

    let () =
      Editor.editor ## on !!"input"
        (Js.wrap_callback (fun _ _ ->
             if not (Editor.is_clean ()) then ExampleList.unselect ();
             Editor.update_undo ()))

    let () =
      Editor.editor ## on !!"focus"
        (Js.wrap_callback (fun _ _ -> clear_task_selection ()))

  end

let handle_why3_message o =
  let doc = Dom_html.document in
  match o with
  | Idle | Warning [] -> ()
  | Warning lst ->
      let annot =
        List.map (fun ((l1, c1), msg) ->
            (l1,c1, Js.string msg, !!"warning")) lst
      in
      Editor.set_annotations annot

  | Error s -> TaskList.print_error s

  | ErrorLoc ((l1, b, l2, e), s) ->
      let r = Editor.mk_range l1 b l2 e in
      Editor.update_error_marker (Some (Editor.add_marker !!"why3-error" r, r));
      TaskList.print_error s;
      Editor.set_annotations [ (l1, b, Js.string s, !!"error") ]

  | Result sl ->
      TaskList.clear ();
      let ul = Dom_html.createUl doc in
      ul ## setAttribute !!"id" !!"why3-exec-list";
      Dom.appendChild TaskList.task_list ul;
      List.iter (fun s ->
          let verb = Dom_html.createPre doc in
          verb ##. innerText := Js.string s;
          let li = Dom_html.createLi doc in
          Dom.appendChild li verb;
          Dom.appendChild ul li) sl

  | Theory (th_id, th_name) ->
      TaskList.add_theory_id th_id;
      TaskList.attach_to_parent (Printf.sprintf "id%d" th_id) "why3-theory-list" th_name [] None

  | Task (id, parent_id, expl, _code, locs, pretty, _steps) ->
      begin match Dom_html.getElementById_opt (Printf.sprintf "id%d" id) with
      | Some _ -> ()
      | None ->
        TaskList.add_task id parent_id expl locs pretty;
        (* If the added task is the child of a theory, we select it in order to split it *)
        if TaskList.is_theory parent_id then
          let span = getElement AsHtml.span (Printf.sprintf "id%d_container" id) in
          let buffer = Editor.get_value () in
          let loc = List.map (fun (k, loc) -> k, Editor.why3_loc_to_range buffer loc) locs in
          TaskList.select_task id span loc pretty;
          TaskList.add_has_to_be_splitted id
      end

  | Formats l ->
      FormatList.add_formats l;
      ExampleList.update ()

  | UpdateStatus(st, id) ->
      try
        let span_icon = getElement AsHtml.span (Printf.sprintf "id%d_icon" id) in
        let span_msg = getElement AsHtml.span (Printf.sprintf "id%d_msg" id) in
        let cls =
          match st with
          | StNew ->
              "fas fa-fw fa-cog fa-spin fa-fw why3-task-pending"
          | StValid ->
              span_msg ##. innerHTML := !!"";
              TaskList.deselect_task id;
              "fas fa-check-circle why3-task-valid"
          | StUnknown ->
              (*
               * These lines will split the selected tasks. It's useful when we hit the
               * verify button because we want all unproven generated tasks to be split
              *)
              if TaskList.has_to_be_split id then
              begin
                TaskList.remove_has_to_be_splitted id;
                ContextMenu.split_menu_entry ## click;
              end;

              "fas fa-question-circle why3-task-unknown"
        in
        span_icon ##. className := !!cls;
      with
        Not_found -> ()


module ToolBar = struct

  let add_action b f =
    let cb = fun _ ->
      f ();
      Editor.editor ## focus;
      Js._false in
    b ##. onclick := Dom.handler cb


  let disable_compile () =
    Editor.disable ();
    ContextMenu.disable ();
    FormatList.disable ();
    ExampleList.disable ();
    let open Buttons in
    disable button_open;
    disable button_undo;
    disable button_redo;
    disable button_execute;
    disable button_compile

  let enable_compile () =
    Editor.enable ();
    ContextMenu.enable ();
    FormatList.enable ();
    ExampleList.enable ();
    let open Buttons in
    enable button_open;
    Editor.update_undo ();
    enable button_execute;
    enable button_compile;
    enable button_stop

  let disable_toolbar () =
    disable_compile ();
    let open Buttons in
    disable button_stop;
    disable button_about;
    disable button_settings;
    disable button_save;
    disable button_help;
    disable button_export

  let enable_toolbar () =
    enable_compile ();
    let open Buttons in
    enable button_stop;
    enable button_about;
    enable button_settings;
    enable button_save;
    enable button_help;
    enable button_export

  let name () =
      if !Editor.name ##. length == 0 then !!"test.mlw" else !Editor.name

  let mk_save () =
    let blob =
      let code = Editor.get_value () in
      File.blob_from_any ~contentType:"text/plain" ~endings:`Native [`js_string code]
    in

    blob, name ()

  let save_default () =
    let blob, name = mk_save () in
    let url = Dom_html.window ##. _URL ## createObjectURL blob in
    Buttons.real_save ##. href := url;
    JSU.(set Buttons.real_save !!"download" name);
    Buttons.real_save ## click
    (* does not work with firefox *)
    (*ignore JSU.(meth_call _URL "revokeObjectURL" [| inject url |]) *)

  let save =
    let nav = Dom_html.window ##. navigator in
    match Js.Optdef.to_option (JSU.get nav !!"msSaveBlob") with
    | None -> save_default
    | Some _f ->
        fun () ->
        let blob, name = mk_save () in
        ignore JSU.(meth_call nav "msSaveBlob" [| inject blob; inject name |])

  let finish_open url reader _ =
    match Js.Opt.to_option (File.CoerceTo.string (reader ##. result)) with
    | None -> Js._true
    | Some content ->
        ExampleList.unselect ();
        let name = File.filename url in
        FormatList.resolve_format name;
        Editor.name := name;
        Editor.set_value content;
        ExampleList.update ();
        Js._true

  let open_ = getElement AsHtml.input "why3-open"

  let start_open _ =
    match Js.Optdef.to_option (open_ ##. files) with
    | None -> Js._false
    | Some f ->
        match Js.Opt.to_option (f ## item 0) with
        | None -> Js._false
        | Some f ->
            let reader = new%js File.fileReader in
            reader ##. onloadend := Dom.handler (finish_open f reader);
            reader ## readAsText (f :> File.blob Js.t);
            Js._true

  let () =
    open_ ##. onchange := Dom.handler start_open

  let open_ () = if Editor.confirm_unsaved () then open_ ## click

  let export () =
    let code = Js.to_string (Editor.get_value ()) in
    let code = Shortener.encode code in
    let clip = getElement AsHtml.textarea "why3-clipboard" in
    let url = new%js Url._URL (Dom_html.window ##. location ##. href) in
    let search = url ##. searchParams in
    search ## set !!"name" (name ());
    search ## set !!"lang" (Js.string !FormatList.selected_format);
    search ## set !!"code" (Js.string code);
    clip ##. value := url ##. href;
    clip ## select;
    Dom_html.document ## execCommand !!"Copy" Js._false Js.null

end

module Panel = struct

    let main_panel = getElement AsHtml.div "why3-main-panel"
    let editor_container = getElement AsHtml.div "why3-editor-container"
    let resize_bar = getElement AsHtml.div "why3-resize-bar"
    let reset () =
      let edit_style = editor_container ##. style in
      JSU.(set edit_style !!"flexGrow" !!"2");
      JSU.(set edit_style !!"flexBasis" !!"")

    let set_wide b =
      reset ();
      main_panel ##. classList ## remove !!"why3-wide-view";
      main_panel ##. classList ## remove !!"why3-column-view";
      if b then
        main_panel ##. classList ## add !!"why3-wide-view"
      else
        main_panel ##. classList ## add !!"why3-column-view"

    let is_wide () =
      Js.to_bool (main_panel ##. classList ## contains !!"why3-wide-view")

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
                let offset = (js_string_of_int offset) ## concat !!"px" in
                let edit_style = editor_container ##. style in
                JSU.(set edit_style !!"flexGrow" !!"0");
                JSU.(set edit_style !!"flexBasis" offset);
                Js._false
              end
            else Js._true)
  end

module KeyBinding = struct

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
            Dom.preventDefault ev;
            f ();
            Js._false)

  let add_global ?(ctrl=Js._false) ?(shift=Js._false) ?(alt=Js._false) ?(meta=Js._false) keycode f =
    let i = min (Array.length callbacks) (max 0 keycode) in
    let t = callbacks.(i) in
    t.(pack ctrl shift meta alt) <- Some f

end

module Controller = struct

    let task_queue  = Queue.create ()

    let first_task = ref true
    type 'a status = Free of 'a | Busy of 'a * Worker_proto.id | Absent

    let alt_ergo_default_steps =
      let v = Session.attach Dialogs.input_num_steps !!"why3-num-steps" in
      ref (int_of_js_string v)

    let alt_ergo_min_steps =
      let v = Session.attach Dialogs.input_min_steps !!"why3-min-steps" in
      ref (int_of_js_string v)

    let alt_ergo_workers =
      let v = Session.attach Dialogs.input_num_threads !!"why3-num-threads" in
      ref (Array.make (int_of_js_string v) Absent)

    let why3_busy = ref false
    let why3_worker = ref None

    let get_why3_worker () =
      match !why3_worker with
      | Some w -> w
      | None -> log ("Why3 Worker not initialized !"); assert false

    let alt_ergo_idle () =
      Array.for_all (function Busy _ -> false | _ -> true) !alt_ergo_workers

    let is_idle () =
      alt_ergo_idle () && Queue.is_empty task_queue && not !why3_busy

    let process_task i w id s steps =
      let open Json_base in
      let convert v = Js.string (Format.asprintf "%a" print_json v) in
      let input =
        convert
          (Record
             ["worker_id", Int id;
              "content",
              List (List.map (fun x -> String x) (String.split_on_char '\n' s))]) in
      let options =
        convert
          (Record
             ["steps_bound", Int (if steps >= 0 then steps else !alt_ergo_default_steps);
              "input_format", String "Native";
              "debug", Bool true]) in
      !alt_ergo_workers.(i) <- Busy (w, id);
      w ## postMessage (input, options)

    let update_status id status =
      handle_why3_message (UpdateStatus (status, id));
      (get_why3_worker ()) ## postMessage (marshal (SetStatus (status, id)))

    let rec get_free_ae_worker () =
      let rec aux i =
        if i >= 0 then
          match !alt_ergo_workers.(i) with
          | Free w -> Some (i, w)
          | Absent ->
              let w = init_ae_worker i in
              Some (i, w)
          | Busy _ -> aux (i - 1)
        else None in
      aux (Array.length !alt_ergo_workers - 1)

    and pop_task () =
      match Queue.take task_queue with
      | (id, s, steps) ->
          begin match get_free_ae_worker () with
          | Some (i, w) -> process_task i w id s steps
          | None -> ()
          end
      | exception Queue.Empty -> ()

    and init_ae_worker i =
      let worker = Worker.create "alt-ergo-worker.js" in
      let handle_result id result =
        TaskList.print_alt_ergo_output id result;
        let status = match result with
          | Valid -> StValid
          | _ -> StUnknown in
        update_status id status;
        pop_task () in
      worker ##. onmessage :=
        Dom.handler (fun ev ->
            let lb = Lexing.from_string (Js.to_string (ev ##. data)) in
            let result = Json_parser.value (fun x -> Json_lexer.read x) lb in
            let id = Json_base.get_int_field result "worker_id" in
            let result =
              match Json_base.get_field result "status" with
              | Json_base.Record ["Unsat", _] -> Valid
              | Json_base.Record ["Unknown", _] -> Unknown "unknown"
              | Json_base.Record ["Sat", _] -> Unknown "unknown"
              | l -> Unknown (Format.asprintf "%a" Json_base.print_json l) in
            !alt_ergo_workers.(i) <- Free worker;
            handle_result id result;
            Js._false);
      worker ##. onerror :=
        Dom.handler (fun ev ->
            let result = Invalid (Js.to_string (ev ##. message)) in
            begin match !alt_ergo_workers.(i) with
            | Busy (w, id)  ->
                w ## terminate;
                !alt_ergo_workers.(i) <- Absent;
                handle_result id result
            | Free _ ->
                worker ## terminate;
                !alt_ergo_workers.(i) <- Absent
            | Absent -> ()
            end;
            Js._false);
      !alt_ergo_workers.(i) <- Free worker;
      worker

    let reset_workers () =
      Array.iteri (fun i w ->
          match w with
          | Busy (w, id)  ->
              w ## terminate;
              !alt_ergo_workers.(i) <- Absent;
              update_status id StUnknown
          | Absent | Free _ -> ()
        ) !alt_ergo_workers;
      Queue.iter (fun (id, _, _) -> update_status id StUnknown) task_queue;
      Queue.clear task_queue;
      if not !why3_busy then ToolBar.enable_compile ()

    let push_task id s steps =
      match get_free_ae_worker () with
      | Some (i, w) -> process_task i w id s steps
      | None -> Queue.add (id, s, steps) task_queue

    let init_why3_worker () =
      ToolBar.disable_toolbar ();
      let worker = Worker.create "why3_worker.js" in
      worker ##. onmessage :=
        Dom.handler (fun ev ->
            let msg = unmarshal (ev ##. data) in
            if !first_task then begin
                first_task := false;
                TaskList.clear ()
              end;
            handle_why3_message msg;
            let () =
              match msg with
              | Task (id, _, _, code, _, _, steps) ->
                  push_task id code steps
              | Idle ->
                  why3_busy := false;
                  if is_idle () then ToolBar.enable_toolbar ()
              | _ -> () in
            Js._false);
      worker

    let () =
      let worker = init_why3_worker () in
      worker ## postMessage (marshal GetFormats);
      why3_worker := Some worker

    let why3_parse steps =
      Tabs.focus "why3-task-list-tab";
      ToolBar.disable_compile ();
      why3_busy := true;
      TaskList.clear ();
      TaskList.print_msg "<span class='fas fa-cog fa-spin'></span> Generating tasks … ";
      reset_workers ();
      first_task := true;
      let code = Js.to_string (Editor.get_value ()) in
      let format = !FormatList.selected_format in
      let msg = marshal (ParseBuffer (format, code, steps)) in
      (get_why3_worker ()) ## postMessage msg

    let why3_execute () =
      Tabs.focus "why3-task-list-tab";
      ToolBar.disable_compile ();
      why3_busy := true;
      TaskList.clear ();
      TaskList.print_msg "<span class='fas fa-cog fa-spin'></span> Compiling buffer … ";
      reset_workers ();
      let code = Js.to_string (Editor.get_value ()) in
      let format = !FormatList.selected_format in
      let msg = marshal (ExecuteBuffer (format, code)) in
      (get_why3_worker ()) ## postMessage msg

    let why3_transform tr f () =
      if is_idle () then
        begin
          why3_busy := true;
          ToolBar.disable_compile ();
          Hashtbl.iter (fun id _ ->
              f id;
              (get_why3_worker()) ## postMessage (marshal (Transform(tr, id))))
            TaskList.task_selection;
          TaskList.clear_task_selection ()
        end

    let stop () =
      if not (alt_ergo_idle ()) then
        reset_workers ()
      else if not (is_idle ()) then
        begin
          (get_why3_worker ()) ## terminate;
          why3_worker := Some (init_why3_worker ());
          reset_workers ();
          TaskList.clear ();
          ToolBar.enable_compile ()
        end

    let why3_custom_transform tr f () =
      if Hashtbl.length TaskList.task_selection > 0 then
        why3_transform tr f ()

end

(* Initialisation *)
let () =

  ToolBar.add_action Buttons.button_open ToolBar.open_;
  KeyBinding.add_global ~ctrl:Js._true 79 ToolBar.open_;

  ToolBar.add_action Buttons.button_save ToolBar.save;
  KeyBinding.add_global ~ctrl:Js._true 83 ToolBar.save;

  ToolBar.add_action Buttons.button_export ToolBar.export;

  ToolBar.add_action Buttons.button_undo Editor.undo;
  KeyBinding.add_global ~ctrl:Js._true 90 Editor.undo;

  ToolBar.add_action Buttons.button_redo Editor.redo;
  KeyBinding.add_global ~ctrl:Js._true ~shift:Js._true 90 Editor.redo;
  KeyBinding.add_global ~ctrl:Js._true 89 Editor.redo;

  ToolBar.add_action Buttons.button_execute Controller.why3_execute;
  KeyBinding.add_global ~alt:Js._true 69 Controller.why3_execute;

  ToolBar.add_action Buttons.button_compile (fun () ->
      Controller.(why3_parse !alt_ergo_min_steps));
  KeyBinding.add_global ~alt:Js._true 82 (fun () ->
      Controller.(why3_parse !alt_ergo_min_steps));

  ToolBar.add_action Buttons.button_stop Controller.stop;
  KeyBinding.add_global ~alt:Js._true 73 Controller.stop;

  KeyBinding.add_global ~alt:Js._true 32 (fun () ->
      Controller.(why3_custom_transform (Split !alt_ergo_min_steps)) ignore ());

  ToolBar.add_action Buttons.button_settings Dialogs.(show setting_dialog);
  ToolBar.add_action Buttons.button_help (fun () ->
      let link_html =
        match !FormatList.selected_format with
        | "micro-C" -> "help_micro-C.html"
        | "python"  -> "help_python.html"
        | _         -> "help_whyml.html"
      in
      Dom_html.window ## open_ !!link_html !!"_blank" Js.null
    );

  ToolBar.add_action Buttons.button_about Dialogs.(show about_dialog);

  ContextMenu.(add_action split_menu_entry) (fun () ->
      Controller.(why3_transform (Split !alt_ergo_min_steps)) ignore ());
  ContextMenu.(add_action prove_menu_entry) (fun () ->
      Controller.(why3_transform (Prove !alt_ergo_default_steps)) ignore ());

  for i = 0 to 2 do
    ContextMenu.(add_action prove_menu_entries.(i)) (fun () ->
        Controller.why3_transform (Prove (ContextMenu.get_context_step i)) ignore ());
  done;

  ContextMenu.(add_action clean_menu_entry)
    (fun () -> Controller.why3_transform Clean TaskList.clean_task ());

  Dialogs.(set_onchange input_num_threads) (fun o ->
      let open Controller in
      let len = int_of_js_string (o ##. value) in
      reset_workers ();
      alt_ergo_workers := Array.make len Absent);

  Dialogs.(set_onchange input_num_steps) (fun o ->
      let steps = int_of_js_string (o ##. value) in
      Controller.alt_ergo_default_steps := steps;
      Controller.reset_workers ());

  Dialogs.(set_onchange input_min_steps) (fun o ->
      let steps = int_of_js_string (o ##. value) in
      Controller.alt_ergo_min_steps := steps;
      Controller.reset_workers ());

  for i = 0 to 2 do
    Dialogs.(set_onchange input_context_steps.(i)) (fun o ->
        let steps = int_of_js_string (o ##. value) in
        ContextMenu.alt_ergo_context_steps.(i) <- steps;
        ContextMenu.change_prove_context ();
        Controller.reset_workers ())
  done;


  ToolBar.add_action Dialogs.button_close Dialogs.close;
  (*KeyBinding.add_global Keycode.esc  Dialogs.close;*)

  Dialogs.(set_onchange radio_wide) (fun _ -> Panel.set_wide true);
  Dialogs.(set_onchange radio_column) (fun _ -> Panel.set_wide false);

  FormatList.(set_onchange select_format) ExampleList.update

let () =
  let url = new%js Url._URL (Dom_html.window ##. location ##. href) in
  let search = url ##. searchParams in
  let () =
    match Js.Opt.to_option (search ## get !!"name") with
    | Some name -> Editor.name := name
    | None -> ()
  in
  let lang, buffer =
    match Js.Opt.to_option (search ## get !!"code") with
    | Some code ->
        let code =
          try Shortener.decode (Js.to_string code)
          with Invalid_argument _ -> "Invalid 'code' fragment in the URL" in
        search ## delete !!"code";
        Dom_html.window ##. history ## replaceState Js.null !!"" (Js.some (url ##. href));
        ("", Js.string code)
    | None ->
        (* restore the session *)
        let lang, name, buffer = Session.load_buffer () in
        Editor.name := name;
        let lang = if lang ##. length == 0 then name else lang in
        (Js.to_string lang, buffer) in
  let lang =
    match Js.Opt.to_option (search ## get !!"lang") with
    | Some lang -> Js.to_string lang
    | None -> lang in

  FormatList.change_mode lang;
  FormatList.selected_format := lang; (* formats not yet loaded *)
  Editor.set_value ~active_callback:false buffer;
  Editor.editor ## getSession ## getUndoManager ## reset;
  Editor.update_undo ();
  Editor.editor ## focus;
  Panel.set_wide (Session.load_view_mode () = !!"wide");
  ExampleList.unselect();
  Dom_html.window ##. onunload :=
    Dom.handler (fun _ ->
        Session.save_buffer (Js.string !FormatList.selected_format)
          !Editor.name (Editor.get_value ());
        Session.save_view_mode (if Panel.is_wide () then !!"wide"
                                else !!"column");
        Session.save ();
        Js._true)

let () =
  let load_config s =
    let lb = Lexing.from_string s in
    ExampleList.config := Json_parser.value (fun x -> Json_lexer.read x) lb;
    ExampleList.update ()
  in

  Promise.catch
    (Promise.bind_unit
      (Promise.bind (Fetch.fetch !!"examples/config.json")
          (fun r -> r ## text))
      (fun s -> load_config (Js.to_string s)))
    (fun _ -> ());

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. trywhy3"
End:
*)
