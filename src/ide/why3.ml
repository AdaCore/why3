

module JSU = Js.Unsafe

let log s = ignore (Firebug.console ## log (Js.string s))

let get_opt o = Js.Opt.get o (fun () -> assert false)

let check_def s o =
  Js.Optdef.get o (fun () -> log ("Object " ^ s ^ " is undefined or null");
			     assert false)

let get_global ident =
  let res : 'a Js.optdef = JSU.(get global) (Js.string ident) in
  check_def ident res



(**********)

module AsHtml =
  struct
    include Dom_html.CoerceTo
    let span e = element e
  end

let getElement_exn cast id =
  Js.Opt.get (cast (Dom_html.getElementById id)) (fun () -> raise Not_found)

let getElement cast id =
  try
    getElement_exn cast id
  with
    Not_found ->
    log ("Element " ^ id ^ " does not exist or has invalid type");
    assert false

(**********)


(*
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
          task_menu ## style ## display <- Js.string "block";
          task_menu ## style ## left <- Js.string ((string_of_int x) ^ "px");
          task_menu ## style ## top <- Js.string ((string_of_int y) ^ "px")
        end
    let hide () =
      if !enabled then
        task_menu ## style ## display <- Js.string "none"

    let add_action b f =
      b ## onclick <- Dom.handler (fun _ ->
				   hide ();
				   f ();
				   Editor.(focus editor);
				   Js._false)

    let () = addMouseEventListener false task_menu "mouseleave"
	(fun _ -> hide())

  end
 *)


module Editor =
  struct
(* not used yet
    type range
    type marker
    let name = ref (Js.string "")
    let saved = ref false
 *)
    let ace = get_global "ace"

(* don't know what it is for
    let _Range : (int -> int -> int -> int -> range Js.t) Js.constr =
      let r =
	JSU.(get (meth_call ace "require" [| inject (Js.string "ace/range") |])
		 (Js.string "Range"))
      in
      check_def "Range" r
 *)

    (* activate/show the editor in the interface *)
    let editor =
      let e =
	JSU.(meth_call ace "edit" [| inject (Js.string "why3-editor") |])
      in
      check_def "why3-editor" e

    (* activate/show the task-viewer in the interface *)
    let task_viewer =
      let e =
	JSU.(meth_call ace "edit" [| inject (Js.string "why3-task-viewer") |])
      in
      check_def "why3-task-viewer" e

end


module ToolBar =
  struct
    let button_open = getElement AsHtml.button "why3-button-open"

    let add_action b f =
      let cb = fun _ ->
	f ();
(*
	Editor.(focus editor);
 *)
	Js._false
      in
      b ## onclick <- Dom.handler cb

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

end

let open_session () =
  TaskList.print_msg "Vous avez clique sur .."

let () =
  ToolBar.(add_action button_open open_session);
