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
module XHR = XmlHttpRequest

let get_opt o = Js.Opt.get o (fun () -> assert false)


(* the view *)
module Editor =
  struct
    type range
    type marker

    let editor =
      let open Js.Unsafe in
      get global (Js.string "editor")
    let task_editor =
      let open Js.Unsafe in
      get global (Js.string "task_editor")

    let get_value ?(editor=editor) () : Js.js_string Js.t =
      let open Js.Unsafe in
      meth_call editor "getValue" [| |]

    let set_value ?(editor=editor) (str : Js.js_string Js.t) =
      let open Js.Unsafe in
      ignore (meth_call editor "setValue" [| inject (str); inject ~-1 |])


    let get_buffer () =
      Js.to_string (get_value ())

    let mk_range l1 c1 l2 c2 =
      let open Js.Unsafe in
      let range : (int -> int -> int -> int -> range Js.t) Js.constr =
        get global (Js.string "Range")
      in
      jsnew range (l1, c1, l2, c2)

    let set_selection_range r =
      let open Js.Unsafe in
      let selection = meth_call editor "getSelection" [| |] in
      ignore (meth_call selection "setSelectionRange" [| inject r |])

    let add_marker cls r : marker =
      let open Js.Unsafe in
      let session = meth_call editor "getSession" [| |] in
      meth_call session "addMarker"
                                 [| inject r;
                                    inject (Js.string cls);
                                    inject (Js.string "text") |]

    let remove_marker m =
      let open Js.Unsafe in
      let session = meth_call editor "getSession" [| |] in
      ignore (meth_call session "removeMarker" [| inject  m|])

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

    let set_on_event e f =
      let open Js.Unsafe in
      ignore (meth_call editor "on" [| inject (Js.string e);
                                       inject f|])
  end

module Console =
  struct


    let tabs =
      let headers = Dom_html.document ## getElementsByClassName (Js.string "tab-header") in
      List.fold_left (fun acc t ->
                      let tab_id = t ## id in
                      let i = tab_id ## lastIndexOf (Js.string "-tab") in
                      let len = tab_id ## length in
                      if i == len - 4 then
                        try
                          let tab = Dom_html.getElementById (Js.to_string (tab_id ## substring(0,i))) in
                          (t, tab) :: acc
                        with
                          Not_found -> acc
                      else acc
                     )
                     [] (Dom.list_of_nodeList headers)
    let () =
      List.iter (fun (th, tb) ->
                 let cb = fun idh idb _ ->
                   List.iter (fun (h,b) ->
                              if Js.to_string (h ## id) = idh &&
                                   Js.to_string (b ## id) = idb
                              then begin
                                  h ## classList ## add (Js.string "active");
                                  b ## classList ## add (Js.string "active");
                                end
                              else begin
                                  h ## classList ## remove (Js.string "active");
                                  b ## classList ## remove (Js.string "active");
                                end;
                             ) tabs;
                   th ## classList ## remove (Js.string "alert");
                   Js._false

                 in
                 th ## onclick <- Dom.handler (cb (Js.to_string th ## id) (Js.to_string tb ## id)))
                tabs


    let get_console () =
        get_opt (Dom_html.document ## getElementById (Js.string "console"))


    let print cls msg =
        (get_console ()) ## innerHTML <-
          (Js.string ("<p class='" ^ cls ^ "'>" ^
                        msg ^ "</p>"))

    let print_error = print "error"

    let print_msg = print "msg"

    let node_to_html n =
      Dom_html.element (get_opt (Dom.CoerceTo.element (get_opt n)))

    let print_alt_ergo_output id res =
      (* see alt_ergo_worker.ml and the Tasks case in print_why3_output *)
      let span_msg = Dom_html.getElementById (id ^ "_msg") in
      match res with
        Valid -> span_msg ## innerHTML <- Js.string ""
      | Unknown msg -> span_msg ## innerHTML <- (Js.string (" (" ^ msg ^ ")"))
      | Invalid msg -> span_msg ## innerHTML <- (Js.string (" (" ^ msg ^ ")"))

    let appendChild o c =
      ignore (o ## appendChild ( (c :> Dom.node Js.t)))

    let mk_li_content id expl =
      Js.string (Format.sprintf
		   "<span id='%s_container'><span id='%s_icon'></span> %s <span id='%s_msg'></span></span><ul id='%s_ul'></ul>"
		   id id expl id id)

    let clean_task id =
      try
	let ul = Dom_html.getElementById (id ^ "_ul") in
	ul ## innerHTML <- Js.string ""
      with
	Not_found -> ()

    let attach_to_parent id parent_id expl _loc =
      let doc = Dom_html.document in
      let ul =
        try
          Dom_html.getElementById parent_id
        with
          Not_found ->
          let ul = Dom_html.createUl doc in
          ul ## id <- Js.string parent_id;
          appendChild (get_console()) ul;
          ul
      in
      try
        ignore (Dom_html.getElementById id);
        log ("li element " ^ id ^ " already exists !")
      with
        Not_found ->
        let li = Dom_html.createLi doc in
        li ## id <- Js.string id;
        appendChild ul li;
	li ## innerHTML <- mk_li_content id expl


    let task_selection = Hashtbl.create 17
    let is_selected id = Hashtbl.mem task_selection id
    let select_task id span loc pretty =
      (span ## classList) ## add (Js.string "task-selected");
      let markers = List.map (fun (cls, range) -> Editor.add_marker cls range) loc in
      Hashtbl.add task_selection id (span, loc, markers);
      Editor.set_value ~editor:Editor.task_editor (Js.string pretty)

    let deselect_task id =
      try
        let span, loc, markers = Hashtbl.find task_selection id in
        (span ## classList) ## remove (Js.string "task-selected");
        List.iter Editor.remove_marker markers;
        Hashtbl.remove task_selection id
      with
        Not_found -> ()

    let clear_task_selection () =
      let l = Hashtbl.fold (fun id _ acc -> id :: acc) task_selection [] in
      List.iter deselect_task l



    let clear () =
      clear_task_selection ();
      (get_console ()) ## innerHTML <- Js.string "";
      Editor.set_value ~editor:Editor.task_editor (Js.string "")

    let error_marker = ref None
    let () =
      Editor.set_on_event
        "change"
        (Js.wrap_callback (fun () -> clear ();
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
         error_marker := Some (Editor.add_marker "error" r, r);
         print_error s

      | Result sl ->
         clear ();
         let ul = Dom_html.createUl doc in
         appendChild (get_console()) ul;
         List.iter (fun (s : string) ->
                    let li = Dom_html.createLi doc in
                    li ## innerHTML <- (Js.string s);
                    appendChild ul li;) sl

      | Theory (th_id, th_name) ->
	 attach_to_parent th_id "theory-list" th_name []

      | Task (id, parent_id, expl, _code, locs, pretty) ->
	 begin
	   try
	     ignore (Dom_html.getElementById id)
	   with Not_found ->
		attach_to_parent id (parent_id ^ "_ul") expl locs;
		let span = Dom_html.getElementById (id ^ "_container") in
                let buffer = Editor.get_value () in
                let locs = List.map (fun (k, loc) -> k, Editor.why3_loc_to_range buffer loc) locs in
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
		     Js._false)
	 end



      | UpdateStatus(st, id) ->
         try
           let span_icon = Dom_html.getElementById (id ^ "_icon") in
           let cls =
             match st with
               `New -> "fa fa-fw fa-cog fa-spin fa-fw task-pending"
             | `Valid -> "fa fa-fw fa-check-circle task-valid"
             | `Unknown -> "fa fa-fw fa-question-circle task-unknown"
           in
           span_icon ## className <- Js.string cls
         with
           Not_found -> ()

    let set_abort_icon () =
      let list = Dom_html.document ## getElementsByClassName (Js.string "task-pending") in
      List.iter (fun span ->
                 span ## className <- (Js.string "fa fa-fw fa-minus-circle task-abort"))
                (Dom.list_of_nodeList list)





    let select_example =
      match Dom_html.tagged (Dom_html.getElementById "select-example") with
	Dom_html.Select s -> s
      | _ -> assert false


    let set_loading_label b =
      let label = Dom_html.getElementById "example-label" in
      select_example ## disabled <- (Js.bool b);
      if b then
	label ## className <- Js.string "fa fa-spin fa-refresh"
      else
	label ## className <- Js.string "fa-book"

    let () =
      let sessionStorage : Dom_html.storage Js.t =
	let open Js.Unsafe in
	get global (Js.string "sessionStorage")
      in
      select_example ## onchange <-
	Dom.handler (fun _ ->
		     let url = select_example ## value in
		     begin
		       match Js.Opt.to_option (sessionStorage ## getItem (url)) with
			 Some s -> Editor.set_value s
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

let add_button buttonname f =
  let handler =
    Dom.handler
      (fun _ev ->
       f ();
       let global = Js.Unsafe.global in
       let editor = Js.Unsafe.get global (Js.string "editor") in
       ignore (Js.Unsafe.meth_call editor "focus" [| |]);
       Js._false)
  in
  let button =
    get_opt (Dom_html.document ## getElementById (Js.string buttonname))
  in
  button ## onclick <- handler


let task_queue  = Queue.create ()
let first_task = ref true
type 'a status = Free of 'a | Busy of 'a | Absent
let num_workers = 4
let alt_ergo_steps = ref 100
let alt_ergo_workers = ref (Array.make num_workers Absent)
let why3_worker = ref None
let get_why3_worker () =
  match !why3_worker with
    Some w -> w
  | None -> log ("Why3 Worker not initialized !"); assert false

let rec init_alt_ergo_worker i =
  let worker = Worker.create "alt_ergo_worker.js" in
  worker ## onmessage <-
    (Dom.handler (fun ev ->
                  let (id, result) as res = unmarshal (ev ## data) in
                  Console.print_alt_ergo_output id result;
		  let status_update = status_of_result res in
		  let () = match status_update with
		      SetStatus(v, id) ->
		      Console.print_why3_output (UpdateStatus(v, id))
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
  | _ -> ()

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
                      Console.clear ()
                    end;
                  Console.print_why3_output msg;
                  let () =
                    match msg with
                      Task (id,_,_,code,_,_) ->
		      log ("Got task " ^ id);
		      push_task (Goal (id,code))
                    | _ -> ()
                  in Js._false));
  worker

let () = why3_worker := Some (init_why3_worker ())

let why3_parse () =
  Console.clear ();
  Console.print_msg "Sending buffer to Alt-Ergo … ";
  log_time "Before marshalling in main thread";
  reset_workers ();
  first_task := true;
  let code = Editor.get_buffer () in
  let msg = marshal (ParseBuffer code) in
  log_time "After marshalling in main thread";
  (get_why3_worker()) ## postMessage (msg)

let why3_execute () =
  Console.clear ();
  Console.print_msg "Compiling buffer … ";
  log_time "Before marshalling in main thread";
  reset_workers ();
  let code = Editor.get_buffer () in
   (get_why3_worker()) ## postMessage (marshal (ExecuteBuffer code))

let array_for_all a f =
  let rec loop i n =
    if i < n then (f a.(i)) && loop (i+1) n
    else true
  in
  loop 0 (Array.length a)

let alt_ergo_not_running () =
  array_for_all !alt_ergo_workers (function Busy _ -> false | _ -> true)

let why3_transform tr f () =
  if alt_ergo_not_running () then
    begin
      Hashtbl.iter
        (fun id _ ->
	 f id;
	 (get_why3_worker()) ## postMessage (marshal (Transform(tr, id))))
	Console.task_selection;
      Console.clear_task_selection ()
    end

let why3_prove_all () =
  if alt_ergo_not_running () then
    (get_why3_worker()) ## postMessage (marshal ProveAll)


let () =
  add_button "button-execute" why3_execute ;
  add_button "button-compile" why3_parse ; (* todo : change *)
  add_button "button-prove-all" why3_prove_all;
  add_button "button-prove" (why3_transform `Prove (fun _ -> ()));
  add_button "button-split" (why3_transform `Split (fun _ -> ()));
  add_button "button-clean" (why3_transform `Clean Console.clean_task);
  add_button "button-stop" (fun () ->
			    (get_why3_worker()) ## terminate ();
			    why3_worker := Some (init_why3_worker ());
			    reset_workers ();
			    Console.clear());

  let input_threads = get_opt Dom_html.(CoerceTo.input
					  (getElementById "input-num-threads"))
  in
  input_threads ## oninput <-
    Dom.handler
      (fun ev ->
       let len = int_of_string (Js.to_string (input_threads ## value)) in
       Array.iter (function Busy (w) | Free (w) -> w ## terminate () | _ -> ())
		  !alt_ergo_workers;
       log (string_of_int len);
       alt_ergo_workers := Array.make len Absent;
       Console.set_abort_icon();
       Js._false
      );

  let input_steps = get_opt Dom_html.(CoerceTo.input
					  (getElementById "input-num-steps"))
  in
  input_steps ## oninput <-
    Dom.handler
      (fun ev ->
       let steps = int_of_string (Js.to_string (input_steps ## value)) in
       log(string_of_int steps);
       alt_ergo_steps := steps;
       reset_workers ();
       Console.set_abort_icon();
       Js._false
      )

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
	     Console.add_example examples.(2*i) ((Js.string "examples/") ## concat (examples.(2*i+1)))
	   done;
	   Console.set_loading_label false
	 else
	   Console.set_loading_label false
      );
  xhr ## _open (Js.string "GET", Js.string "examples/index.txt", Js._true);
  xhr ## send (Js.null);
  Console.set_loading_label true

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. trywhy3"
End:
*)
