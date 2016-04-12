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

let get_opt o = Js.Opt.get o (fun () -> assert false)


(* the view *)
module Console =
  struct
    let highlightRegion s l1 c1 l2 c2 =
      ignore (Js.Unsafe.meth_call Js.Unsafe.global
                                  "highlightRegion"
                                  Js.Unsafe.( [| inject (Js.string s);
                                                inject l1;
                                                inject c1;
                                                inject l2;
                                                inject c2 |] ) )

    let clearHighlight ()=
      ignore (Js.Unsafe.meth_call Js.Unsafe.global
                                  "clearHighlight" [| |])
    let get_buffer () =
      let global = Js.Unsafe.global in
      let editor = Js.Unsafe.get global (Js.string "editor") in
      Js.to_string (Js.Unsafe.meth_call editor "getValue" [| |])

    let get_console () =
        get_opt (Dom_html.document ## getElementById (Js.string "console"))

    let clear () =
      (get_console ()) ## innerHTML <- (Js.string "")

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
        Valid -> ()
      | Unknown msg -> span_msg ## innerHTML <- (Js.string (" (" ^ msg ^ ")"))
      | Invalid msg -> span_msg ## innerHTML <- (Js.string (" (" ^ msg ^ ")"))

    let appendChild o c =
      ignore (o ## appendChild ( (c :> Dom.node Js.t)))

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
        let span_icon = Dom_html.createSpan doc in
        appendChild li span_icon;
        span_icon ## id <- Js.string (id ^ "_icon");
        appendChild li (doc ## createTextNode (Js.string (" " ^ expl ^ " ")));
        let span_msg = Dom_html.createSpan doc in
        span_msg ## id <- Js.string (id ^ "_msg");
        appendChild li span_msg;
        let tul = Dom_html.createUl doc in
        tul ## id <- Js.string (id ^ "_ul");
        appendChild li tul


    let print_why3_output o =
      let doc = Dom_html.document in
      (* see why3_worker.ml *)
      match o with
        Error s -> print_error s

      | ErrorLoc ((l1, b, l2, e), s) ->
         ignore (Js.Unsafe.meth_call Js.Unsafe.global
                                     "highlightError"
                                     (Array.map Js.Unsafe.inject [| l1; b; l2; e |]));
         print_error s
      | Result sl ->
         clear ();
         let ul = Dom_html.createUl doc in
         appendChild (get_console()) ul;
         List.iter (fun (s : string) ->
                    let li = Dom_html.createLi doc in
                    li ## innerHTML <- (Js.string s);
                    appendChild ul li;) sl

      | Theory (th_id, th_name) -> attach_to_parent th_id "theory-list" th_name []
      | Task (id, parent_id, expl, _code, loc) ->
         attach_to_parent id parent_id expl loc
      | UpdateStatus(st, id) ->
         try
           let span_icon = Dom_html.getElementById (id ^ "_icon") in
           let cls =
             match st with
               `New -> "fontawesome-cogs task-pending"
             | `Valid -> "fontawesome-ok-sign task-valid"
             | `Unknown -> "fontawesome-question-sign task-unknown"
           in
           span_icon ## className <- Js.string cls
         with
           Not_found -> ()

    let set_abort_icon () =
      let list = Dom_html.document ## getElementsByClassName (Js.string "task-pending") in
      List.iter (fun span ->
                 span ## className <- (Js.string "fontawesome-minus-sign task-abort"))
                (Dom.list_of_nodeList list)

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
                  (get_why3_worker()) ## postMessage (marshal (status_of_result res));
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
                      Task (id,_,_,code,_) -> push_task (Goal (id,code))
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
  let code = Console.get_buffer () in
  let msg = marshal (ParseBuffer code) in
  log_time "After marshalling in main thread";
  (get_why3_worker()) ## postMessage (msg)

let why3_execute () =
  Console.clear ();
  Console.print_msg "Compiling buffer … ";
  log_time "Before marshalling in main thread";
  reset_workers ();
  let code = Console.get_buffer () in
   (get_why3_worker()) ## postMessage (marshal (ExecuteBuffer code))


let () =
  add_button "prove" why3_parse ;
  add_button "run" why3_execute ;
  add_button "stop" (fun () ->
                     (get_why3_worker()) ## terminate ();
                     why3_worker := Some (init_why3_worker ());
                     reset_workers ();
                     Console.set_abort_icon());

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


(* Predefined examples *)

let add_file_example (buttonname, file) =
  let handler = Dom.handler
    (fun _ev ->
      let text = Sys_js.file_content file in
      let global = Js.Unsafe.global in
      let editor = Js.Unsafe.get global (Js.string "editor") in
      Js.Unsafe.set global (Js.string "loadedBuffer") (Js.string text);
      let loaded = Filename.basename file in
      Js.Unsafe.set global (Js.string "loadedFilename") (Js.string loaded);
      ignore (Js.Unsafe.meth_call global "replaceWithLoaded" [| |]);
      ignore (Js.Unsafe.meth_call editor "focus" [| |]);
      Js._false)
  in
  let button =
    get_opt (Dom_html.document ## getElementById (Js.string buttonname))
  in
  button ## onclick <- handler

let () =
  let files =
    [
      "drinkers", "/drinkers.why";
(*  add_file_example "simplearith" "/simplearith.why";*)
      "bin_mult", "/bin_mult.mlw";
      "fact", "/fact.mlw";
      "isqrt", "/isqrt.mlw"
    ]
  in
  List.iter add_file_example files;


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. trywhy3"
End:
*)
