open Why3
open Itp_communication

let printAnswer s =
  let doc = Dom_html.document in
  let node = doc##createElement (Js.string "P") in
  let textnode = doc##createTextNode (Js.string s) in
  Dom.appendChild node textnode;
  let answers = doc ## getElementById (Js.string "answers") in
  let opt_answers = Js.Opt.to_option answers in
  match opt_answers with
  | None -> ()
  | Some answers ->
      Dom.appendChild answers node

let readBody (xhr: XmlHttpRequest.xmlHttpRequest Js.t) =
  let data = ref None in
  let resType = xhr ## responseType in
  printAnswer (Js.to_string resType);
  data := Some (xhr ## responseText);
  match !data with
  | None -> raise Not_found
  | Some data -> printAnswer (Js.to_string data); Js.to_string data

(* TEMPORAZRY TODO s todo *)
exception TODO1
exception TODO2

let interpNotif (n: notification) =
  let doc = Dom_html.document in
  match n with
  | Initialized g ->
      printAnswer ("Initialized")
  | New_node (nid, parent, ntype, name, detached) ->
      let pid = ref "session" in
      (if (nid != parent) then
        pid := "nid" ^ string_of_int parent
      else
        let ses = doc ## getElementById (Js.string !pid) in
        match (Js.Opt.to_option ses) with
        | None -> raise TODO1
        | Some ses ->
            (ses ## innerHTML <- (Js.string "")); printAnswer "Node 0 reinitialized everything");
      let parentnode = doc ## getElementById (Js.string !pid) in
      (match (Js.Opt.to_option parentnode) with
      | None -> printAnswer !pid; raise TODO2
      | Some parentnode ->
      let linode = doc ## createElement (Js.string "LI") in
      let text = (Json_util.convert_node_type_string ntype) ^ " " ^ name in
      let textnode = doc##createTextNode (Js.string text) in
      Dom.appendChild linode textnode;
      let ulnode = doc ## createElement (Js.string "UL") in
      ulnode ## setAttribute (Js.string "id",
                              Js.string ("nid" ^ string_of_int nid));
      Dom.appendChild linode ulnode;
      Dom.appendChild parentnode linode;
      printAnswer "new_node") (* TODO *)
  | _ -> printAnswer "Unsupported" (* TODO *)

(*
<div oncontextmenu="javascript:alert('success!');return false;">
    Lorem Ipsum
</div>

el.addEventListener('contextmenu', function(ev) {
    ev.preventDefault();
    alert('success!');
    return false;
}, false);
*)

(* TODO remove this *)
exception NoNotification

let interpNotifications l =
  let rec interpNotifications l =
    match l with
    | [] -> ()
    | hd :: tl -> interpNotif hd; interpNotifications tl
  in
  match l with
  | [] -> raise NoNotification
  | l -> interpNotifications l

let getNotification2 () =
  let xhr = XmlHttpRequest.create () in
  let onreadystatechange () =
    if xhr ## readyState == XmlHttpRequest.DONE then
      if xhr ## status == 200 then
        let r = readBody xhr in
        printAnswer ("r = |" ^ r ^ "|"); (* TODO *)
        let nl = Json_util.parse_list_notification r in
        interpNotifications nl
(* TODO *)
      else
        raise NoNotification
        (* TODO printAnswer ("Erreur" ^ string_of_int xhr##status)*)
  in
  (xhr ## onreadystatechange <-
    (Js.wrap_callback onreadystatechange));
  xhr ## overrideMimeType (Js.string "text/json");
  let _ = xhr ## _open (Js.string "GET",
                Js.string "http://localhost:6789/getNotifications", Js._true) in
  xhr ## send (Js.null)

let sendRequest r =
   let r = Js.to_string r in
   let xhr = XmlHttpRequest.create () in
   let onreadystatechange () =
     if xhr ## readyState == XmlHttpRequest.DONE then
       if xhr ## status == 200 then
         printAnswer (readBody xhr)
       else
         printAnswer ("Erreur " ^ string_of_int (xhr ## status)) in
   xhr ## overrideMimeType (Js.string "text/json");
   let _ = xhr ## _open (Js.string "GET",
                Js.string ("http://localhost:6789/request?"^r), Js._true) in
   xhr ## onreadystatechange <- (Js.wrap_callback onreadystatechange);
   xhr ## send (Js.null)

let notifHandler = ref None

let startNotificationHandler () =
   if (!notifHandler = None) then
     notifHandler := Some (Dom_html.window ## setInterval
                       (Js.wrap_callback getNotification2, Js.float 1000.0))

let stopNotificationHandler () =
   match !notifHandler with
   | None -> ()
   | Some n -> Dom_html.window ## clearInterval (n); notifHandler := None

let () = Js.Unsafe.global##stopNotificationHandler <-
   Js.wrap_callback stopNotificationHandler

let () = Js.Unsafe.global##startNotificationHandler <-
   Js.wrap_callback startNotificationHandler

let () = Js.Unsafe.global##sendRequest <- Js.wrap_callback sendRequest

let () = Js.Unsafe.global##getNotification1 <- Js.wrap_callback getNotification2

let () = Js.Unsafe.global##printAnswer1 <-
  Js.wrap_callback (fun s -> printAnswer s)
