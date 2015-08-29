
module D = Dom_html

let d = D.document

let node x = (x : #Dom.node Js.t :> Dom.node Js.t)

let (<|) e l = List.iter (fun c -> Dom.appendChild e c) l; node e

let html_of_string (s:string) =
  d##createElement (Js.string "p") <|
      [node (d##createTextNode (Js.string s))]

let replace_child p n =
  Js.Opt.iter (p##firstChild) (fun c -> Dom.removeChild p c);
  Dom.appendChild p n

let temp_file_name = "/input.mlw"

open Why3

let run textbox preview _ =
  let text = Js.to_string (textbox##value) in
  Sys_js.register_file ~name:temp_file_name ~content:text;
  let env = Env.create_env [] in
  let answer =
    try
      let _x = Env.read_file Env.base_language env temp_file_name in
      "parsing OK"
    with e ->
      Pp.sprintf
        "exception raised in parsing: %a" Exn_printer.exn_printer e
  in
  replace_child preview (html_of_string answer);
  Js._false

let onload (_event : #Dom_html.event Js.t) : bool Js.t =
  let body =
    Js.Opt.get (d##getElementById(Js.string "trywhy3"))
      (fun () -> assert false) in
  let textbox = D.createTextarea d in
  textbox##rows <- 20; textbox##cols <- 100;
  let go = D.createButton ~name:(Js.string "go") d in
  go##textContent <- Js.some (Js.string "Go");
  let preview = D.createDiv d in
  preview##style##border <- Js.string "1px black";
  preview##style##padding <- Js.string "5px";
  Dom.appendChild body textbox;
  Dom.appendChild body (D.createBr d);
  Dom.appendChild body go;
  Dom.appendChild body (D.createBr d);
  Dom.appendChild body preview;
  replace_child preview (html_of_string "(Answer)");
  go##onclick <- D.handler (run textbox preview);
  Js._false

let _ = D.window##onload <- D.handler onload
