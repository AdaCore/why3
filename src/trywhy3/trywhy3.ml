


let examples =
  [ "Drinkers paradox","
theory T

   (** Type of all persons *)
   type person

   (** Predicate saying that some person drinks *)
   predicate drinks person

   (** Paradox: there exists a person x such that if x drinks,
       then everybody drinks *)
   goal drinkers_paradox: exists x:person. drinks x -> forall y:person. drinks y

end
";
   "Simple Arithmetic","
theory T

   use import int.Int

   goal g: exists x:int. x*(x+1) = 42

end
";
  ]

(** registering the std lib *)

let () =
  List.iter
    (fun (name,content) ->
      Sys_js.register_file ~name ~content;
    ) Theories.theories

(** Rendering in the browser *)

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

let () =
  Sys_js.register_file ~name:temp_file_name ~content:"";

open Why3

(* TODO: loading from standard library.

   piste: utiliser Sys_js.register_autoload et
   XmlHttpRequest.get

*)
let env = Env.create_env ["/theories" (*; "/modules"*)]

(*
let bad_suffix path name =
  match path with
  | "/theories" -> not (Filename.check_suffix name ".why")
  | "/modules" -> not (Filename.check_suffix name ".mlw")
  | _ -> true

let load_file_from_the_web (path,name) =
  if bad_suffix path name then None else
  let t = XmlHttpRequest.get
    ("http://why3.lri.fr/try" ^ path ^ "/" ^ name)
  in
  let c = ref "" in
  Lwt.on_success t
    (fun frame ->
      let content = frame. XmlHttpRequest.content in
      (* useless ?
         Sys_js.register_file ~name:(path ^ "/" ^ name) ~content; *)
      c := content);
  Some !c

let () = Sys_js.register_autoload ~path:"/theories" load_file_from_the_web
*)

let run textbox preview (_ : D.mouseEvent Js.t) : bool Js.t =
  let text = Js.to_string (textbox##value) in
  let ch = open_out temp_file_name in
  output_string ch text;
  close_out ch;
  let answer =
    try
      let x = Env.read_file Env.base_language env temp_file_name in
      Pp.sprintf "parsing and typing OK, %d theories"
        (Stdlib.Mstr.cardinal x)
    with
    | Loc.Located(loc,Parser.Error) ->
      let (_,l,b,e) = Loc.get loc in
      Pp.sprintf "syntax error line %d, columns %d-%d" l b e
    | Loc.Located(loc,e') ->
      let (_,l,b,e) = Loc.get loc in
      Pp.sprintf
        "error line %d, columns %d-%d: %a" l b e Exn_printer.exn_printer e'
    | e ->
      Pp.sprintf
        "unexpected exception: %a (%s)" Exn_printer.exn_printer e
        (Printexc.to_string e)
  in
  replace_child preview (html_of_string answer);
  Js._false

let onload (_event : #Dom_html.event Js.t) : bool Js.t =
  let body =
    Js.Opt.get (d##getElementById(Js.string "trywhy3"))
      (fun () -> assert false) in
  (* first, the textbox *)
  let textbox = D.createTextarea d in
  textbox##rows <- 20; textbox##cols <- 100;
  Dom.appendChild body textbox;
  Dom.appendChild body (D.createBr d);
  (* second, the example buttons *)
  List.iter
    (fun (name,text) ->
      let b = D.createButton ~name:(Js.string name) d in
      b##textContent <- Js.some (Js.string name);
      Dom.appendChild body b;
      b##onclick <-
        D.handler
        (fun (_ : D.mouseEvent Js.t) ->
          textbox##textContent <- Js.some (Js.string text);
          Js._false))
    examples;
  Dom.appendChild body (D.createBr d);
  (* third, the go button *)
  let go = D.createButton ~name:(Js.string "go") d in
  go##textContent <- Js.some (Js.string "Go");
  Dom.appendChild body go;
  Dom.appendChild body (D.createBr d);
  (* then, the answer zone *)
  let preview = D.createDiv d in
  go##onclick <- D.handler (run textbox preview);
  preview##style##border <- Js.string "1px black";
  preview##style##padding <- Js.string "5px";
  Dom.appendChild body preview;
  Js._false

let _ = D.window##onload <- D.handler onload
