

(* computation part  *)

let compute_result text =
  try
    let a,b = Scanf.sscanf text "%d %d" (fun x y -> x,y) in
    string_of_int (Gcd__EuclideanAlgorithm31.euclid a b)
  with _ -> "exception"



(* HTML rendering *)

module Html = Dom_html

let node x = (x : #Dom.node Js.t :> Dom.node Js.t)

let (<|) e l = List.iter (fun c -> Dom.appendChild e c) l; node e

let html_of_string (d : Html.document Js.t) (s:string) =
  d##createElement (Js.string "p") <|
      [node (d##createTextNode (Js.string s))]

let replace_child p n =
  Js.Opt.iter (p##firstChild) (fun c -> Dom.removeChild p c);
  Dom.appendChild p n

let onload (_event : #Html.event Js.t) : bool Js.t =
  let d = Html.document in
  let body =
    Js.Opt.get (d##getElementById(Js.string "test"))
      (fun () -> assert false) in
  let textbox = Html.createTextarea d in
  textbox##rows <- 20; textbox##cols <- 100;
  let preview = Html.createDiv d in
  preview##style##border <- Js.string "1px black";
  preview##style##padding <- Js.string "5px";
  Dom.appendChild body textbox;
  Dom.appendChild body (Html.createBr d);
  Dom.appendChild body preview;
  let rec dyn_preview old_text n =
    let text = Js.to_string (textbox##value) in
    let n =
      if text <> old_text then
        begin
          begin try
                  let rendered =
                    html_of_string d (compute_result text)
                  in
                  replace_child preview rendered
            with _ -> ()
          end;
          20
        end
      else
        max 0 (n - 1)
    in
    Lwt.bind
      (Lwt_js.sleep (if n = 0 then 0.5 else 0.1))
      (fun () -> dyn_preview text n)
  in
  let (_ : 'a Lwt.t) = dyn_preview "" 0 in Js._false

let (_ : unit) = Html.window##onload <- Html.handler onload
