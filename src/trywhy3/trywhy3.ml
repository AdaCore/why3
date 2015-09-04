


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
"Integral square root","
module M

  use import int.Int
  use import ref.Ref

  function sqr (x:int) : int = x * x

  let isqrt (x:int) : int
    requires { x >= 0 }
    ensures { result >= 0 }
    ensures { result <= x < sqr (result + 1) }
  = let count = ref 0 in
    let sum = ref 1 in
    while !sum <= x do
      invariant { !count >= 0 }
      invariant { x >= sqr !count }
      invariant { !sum = sqr (!count+1) }
      variant   { x - !count }
      count := !count + 1;
      sum := !sum + 2 * !count + 1
    done;
    !count

  let main () ensures { result = 4 } = isqrt 17

end
";
  ]

(** registering the std lib *)

(*
let () =
  List.iter
    (fun (name,content) ->
      Sys_js.register_file ~name ~content;
    ) Theories.theories
*)


(** Rendering in the browser *)

module D = Dom_html

module Html = struct

let d = D.document

let node x = (x : #Dom.node Js.t :> Dom.node Js.t)

let of_string s = node (d##createTextNode (Js.string s))

let par nl =
  let x = d##createElement (Js.string "p") in
  List.iter (Dom.appendChild x) nl;
  node x

let ul nl =
  let x = d##createElement (Js.string "ul") in
  List.iter
    (fun n ->
      let y =  d##createElement (Js.string "li") in
      List.iter (Dom.appendChild y) n;
      Dom.appendChild x (node y))
    nl;
  node x

end

let temp_file_name = "/input.mlw"
let why3_conf_file = "/why3.conf"

let () =
  Sys_js.register_file ~name:temp_file_name ~content:""

open Why3
open Format

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config (Some why3_conf_file)
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* One prover named Alt-Ergo in the config file *)
let alt_ergo : Whyconf.config_prover =
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else snd (Whyconf.Mprover.choose provers)

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)


let alt_ergo_driver : Driver.driver =
  try
    Printexc.record_backtrace true;
    Driver.load_driver env alt_ergo.Whyconf.driver []
  with e ->
    let s = Printexc.get_backtrace () in
    eprintf "Failed to load driver for alt-ergo: %a@.%s@."
      Exn_printer.exn_printer e s;
  exit 1


let run_alt_ergo_on_task t =
  (* printing the task in a string *)
  Driver.print_task alt_ergo_driver str_formatter t;
  let text = flush_str_formatter () in
  (* TODO ! *)
  text

let split_trans = Trans.lookup_transform_l "split_goal_wp" env

let run textbox preview (_ : D.mouseEvent Js.t) : bool Js.t =
  let text = Js.to_string (textbox##value) in
  let ch = open_out temp_file_name in
  output_string ch text;
  close_out ch;
  let answer =
    try
      (* TODO: add a function Env.read_string or Env.read_from_lexbuf ? *)
      let theories = Env.read_file Env.base_language env temp_file_name in
(*
      Html.par
        [Html.of_string
           (Pp.sprintf "parsing and typing OK, %d theories"
              (Stdlib.Mstr.cardinal theories))]
*)
      let theories =
        Stdlib.Mstr.fold
          (fun thname th acc ->
            let tasks = Task.split_theory th None None in
            let tasks = List.fold_left
              (fun acc t ->
                let tl = Trans.apply split_trans t in
                List.rev_append tl acc)
              [] tasks
            in
            let tasks =
              List.rev_map
                (fun task ->
                  let (id,expl,_) = Termcode.goal_expl_task ~root:false task in
                  let expl = match expl with
                    | Some s -> s
                    | None -> id.Ident.id_string
                  in
                  let result = run_alt_ergo_on_task task in
                  [Html.of_string (expl ^" : " ^ result)])
                tasks
            in
            [ Html.of_string ("Theory " ^ thname); Html.ul tasks]
            :: acc)
          theories []
      in
      Html.ul theories
(*
      Stdlib.Mstr.iter
        (fun _thname th ->
          let tasks = Task.split_theory th None None in
          List.iter
            (fun task ->
              let (id,expl,_) = Termcode.goal_expl_task ~root:true task in
              let expl = match expl with
                | Some s -> s
                | None -> id.Ident.id_string
              in
              push_answer
                (Pp.sprintf "Goal: %s@\n" expl))
            tasks)
*)
    with
    | Loc.Located(loc,Parser.Error) ->
      let (_,l,b,e) = Loc.get loc in
      Html.par
        [Html.of_string
            (Pp.sprintf "syntax error line %d, columns %d-%d" l b e)]
    | Loc.Located(loc,e') ->
      let (_,l,b,e) = Loc.get loc in
      Html.par
        [Html.of_string
            (Pp.sprintf
               "error line %d, columns %d-%d: %a" l b e
               Exn_printer.exn_printer e')]
    | e ->
      Html.par
        [Html.of_string
            (Pp.sprintf
               "unexpected exception: %a (%s)" Exn_printer.exn_printer e
               (Printexc.to_string e))]
  in
  (* remove the previous answer if any *)
  Js.Opt.iter (preview##lastChild) (Dom.removeChild preview);
  (* put the new answer *)
  Dom.appendChild preview answer;
  Js._false

let onload (_event : #Dom_html.event Js.t) : bool Js.t =
  let input =
    Js.Opt.get (Html.d##getElementById(Js.string "input"))
      (fun () -> assert false) in
  let output =
    Js.Opt.get (Html.d##getElementById(Js.string "output"))
      (fun () -> assert false) in
  (* first, the textbox *)
  let textbox = D.createTextarea Html.d in
  textbox##rows <- 32; textbox##cols <- 64;
  Dom.appendChild input textbox;
  (* second, the example buttons *)
  List.iter
    (fun (name,text) ->
      let b = D.createButton ~name:(Js.string name) Html.d in
      b##textContent <- Js.some (Js.string name);
      Dom.appendChild output b;
      b##onclick <-
        D.handler
        (fun (_ : D.mouseEvent Js.t) ->
          textbox##value <- Js.string text;
          Js._false))
    examples;
  Dom.appendChild output (D.createBr Html.d);
  (* third, the go button *)
  let go = D.createButton ~name:(Js.string "go") Html.d in
  go##textContent <- Js.some (Js.string "Go");
  Dom.appendChild output go;
  Dom.appendChild output (D.createBr Html.d);
  (* then, the answer zone *)
  let preview = D.createDiv Html.d in
  go##onclick <- D.handler (run textbox preview);
  preview##style##border <- Js.string "1px black";
  preview##style##padding <- Js.string "5px";
  Dom.appendChild output preview;
  Js._false

let _ = D.window##onload <- D.handler onload


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. src/trywhy3/trywhy3.js"
End:
*)
