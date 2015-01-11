

let () = Firebug.console##info (Js.string "debut de jsmain.ml")

module D = Dom_html

let d = D.document

let make_board () =
  let make_input () =
    let input =
      D.createInput ~_type:(Js.string "text") ~name:(Js.string "input") d
    in
    input##size <- 1;
    input##maxLength <- 1;
    input##align <- Js.string "center";
    let style = input##style in
    style##border <- Js.string "none";
    style##padding <- Js.string "0px";
    style##maxWidth <- Js.string "20px";
    let enforce_digit _ =
      begin
        match Js.to_string input##value with
        | "1" | "2" | "3" | "4" | "5"
        | "6" | "7" | "8" | "9" -> ()
        | _ -> input##value <- Js.string ""
      end;
      Js._false
    in
    input##onchange <- Dom_html.handler enforce_digit;
    input in

  (* We construct the Sudoku board in several steps. First, we make an
     input box for each square. Notice that you can call DOM methods
     (e.g. createElement) with OCaml object syntax. But what is the type of
     createElement? The type of the object you get back depends on the tag
     name you pass in; OCaml has no type for that. So createElement is
     declared to return #element (that is, a subclass of element). If you
     need only methods from element then you usually don't need to ascribe
     a more-specific type, but in this case we need an input node. (Static
     type checking with Javascript objects is therefore only advisory in
     some cases--if you ascribe the wrong type you can get a runtime
     error--but still better than nothing.)

     We next set some attributes, properties, and styles on the input
     box. Properties are manipulated with specially-named methods:
     foo#_get_bar becomes foo.bar in Javascript, and foo#_set_bar baz
     becomes foo.bar = baz. Finally we add a validation function to enforce
     that the input box contains at most a single digit. To set the
     onchange handler, you need to wrap it in Ocamljs.jsfun, because the
     calling convention of an ocamljs function is different from that of
     plain Javascript function (to accomodate partial application and tail
     recursion).
  *)

  let make_td i j input =
    let td = D.createTd d in
    td##align <- Js.string "center";
    let style = td##style in
    style##borderStyle <- Js.string "solid";
    style##borderColor <- Js.string "#000000";
    let widths = function
      | 0 -> 2, 0 | 2 -> 1, 1 | 3 -> 1, 0
      | 5 -> 1, 1 | 6 -> 1, 0 | 8 -> 1, 2
      | _ -> 1, 0 in
    let (top, bottom) = widths i in
    let (left, right) = widths j in
    let px k = Js.string (string_of_int k ^ "px") in
    style##borderTopWidth <- px top;
    style##borderBottomWidth <- px bottom;
    style##borderLeftWidth <- px left;
    style##borderRightWidth <- px right;
    Dom.appendChild td input;
    td in

  (* Next we make a table cell for each square, containing the input
     box, with borders according to its position in the grid. Here we don't
     ascribe a type to the result of createElement since we don't need any
     td-specific methods.
  *)

  let rows =
    Array.init 9 (fun i ->
      Array.init 9 (fun j ->
        make_input ())) in

  let table = D.createTable d in
  table##cellPadding <- Js.string "0px";
  table##cellSpacing <- Js.string "0px";
  let tbody = D.createTbody d in
  Dom.appendChild table tbody;
  ArrayLabels.iteri rows ~f:(fun i row ->
    let tr = D.createTr d in
    ArrayLabels.iteri row ~f:(fun j cell ->
      let td = make_td i j cell in
      ignore (Dom.appendChild tr td));
    ignore (Dom.appendChild tbody tr));

  (rows, table)

(* Then we assemble the full board: make a 9 x 9 matrix of input
   boxes, make a table containing the input boxes, then return the matrix
   and table. Notice that we freely use the OCaml standard library. Here
   the tbody is necessary for IE; the cellpadding and cellspacing don't
   work in IE for some reason that I have not tracked down. This raises
   an important point: the Dom module is the thinnest possible wrapper
   over the actual DOM objects, and as such gives you no help with
   cross-browser compatibility.
*)

let check_board rows _ =
  let error i j =
    let cell = rows.(i).(j) in
    cell##style##backgroundColor <- Js.string "#ff0000" in

  let check_set set =
    let seen = Array.make 9 None in
    ArrayLabels.iter set ~f:(fun (i,j) ->
      let cell = rows.(i).(j) in
      match Js.to_string cell##value with
        | "" -> ()
        | v ->
            let n = int_of_string v in
            match seen.(n - 1) with
              | None ->
                  seen.(n - 1) <- Some (i,j)
              | Some (i',j') ->
                  error i j;
                  error i' j') in

  let check_row i =
    check_set (Array.init 9 (fun j -> (i,j))) in

  let check_column j =
    check_set (Array.init 9 (fun i -> (i,j))) in

  let check_square i j =
    let set = Array.init 9 (fun k ->
      i * 3 + k mod 3, j * 3 + k / 3) in
    check_set set in

  ArrayLabels.iter rows ~f:(fun row ->
    ArrayLabels.iter row ~f:(fun cell ->
      cell##style##backgroundColor <- Js.string "#ffffff"));

  for i = 0 to 8 do check_row i done;
  for j = 0 to 8 do check_column j done;
  for i = 0 to 2 do
    for j = 0 to 2 do
      check_square i j
    done
  done;
  Js._false

(* Now we define a function to check that the Sudoku constraints are
   satisfied: that no row, column, or heavy-lined square has more than
   one occurrence of a digit. If more than one digit occurs then we color
   all occurrences red. The only ocamljs-specific parts here are getting
   the cell contents (with _get_value) and setting the background color
   style. However, it's worth noticing the algorithm: we imperatively
   clear the error states for all cells, then set error states as we
   check each constraint. I'll revisit this in a later post about
   functional reactive programming.
*)

open Why3extract

let display_sol rows a =
  for i=0 to 8 do
    for j=0 to 8 do
      let cell = rows.(i).(j) in
      cell##value <- Js.string (Why3__BigInt.to_string a.(9*i+j))
    done
  done

let solve_board rows _ =
  let sudoku = Sudoku__TheClassicalSudokuGrid.classical_sudoku () in
  let input_grid = Array.make 81 Why3__BigInt.zero in
  for i=0 to 8 do
    for j=0 to 8 do
      let cell = rows.(i).(j) in
      let v =
        match Js.to_string cell##value with
        | "" -> 0
        | s -> Char.code s.[0] - Char.code '0'
      in
      input_grid.(9*i+j) <- Why3__BigInt.of_int v
    done
  done;
  let a = Sudoku__Solver.solve sudoku input_grid in
  display_sol rows a;
  Js._false


let onload (_event : #Dom_html.event Js.t) : bool Js.t =
  let (rows, table) = make_board () in
  let check = Js.Opt.get (d##getElementById (Js.string "check"))
    (fun () -> assert false) in
  check##onclick <- Dom_html.handler (check_board rows);
  let solve = Js.Opt.get (d##getElementById (Js.string "solve"))
    (fun () -> assert false) in
  solve##onclick <- Dom_html.handler (solve_board rows);
  let board = Js.Opt.get (d##getElementById (Js.string "board"))
    (fun () -> assert false) in
  Dom.appendChild board table;
  board##style##backgroundColor <- Js.string "#00ff00";
  board##style##paddingLeft <- Js.string "40px";
  board##style##paddingRight <- Js.string "40px";
  board##style##paddingBottom <- Js.string "40px";
  board##style##paddingTop <- Js.string "40px";
  Js._false

let _ = Dom_html.window##onload <- Dom_html.handler onload

(* Finally we put the pieces together: make the board, insert it into
   the DOM, call check_board when the Check button is clicked, and call
   this setup code once the document has been loaded. See the full source
   for build files.
*)
