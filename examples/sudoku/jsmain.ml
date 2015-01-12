

module D = Dom_html

let d = D.document

(* Grid Layout *)

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
    style##fontFamily <- Js.string "monospace";
    style##fontSize <- Js.string "20px";
    style##fontWeight <- Js.string "bold";
    style##paddingBottom <- Js.string "5px";
    style##paddingTop <- Js.string "5px";
    style##paddingLeft <- Js.string "10px";
    style##paddingRight <- Js.string "10px";
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
    input
  in
  let make_td i j input =
    let td = D.createTd d in
    td##align <- Js.string "center";
    let style = td##style in
    style##borderStyle <- Js.string "solid";
    style##borderColor <- Js.string "#000000";
    let widths = function
      | 0 -> 3, 0 | 2 -> 1, 1 | 3 -> 1, 0
      | 5 -> 1, 1 | 6 -> 1, 0 | 8 -> 1, 3
      | _ -> 1, 0 in
    let (top, bottom) = widths i in
    let (left, right) = widths j in
    let px k = Js.string (string_of_int k ^ "px") in
    style##borderTopWidth <- px top;
    style##borderBottomWidth <- px bottom;
    style##borderLeftWidth <- px left;
    style##borderRightWidth <- px right;
    Dom.appendChild td input;
    td
  in
  let rows = Array.init 9 (fun i -> Array.init 9 (fun j -> make_input ())) in
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


(* Solver *)

open Why3extract

let display_sol rows a =
  for i=0 to 8 do
    for j=0 to 8 do
      let cell = rows.(i).(j) in
      cell##value <- Js.string (Why3__BigInt.to_string a.(9*i+j));
      cell##style##backgroundColor <- Js.string "#ffffff"
    done
  done

let no_sol rows =
  for i=0 to 8 do
    for j=0 to 8 do
      let cell = rows.(i).(j) in
      cell##style##backgroundColor <- Js.string "#ff0000"
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
  begin
    try
      let a = Sudoku__Solver.check_then_solve sudoku input_grid in
      display_sol rows a
    with Sudoku__Solver.NoSolution -> no_sol rows
  end;
  Js._false

(* reset board to empty cells *)

let reset_board rows _ =
  for i=0 to 8 do
    for j=0 to 8 do
      let cell = rows.(i).(j) in
      cell##value <- Js.string "";
      cell##style##backgroundColor <- Js.string "#ffffff";
    done
  done;
  Js._false

(* load examples *)

let load_board rows test _ =
  for i=0 to 8 do
    for j=0 to 8 do
      let cell = rows.(i).(j) in
      let v = test.(9*i+j) in
      let v = if v = 0 then "" else string_of_int v in
      cell##value <- Js.string v;
      cell##style##backgroundColor <- Js.string "#ffffff";
    done
  done;
  Js._false

let test1 =
[| 2;0;9;0;0;0;0;1;0;
   0;0;0;0;6;0;0;0;0;
   0;5;3;8;0;2;7;0;0;
   3;0;0;0;0;0;0;0;0;
   0;0;0;0;7;5;0;0;3;
   0;4;1;2;0;8;9;0;0;
   0;0;4;0;9;0;0;2;0;
   8;0;0;0;0;1;0;0;5;
   0;0;0;0;0;0;0;7;6 |]

let test2 =
[| 7;0;0;0;0;0;0;0;8;
   0;9;0;7;0;6;0;3;0;
   0;0;1;0;0;0;9;0;0;
   0;7;0;1;0;4;0;5;0;
   0;0;0;0;6;0;0;0;0;
   0;5;0;3;0;7;0;1;0;
   0;0;2;0;0;0;1;0;0;
   0;1;0;9;0;8;0;7;0;
   8;0;0;0;0;0;0;0;6 |]

let test3 =
[| 0;0;0;0;0;0;0;0;0;
   0;0;0;0;0;3;0;8;5;
   0;0;1;0;2;0;0;0;0;
   0;0;0;5;0;7;0;0;0;
   0;0;4;0;0;0;1;0;0;
   0;9;0;0;0;0;0;0;0;
   5;0;0;0;0;0;0;7;3;
   0;0;2;0;1;0;0;0;0;
   0;0;0;0;4;0;0;0;9 |]

let onload (_event : #Dom_html.event Js.t) : bool Js.t =
  let (rows, table) = make_board () in
  let solve = Js.Opt.get (d##getElementById (Js.string "solve"))
    (fun () -> assert false) in
  solve##onclick <- Dom_html.handler (solve_board rows);
  let reset = Js.Opt.get (d##getElementById (Js.string "reset"))
    (fun () -> assert false) in
  reset##onclick <- Dom_html.handler (reset_board rows);
  let sample1 = Js.Opt.get (d##getElementById (Js.string "sample1"))
    (fun () -> assert false) in
  sample1##onclick <- Dom_html.handler (load_board rows test1);
  let sample2 = Js.Opt.get (d##getElementById (Js.string "sample2"))
    (fun () -> assert false) in
  sample2##onclick <- Dom_html.handler (load_board rows test2);
  let sample3= Js.Opt.get (d##getElementById (Js.string "sample3"))
    (fun () -> assert false) in
  sample3##onclick <- Dom_html.handler (load_board rows test3);
  let board = Js.Opt.get (d##getElementById (Js.string "board"))
    (fun () -> assert false) in
  Dom.appendChild board table;
  board##style##padding <- Js.string "40px";
  Js._false

let _ = Dom_html.window##onload <- Dom_html.handler onload
