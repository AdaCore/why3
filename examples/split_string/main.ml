
open Format
module Q = Queue

let print_queue fmt q =
  while not (Q.is_empty q) do
    let s = Q.pop q in
    fprintf fmt "%S" s;
    if not (Q.is_empty q) then fprintf fmt ",@ "
  done

let test ?(limit = -1) ?(sep='.') s =
    printf "split %S %C " s sep;
    if limit <> -1 then printf "(limit=%d) " limit;
    let q = Split_string.split_string s sep limit in
    printf "=> @[[%a@]]@." print_queue q

let () = test ""
let () = test "."
let () = test ".."
let () = test "abc"
let () = test "abc."
let () = test ".abc"
let () = test "a.bc"
let () = test "a..bc"

let () = test ~limit:2 "a."
let () = test ~limit:2 "b.."
let () = test ~limit:2 "b..."
let () = test ~limit:2 "ba.b.b."
