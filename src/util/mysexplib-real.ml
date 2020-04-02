module Std = Sexplib.Std
module Std_big_int = Sexplib_num.Std.Big_int

let of_list = function
  | Sexplib.Sexp.List l -> l
  | _ -> invalid_arg "Mysexplib.of_list"
