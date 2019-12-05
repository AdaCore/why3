
open Why3
open Pretty
open Format
open Term

(* microc print_binop *)
let print_binop fmt = function
  | Tand           -> fprintf fmt "&&"
  | Tor            -> fprintf fmt "||"
  | Timplies       -> fprintf fmt "->"
  | Tiff           -> fprintf fmt "<->"

let rec microc_ext_printer print_any fmt a =
  match a with
  | Pp_term (t, pri) ->
      begin match t.t_node with
        | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
            (* == *)
            fprintf fmt (protect_on (pri > 0) "@[%a == %a@]")
              (microc_ext_printer print_any) (Pp_term (t1, 0))
              (microc_ext_printer print_any) (Pp_term (t2, 0))
        | Tnot {t_node = Tapp (ls, [t1; t2]) } when ls_equal ls ps_equ ->
            (* != *)
            fprintf fmt (protect_on (pri > 0) "@[%a != %a@]")
              (microc_ext_printer print_any) (Pp_term (t1, 0))
              (microc_ext_printer print_any) (Pp_term (t2, 0))
        | Tnot t1 ->
            (* ! *)
            fprintf fmt (protect_on (pri > 0) "@[! %a@]")
              (microc_ext_printer print_any) (Pp_term (t1, 1))
        | Tbinop (b, f1, f2) ->
            (* &&, || *)
            let p = prio_binop b in
            fprintf fmt (protect_on (pri > p) "@[%a %a@ %a@]")
              (microc_ext_printer print_any) (Pp_term (f1, (p + 1)))
              print_binop b
              (microc_ext_printer print_any) (Pp_term (f2, p))
        | _ -> print_any fmt a
      end
  | _ -> print_any fmt a
