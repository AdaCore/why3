open Apron
open Term

module Apron_to_term(E: sig
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct

  exception Cannot_be_expressed

  let th_int = Env.read_theory E.env ["int"] "Int"
  let int_tys = Theory.(ns_find_ts th_int.th_export ["int"])
  let ty_int = (Ty.ty_app int_tys [])
  (*let int_zero = fs_app Theory.(ns_find_ls th_int.th_export ["zero"]) [] ty_int (* not nice *) *)
  let int_zero = t_nat_const 0
  let int_one = t_nat_const 1
  let int_le = Theory.(ns_find_ls th_int.th_export ["infix <="])
  let int_lt = Theory.(ns_find_ls th_int.th_export ["infix <"])
  let int_add =  begin fun a ->
    match a with
    | [a; b] ->
      if t_equal a int_zero then b
      else if t_equal b int_zero then a
      else fs_app Theory.(ns_find_ls th_int.th_export ["infix +"]) [a; b] ty_int
    | _ -> assert false
  end
  let int_minus_u = fun a -> fs_app Theory.(ns_find_ls th_int.th_export ["prefix -"]) a ty_int
  let int_minus = begin fun a ->
    match a with
    | [a; b] ->
      if t_equal a int_zero then int_minus_u [b]
      else if t_equal b int_zero then a
      else fs_app Theory.(ns_find_ls th_int.th_export ["infix -"]) [a; b] ty_int
    | _ -> assert false
  end
  let int_mult = fun a -> fs_app Theory.(ns_find_ls th_int.th_export ["infix *"]) a ty_int

  type coeff =
    | CNone
    | CPos of Term.term
    | CMinus of Term.term
    | CMinusOne
    | COne

  let int_of_string s =
    let f = float_of_string s in
    let i = int_of_float f in
    assert (float_of_int i = f);
    i

  let coeff_to_term = function
    | Coeff.Scalar(s) ->
      let i = int_of_string (Scalar.to_string s) in
      let n = Constant.int_const_of_int (abs i) in

      if i = 1 then
        COne
      else if i = -1 then
        CMinusOne
      else if i > 0 then
        CPos (t_const n Ty.ty_int)
      else if i < 0 then
        CMinus (t_const n Ty.ty_int)
      else
        CNone
    | Coeff.Interval(_) -> raise Cannot_be_expressed

  let lincons_to_term l variable_mapping =
    let open Ty in
    let term = ref int_zero in
    Lincons1.iter (fun c v ->
        match coeff_to_term c with
        | CPos c ->
          let v = variable_mapping v in
          term := int_add [!term; int_mult [c; v]];
        | COne ->
          let v = variable_mapping v in
          term := int_add [!term; v];
        | CMinusOne ->
          let v = variable_mapping v in
          term := int_minus [!term; v];
        | CMinus c ->
          let v = variable_mapping v in
          term := int_minus [!term; int_mult [c; v]];
        | CNone -> ()
      ) l;
    let c = coeff_to_term (Lincons1.get_cst l) in
    let term = match c with
      | CNone -> !term
      | CPos c ->
        int_add [c; !term]
      | CMinus c ->
        int_minus [!term;c]
      | COne ->
        int_add [int_one; !term]
      | CMinusOne ->
        int_minus [!term; int_one]
    in
    match Lincons1.get_typ l with
    | Lincons1.EQ -> ps_app ps_equ [term; int_zero]
    | Lincons1.SUP -> ps_app int_lt [int_zero; term]
    | Lincons1.SUPEQ -> ps_app int_le [int_zero; term;]
    | Lincons1.DISEQ ->  t_not (ps_app ps_equ [term; int_zero])
    | Lincons1.EQMOD _ -> assert false

  let lincons_array_to_term l variable_mapping =
    let n = Lincons1.array_length l in
    let t = ref (Term.t_true) in
    for i = 0 to n - 1 do
      t := t_and_simp !t (lincons_to_term (Lincons1.array_get l i) variable_mapping);
    done;
    !t

  let domain_to_term man d variable_mapping =
    let a = Abstract1.to_lincons_array man d in
    lincons_array_to_term a variable_mapping

end
