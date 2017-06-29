open Term

exception Arg_trans of string
exception Arg_trans_term of (string * term * term)
exception Arg_trans_pattern of (string * pattern * pattern)
exception Arg_trans_type of (string * Ty.ty * Ty.ty)
exception Arg_bad_hypothesis of (string * term)
exception Cannot_infer_type of string

let gen_ident = Ident.id_fresh

(* Replace all occurences of f1 by f2 in t *)
let replace_in_term = Term.t_replace
(* TODO be careful with label copy in t_map *)

let subst_quant c tq x : term =
  let (vsl, tr, te) = t_open_quant tq in
  (match vsl with
  | hdv :: tl ->
      (try
        (let new_t = t_subst_single hdv x te in
        t_quant_close c tl tr new_t)
      with
      | Ty.TypeMismatch (ty1, ty2) ->
          raise (Arg_trans_type ("subst_quant", ty1, ty2)))
  | [] -> failwith "subst_quant: Should not happen, please report")

(* Transform the term (exists v, f) into f[x/v] *)
let subst_exist t x =
  match t.t_node with
  | Tquant (Texists, tq) ->
      subst_quant Texists tq x
  | _ -> raise (Arg_trans "subst_exist")

(* Transform the term (forall v, f) into f[x/v] *)
let subst_forall t x =
  match t.t_node with
  | Tquant (Tforall, tq) ->
      subst_quant Tforall tq x
  | _ -> raise (Arg_trans "subst_forall")
