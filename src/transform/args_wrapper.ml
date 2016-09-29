

open Task
open Ty
open Term
open Trans

type _ trans_typ =
  | Ttrans : (task -> task list) trans_typ
  | Tint : 'a trans_typ -> (int -> 'a) trans_typ
  | Tstring : 'a trans_typ -> (string -> 'a) trans_typ
  | Tty : 'a trans_typ -> (ty -> 'a) trans_typ
  | Ttysymbol : 'a trans_typ -> (tysymbol -> 'a) trans_typ
  | Tterm : 'a trans_typ -> (term -> 'a) trans_typ

let rec wrap : type a. a trans_typ -> a -> trans_with_args =
  fun t f l task ->
  match t with
  | Ttrans -> f task
  | Tint t' ->
    begin
      match l with
      | s :: tail ->
         let n = int_of_string s in
         wrap t' (f n) tail task
      | _ -> assert false
    end
  | Tstring t' ->
    begin
      match l with
      | s :: tail -> wrap t' (f s) tail task
      | _ -> assert false
    end
  | Tterm t' ->
    begin
      match l with
      | _s :: tail ->
         let te = Term.t_true in (* TODO: parsing + typing of s *)
         wrap t' (f te) tail task
      | _ -> assert false
    end
  | Tty t' ->
    begin
      match l with
      | _s :: tail ->
         let ty = Ty.ty_int in (* TODO: parsing + typing of s *)
         wrap t' (f ty) tail task
      | _ -> assert false
    end
  | Ttysymbol t' ->
    begin
      match l with
      | _s :: tail ->
         let tys = Ty.ts_int in (* TODO: parsing + typing of s *)
         wrap t' (f tys) tail task
      | _ -> assert false
    end
