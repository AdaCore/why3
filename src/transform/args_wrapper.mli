
open Task

type _ trans_typ =
  | Ttrans : (task -> task list) trans_typ
  | Tint : 'a trans_typ -> (int -> 'a) trans_typ
  | Tstring : 'a trans_typ -> (string -> 'a) trans_typ
  | Tty : 'a trans_typ -> (Ty.ty -> 'a) trans_typ
  | Ttysymbol : 'a trans_typ -> (Ty.tysymbol -> 'a) trans_typ
  | Tterm : 'a trans_typ -> (Term.term -> 'a) trans_typ

val wrap : 'a trans_typ -> 'a -> Trans.trans_with_args
