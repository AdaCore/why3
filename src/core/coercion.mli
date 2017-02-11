

type coercion_kind =
  | CRCleaf of Term.lsymbol
  | CRCcomp of coercion_kind * coercion_kind

type coercion = private {
  crc_kind: coercion_kind;
  crc_src : Ty.tysymbol;
  crc_tar : Ty.tysymbol;
  crc_len : int;
}

type t
  (** a set of coercions *)

val empty: t

val add: t -> Term.lsymbol -> t
  (** adds a new coercion from function [ls: ty1 -> ty2 ]
      raises an error if
        - this introduces a cycle, i.e. a coercion from [ty2] to [ty1] is already defined;
        - function [ls] cannot be coercion, i.e. [ty1 = ty2];
        - a coercion from [ty1] to [ty2] is already defined *)

val find: t -> Ty.tysymbol -> Ty.tysymbol -> coercion
  (** returns the coercion, or raises [Not_found] *)

val union: t -> t -> t
  (** [union s1 s2] merges the coercions from [s2] into [s1]
      (as a new set of coercions)
      this is asymetric: a coercion from [s2] may hide a coercion from [s1] *)
