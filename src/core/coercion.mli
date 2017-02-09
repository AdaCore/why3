

type crc = private
           { crc_lsl : Term.lsymbol list;
             crc_src : Ty.tysymbol;
             crc_tar : Ty.tysymbol;
             crc_len : int }

type t
  (** a set of coercions *)

val empty: t

val add: t -> Term.lsymbol -> t
  (** adds a new coercion
      raises an error if this introduces a cycle *)

val find: t -> Ty.tysymbol -> Ty.tysymbol -> crc
  (** returns the coercion, or raises [Not_found] *)

val union: t -> t -> t
  (** [union s1 s2] merges the coercions from [s2] into [s1]
      (as a new set of coercions)
      this is asymetric: a coercion from [s2] may hide a coercion from [s1] *)
