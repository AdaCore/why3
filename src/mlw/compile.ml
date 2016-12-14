(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*
  - option to extract into a single file

  - no more why3extract.cma
    use driver preludes instead

  - 2 drivers for nums and zarith

  - no delcaration at all for a module -> no file produced
    (e.g. ref.Ref)

  - suggest a command line to compile the extracted code
    (for instance in a comment)

  - drivers for val now may use %1, %2, etc. (though not mandatory)
    Capp f x y
      "..." -> "..." x y
      "...%1..." -> "...x..." y
      "..(*%1*)..." -> "...(*x*)..." y
      "..%1..%3.." -> (fun z -> "..x..z..")  (y ignored)

  - extract file f.mlw into OCaml file f.ml, with sub-modules

  - "use (im|ex)port" -> "open"
    but OCaml's open is not transitive, so requires some extra work
    to figure out all the opens

  - if a WhyML module M is extracted to something that is a signature,
    then extract "module type B_sig = ..." (as well as "module B = ...")

  - use a black list in printer to avoid clash with Pervasives symbols
    (e.g. ref, (!), etc.)

*)

(** Abstract syntax of ML *)

open Ident
open Ity

module ML = struct

  type ty =
    | Tvar    of ident
    | Tapp    of ident * ty list
    | Ttuple  of ty list

  type var = ident * ty

  type pat =
    | Pwild
    | Pident  of ident
    | Papp    of ident * pat list
    | Ptuple  of pat list
    | Precord of (ident * pat) list
    | Por     of pat * pat
    | Pas     of pat * ident

  type is_rec = bool

  type binop = Band | Bor | Beq

  type for_direction = To | DownTo

  type exn =
    | Xident  of ident
    | Xsyntax of string
    | Xexit             (* Pervasives.Exit *)

  type expr = {
    e_node : expr_node;
    e_ity  : ity;
  }

  and expr_node =
    | Econst  of Number.integer_constant
    | Ebool   of bool
    | Eident  of ident
    | Eapp    of expr * expr list
    | Efun    of var list * expr
    | Elet    of ident * expr * expr
    | Eletrec of is_rec * (ident * var list * expr) list * expr
    | Eif     of expr * expr * expr
    | Ecast   of expr * ty
    | Etuple  of expr list (* at least 2 expressions *)
    | Econstr of ident * expr list
    | Ematch  of expr * (pat * expr) list
    | Ebinop  of expr * binop * expr
    | Enot    of expr
    | Eblock  of expr list
    | Ewhile  of expr * expr
    | Efor    of ident * ident * for_direction * ident * expr
    | Eraise  of exn * expr option
    | Etry    of expr * (exn * ident option * expr) list
    | Eabsurd

  type is_mutable = bool

  type typedef =
    | Dabstract
    | Ddata     of (ident * ty list) list
    | Drecord   of (is_mutable * ident * ty) list
    | Dalias    of ty

  type decl = (* TODO add support for the extraction of ocaml modules *)
    | Dtype of (ident * ident list * typedef) list
    | Dlet  of is_rec * (ident * var list * expr) list
        (* TODO add return type? *)
    | Dexn  of ident * ty option

(* TODO add here some smart constructors for ML expressions *)

end
