
open Why
open Ident
open Term
open Decl
open Theory
open Pgm_ttree

let wp _l _e = f_true (* TODO *)

let wp_recfun _l _def = f_true (* TODO *)

let add_wp_decl uc l f =
  let pr = create_prsymbol (id_fresh ("WP_" ^ l.ls_name.id_string)) in
  let d = create_prop_decl Pgoal pr f in
  add_decl uc d

let decl uc = function
  | Dlet (l, e) ->
      let f = wp l e in
      add_wp_decl uc l f
  | Dletrec dl ->
      let add_one uc (l, def) = let f = wp_recfun l def in add_wp_decl uc l f in
      List.fold_left add_one uc dl
  | Dparam _ ->
      uc

let file uc dl =
  let uc = List.fold_left decl uc dl in
  Theory.close_theory uc
