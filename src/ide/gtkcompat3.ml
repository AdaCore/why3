(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

#13 "src/ide/gtkcompat3.ml"
module GSourceView = GSourceView3

let gpango_font_description_from_string s =
  new GPango.font_description (Pango.Font.from_string s)
(* TODO: use GPango.font_description_from_string once lablgtk3 >= 3.0~beta4 *)
