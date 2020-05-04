(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{


  open Cfg_ast

%}


%start cfgfile

%type <Cfg_ast.cfg> cfgfile

%%

cfgfile:
| dl=decl* EOF { dl }
;

decl:
| LET attrs(lident_rich) binders EQUAL seq { $1 }
;

seq:
