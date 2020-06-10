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

%}

(* Entry points *)

%start <Pmodule.pmodule Wstdlib.Mstr.t> mlw_file
%start <Ptree.mlw_file> mlw_file_parsing_only
%start <Ptree.term> term_eof
%start <Ptree.expr> expr_eof
%start <Ptree.decl> decl_eof
%start <Ptree.qualid> qualid_eof
%start <Ptree.qualid list> qualid_comma_list_eof
%start <Ptree.term list> term_comma_list_eof
%start <Ptree.ident list> ident_comma_list_eof


%%

(* parsing of a single term or a single decl *)

term_eof:
| term EOF { $1 }

expr_eof:
| expr EOF { $1 }

decl_eof:
| pure_decl EOF { $1 }
| prog_decl EOF { $1 }

(* Parsing of a list of qualified identifiers for the ITP *)

qualid_eof:
| qualid EOF { $1 }

qualid_comma_list_eof:
| comma_list1(qualid) EOF { $1 }

ident_comma_list_eof:
| comma_list1(ident) EOF { $1 }

term_comma_list_eof:
| comma_list1(single_term) EOF { $1 }
(* we use single_term to avoid conflict with tuples, that
   do not need parentheses *)
