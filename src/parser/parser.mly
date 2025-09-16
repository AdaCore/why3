(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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
| seq_expr EOF { $1 }

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


(* Modules and scopes *)

mlw_file:
| EOF
| mlw_module mlw_module_no_decl* EOF
    { Typing.close_file () }
| module_decl module_decl_no_head* EOF
    { let loc = floc $startpos($3) $endpos($3) in
      Typing.close_module loc; Typing.close_file () }

mlw_file_parsing_only:
| EOF { (Modules([])) }
| mlw_module_parsing_only mlw_module_no_decl_parsing_only* EOF { (Modules( [$1] @ $2)) }
| module_decl_parsing_only module_decl_no_head_parsing_only* EOF { (Decls( [$1] @ $2)) }


mlw_module:
| module_head module_decl_no_head* END
    { Typing.close_module (floc $startpos($3) $endpos($3)) }

mlw_module_parsing_only:
| module_head_parsing_only module_decl_no_head_parsing_only* END { ($1,$2) }

module_head:
| THEORY attrs(uident_nq)  { Typing.open_module $2 }
| MODULE attrs(uident_nq) intf = option(preceded(COLON, tqualid))
    { Typing.open_module ?intf $2 }

scope_head:
| SCOPE boption(IMPORT) attrs(uident_nq)
    { Typing.open_scope (floc $startpos $endpos) $3; $2 }

module_decl:
| scope_head module_decl* END
    { Typing.close_scope (floc $startpos($1) $endpos($1)) ~import:$1 }
| IMPORT uqualid
    { Typing.add_decl (floc $startpos $endpos) (Dimport($2)) }
| d = pure_decl | d = prog_decl | d = meta_decl
    { Typing.add_decl (floc $startpos $endpos) d }
| use_clone { () }

module_decl_parsing_only:
| scope_head_parsing_only module_decl_parsing_only* END
    { let loc,import,qid = $1 in (Dscope(loc,import,qid,$2))}
| IMPORT uqualid { (Dimport $2) }
| d = pure_decl | d = prog_decl | d = meta_decl { d }
| use_clone_parsing_only { $1 }

(* Do not open inside another module *)

mlw_module_no_decl:
| SCOPE | IMPORT | USE | CLONE | pure_decl | prog_decl | meta_decl
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| mlw_module
   { $1 }

mlw_module_no_decl_parsing_only:
| SCOPE | IMPORT | USE | CLONE | pure_decl | prog_decl | meta_decl
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| mlw_module_parsing_only
   { $1 }

module_decl_no_head:
| THEORY | MODULE
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| module_decl
   { $1 }

module_decl_no_head_parsing_only:
| THEORY | MODULE
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| module_decl_parsing_only
   { $1 }


(* Use and clone *)

use_clone:
| USE EXPORT tqualid
    { let loc = floc $startpos $endpos in
      let decl = Ptree.Duseexport (loc, $3) in
      Typing.add_decl loc decl
    }
| CLONE EXPORT tqualid clone_subst
    { let loc = floc $startpos $endpos in
      let decl = Ptree.Dcloneexport(loc,$3,$4) in
      Typing.add_decl loc decl
    }
| USE boption(IMPORT) m_as_list = comma_list1(use_as)
    { let loc = floc $startpos $endpos in
      let exists_as = List.exists (fun (_, q) -> q <> None) m_as_list in
      let import = $2 in
      if import && not exists_as then Loc.warning ~loc warn_redundant_import
        "the keyword `import' is redundant here and can be omitted";
      let decl = Ptree.Duseimport(loc,import,m_as_list) in
      Typing.add_decl loc decl
    }
| CLONE boption(IMPORT) tqualid option(preceded(AS, uident)) clone_subst
    { let loc = floc $startpos $endpos in
      let import = $2 in
      let as_opt = $4 in
      if import && as_opt = None then Loc.warning ~loc warn_redundant_import
        "the keyword `import' is redundant here and can be omitted";
      let decl = Ptree.Dcloneimport(loc,import,$3,as_opt,$5) in
      Typing.add_decl loc decl
    }
