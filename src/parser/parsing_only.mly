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


(**

  This is an extension of the main grammar, to be used for parsing only and
  producing [Ptree]

*)


%{

  (* no new tokens! *)

%}


(* One new entry point *)

%start <Ptree.mlw_file> mlw_file_parsing_only

%%

(* new rules *)

mlw_file_parsing_only:
| EOF { (Modules([])) }
| mlw_module_parsing_only mlw_module_no_decl_parsing_only* EOF { (Modules( [$1] @ $2)) }
| module_decl_parsing_only module_decl_no_head_parsing_only* EOF { (Decls( [$1] @ $2)) }

mlw_module_parsing_only:
| module_head_parsing_only module_decl_no_head_parsing_only* END { ($1,$2) }

module_head_parsing_only:
| THEORY attrs(uident_nq)  { $2 }
| MODULE attrs(uident_nq)  { $2 }

scope_head_parsing_only:
| SCOPE boption(IMPORT) attrs(uident_nq)
    { let loc = floc $startpos $endpos in (loc, $2, $3) }

module_decl_parsing_only:
| scope_head_parsing_only module_decl_parsing_only* END
    { let loc,import,qid = $1 in (Dscope(loc,import,qid,$2))}
| IMPORT uqualid { (Dimport $2) }
| d = pure_decl | d = prog_decl | d = meta_decl { d }
| use_clone_parsing_only { $1 }

mlw_module_no_decl_parsing_only:
| SCOPE | IMPORT | USE | CLONE | pure_decl | prog_decl | meta_decl
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| mlw_module_parsing_only
   { $1 }

module_decl_no_head_parsing_only:
| THEORY | MODULE
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| module_decl_parsing_only
   { $1 }

(* Use and clone *)

use_clone_parsing_only:
| USE EXPORT tqualid
    { (Duseexport $3) }
| CLONE EXPORT tqualid clone_subst
    { (Dcloneexport ($3, $4)) }
| USE boption(IMPORT) m_as_list = comma_list1(use_as)
    { let loc = floc $startpos $endpos in
      let exists_as = List.exists (fun (_, q) -> q <> None) m_as_list in
      if $2 && not exists_as then Warning.emit ~loc
        "the keyword `import' is redundant here and can be omitted";
      (Duseimport (loc, $2, m_as_list)) }
| CLONE boption(IMPORT) tqualid option(preceded(AS, uident)) clone_subst
    { let loc = floc $startpos $endpos in
      if $2 && $4 = None then Warning.emit ~loc
        "the keyword `import' is redundant here and can be omitted";
      (Dcloneimport (loc, $2, $3, $4, $5)) }
