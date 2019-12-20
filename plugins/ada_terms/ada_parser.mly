(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
  open Why3
  open Ptree

  let floc s e = Loc.extract (s,e)

  let add_attr id l = (* id.id_ats is usually nil *)
    { id with id_ats = List.rev_append id.id_ats l }

  let id_anonymous loc = { id_str = "_"; id_ats = []; id_loc = loc }

  let mk_id id s e = { id_str = id; id_ats = []; id_loc = floc s e }
  let mk_id_noloc id = { id_str = id; id_ats = []; id_loc = Loc.dummy_position }

  let get_op  q s e = Qident (mk_id (Ident.op_get q) s e)
  let upd_op  q s e = Qident (mk_id (Ident.op_update q) s e)
  let cut_op  q s e = Qident (mk_id (Ident.op_cut q) s e)
  let rcut_op q s e = Qident (mk_id (Ident.op_rcut q) s e)
  let lcut_op q s e = Qident (mk_id (Ident.op_lcut q) s e)

  let mk_pat  d s e = { pat_desc  = d; pat_loc  = floc s e }
  let mk_term d s e = { term_desc = d; term_loc = floc s e }
  let mk_term_loc d l = { term_desc = d; term_loc = l }

  let create_in_range inf sup v =
    let ineq1 = mk_term_loc (Tidapp (Qident (mk_id_noloc (Ident.op_infix "<=")),
                                     [inf; mk_term_loc (Tident (Qident v)) Loc.dummy_position]))
                            Loc.dummy_position in
    let ineq2 = mk_term_loc (Tidapp (Qident (mk_id_noloc (Ident.op_infix "<=")),
                                 [mk_term_loc (Tident (Qident v)) Loc.dummy_position; sup]))
                            Loc.dummy_position in
    mk_term_loc (Tbinop (ineq1, Dterm.DTand, ineq2)) Loc.dummy_position

  let double_ref {id_loc = loc} =
    Loc.errorm ~loc "this variable is already a reference"

  let set_ref id =
    List.iter (function
      | ATstr a when Ident.attr_equal a Pmodule.ref_attr ->
          double_ref id
      | _ -> ()) id.id_ats;
    { id with id_ats = ATstr Pmodule.ref_attr :: id.id_ats }

  let set_ref_opt loc r = function
    | id when not r -> id
    | Some id -> Some (set_ref id)
    | None -> Loc.errorm ~loc "anonymous parameters cannot be references"

  let binder_of_id id =
    if id.id_str = "ref" then Loc.error ~loc:id.id_loc Error;
    (* TODO: recognize and fail on core idents *)
    Some id

  let error_loc loc = Loc.error ~loc Error

  let () = Exn_printer.register (fun fmt exn -> match exn with
    | Error -> Format.fprintf fmt "syntax error %s" (Parser_messages.message 1)
    | _ -> raise exn)

  let core_ident_error  = format_of_string
    "Symbol %s cannot be user-defined. User-defined symbol cannot use ' \
      before a letter. You can only use ' followed by _ or a number."

  let convert_array (a: term) =
    let nt = Ada_nametable.get_naming_table () in
    let a_str = match a.term_desc with
      | Tident (Qident id) -> id.id_str
      | _ -> ""  in
    match Ada_nametable.convert_array nt a_str with
    | id_str ->
       mk_term_loc (Tidapp (Qident (mk_id_noloc id_str), [a])) Loc.dummy_position
    | exception Not_found -> a


%}

(* Tokens *)

%token <string> LIDENT CORE_LIDENT UIDENT CORE_UIDENT
%token <Why3.Number.int_constant> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Why3.Number.real_constant> REAL
%token <string> ATTRIBUTE
%token <Why3.Loc.position> POSITION
%token <string> QUOTE_LIDENT
%token <string> RIGHTSQ_QUOTE (* ]'' *)
%token <string> RIGHTPAR_QUOTE (* )'spec *)
%token <string> RIGHTPAR_USCORE (* )_spec *)

(* keywords *)

%token AS BY
%token ELSE END FALSE FLOAT
(* Ada quantification *)
%token FOR ALL SOME
%token IF IN
%token LET MATCH NOT RANGE
%token SO THEN TRUE WITH

(* program keywords *)

%token AT BEGIN
%token FUN GHOST OLD
%token REF

(* symbols *)

%token AND ARROW
%token AMP BAR
%token COLON COMMA
%token DARROW
%token QUOTE
%token DOT DOTDOT EQUAL LT GT LTGT MINUS
%token LEFTPAR LEFTSQ
%token LARROW LRARROW OR
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

(* program symbols *)

%token LEFTBRC RIGHTBRC SEMICOLON

(* Precedences *)

%nonassoc DOT
%nonassoc below_COMMA
%nonassoc COMMA
%nonassoc AS
%nonassoc GHOST
%nonassoc prec_attr
%nonassoc COLON (* weaker than -> because of t: a -> b *)
%right ARROW LRARROW BY SO
%right OR ELSE
%right AND THEN
%nonassoc NOT
%right EQUAL LTGT LT GT OP1
%nonassoc AT OLD
%left OP2 MINUS
%left OP3
%left OP4
%nonassoc prec_prefix_op
%nonassoc INTEGER REAL (* stronger than MINUS *)
%nonassoc LEFTSQ
%nonassoc OPPREF

(* Entry points *)

%start <Why3.Ptree.term> term_eof
%start <Why3.Ptree.qualid> qualid_eof
%start <Why3.Ptree.qualid list> qualid_comma_list_eof
%start <Why3.Ptree.term list> term_comma_list_eof
%start <Why3.Ptree.ident list> ident_comma_list_eof

%%

(* parsing of a single term or a single decl *)

term_eof:
| term EOF { $1 }

(* Type expressions *)

ty:
| ty_arg          { $1 }
| lqualid ty_arg+ { PTtyapp ($1, $2) }
| ty ARROW ty     { PTarrow ($1, $3) }

ty_arg:
| qualid                            { PTtyapp ($1, []) }
| quote_lident                      { PTtyvar $1 }
| ty_block                          { $1 }

ty_block:
| LEFTPAR comma_list2(ty) RIGHTPAR  { PTtuple $2 }
| LEFTPAR RIGHTPAR                  { PTtuple [] }
| LEFTPAR ty RIGHTPAR               { PTparen $2 }
| LEFTBRC ty RIGHTBRC               { PTpure $2 }

cast:
| COLON ty  { $2 }

(* Parameters and binders *)

(* [param] and [binder] below must have the same grammar
   and raise [Error] in the same cases. Interpretaion of
   single-standing untyped [Qident]'s is different: [param]
   treats them as type expressions, [binder], as parameter
   names, whose type must be inferred. *)

binders: binder+ { List.concat $1 }

binder:
| special_binder
    { let l,i = $1 in [l, i, false, None] }
| lident_nq attr+
    { [floc $startpos $endpos, Some (add_attr $1 $2), false, None] }
| ty_arg
    { match $1 with
      | PTparen (PTtyapp (Qident {id_str="ref"}, [PTtyapp (Qident id, [])])) ->
              [floc $startpos $endpos, binder_of_id (set_ref id), false, None]
      | PTtyapp (Qident id, [])
      | PTparen (PTtyapp (Qident id, [])) ->
              [floc $startpos $endpos, binder_of_id id, false, None]
      | _ ->  [floc $startpos $endpos, None, false, Some $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { match $3 with
      | PTtyapp (Qident {id_str="ref"}, [PTtyapp (Qident id, [])]) ->
              [floc $startpos $endpos, binder_of_id (set_ref id), true, None]
      | PTtyapp (Qident id, []) ->
              [floc $startpos $endpos, binder_of_id id, true, None]
      | _ ->  [floc $startpos $endpos, None, true, Some $3] }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match snd $2 with [l,i] -> [l, set_ref_opt l (fst $2) i, false, None]
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match snd $3 with [l,i] -> [l, set_ref_opt l (fst $3) i, true, None]
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { let r = fst $2 in let ty = if r then PTref [$3] else $3 in
      List.map (fun (l,i) -> l, set_ref_opt l r i, false, Some ty) (snd $2) }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { let r = fst $3 in let ty = if r then PTref [$4] else $4 in
      List.map (fun (l,i) -> l, set_ref_opt l r i, true, Some ty) (snd $3) }

binder_vars:
| binder_vars_head  { fst $1, match snd $1 with
                        | [] -> raise Error
                        | bl -> List.rev bl }
| binder_vars_rest  { $1 }

binder_vars_rest:
| binder_vars_head attr+ binder_var*
    { let l2 = floc $startpos($2) $endpos($2) in
      fst $1, List.rev_append (match snd $1 with
        | (l, Some id) :: bl ->
            (Loc.join l l2, Some (add_attr id $2)) :: bl
        | _ -> error_loc l2) $3 }
| binder_vars_head special_binder binder_var*
    { fst $1, List.rev_append (snd $1) ($2 :: $3) }
| special_binder binder_var*
    { false, $1 :: $2 }

binder_vars_head:
| ty {
    let of_id id = id.id_loc, binder_of_id id in
    let push acc = function
      | PTtyapp (Qident id, []) -> of_id id :: acc
      | _ -> raise Error in
    match $1 with
      | PTtyapp (Qident {id_str = "ref"}, l) ->
          true, List.fold_left push [] l
      | PTtyapp (Qident id, l) ->
          false, List.fold_left push [of_id id] l
      | _ -> raise Error }

binder_var:
| attrs(lident_nq)      { floc $startpos $endpos, Some $1 }
| special_binder        { $1 }

special_binder:
| UNDERSCORE            { floc $startpos $endpos, None }
| AMP attrs(lident_nq)  { floc $startpos $endpos, Some (set_ref $2) }

(* Logical terms *)

mk_term(X): d = X { mk_term d $startpos $endpos }

term:
| single_term %prec below_COMMA   { $1 }
| single_term COMMA term_
    { mk_term (Ttuple ($1::$3)) $startpos $endpos }

term_:
| single_term %prec below_COMMA   { [$1] }
| single_term COMMA term_         { $1::$3 }

single_term: t = mk_term(single_term_) { t }

single_term_:
| term_arg_
    { match $1 with (* break the infix relation chain *)
      | Tinfix (l,o,r) -> Tinnfix (l,o,r)
      | Tbinop (l,o,r) -> Tbinnop (l,o,r)
      | d -> d }
| NOT single_term
    { Tnot $2 }
| OLD single_term
    { Tat ($2, mk_id Dexpr.old_label $startpos($1) $endpos($1)) }
| single_term AT uident
    { Tat ($1, $3) }
| prefix_op single_term %prec prec_prefix_op
    { Tidapp (Qident $1, [$2]) }
| minus_numeral
    { Tconst $1 }
| l = single_term ; o = bin_op ; r = single_term
    { Tbinop (l, o, r) }
| l = single_term ; o = infix_op_1 ; r = single_term
    { Tinfix (l, o, r) }
| l = single_term ; o = infix_op_234 ; r = single_term
    { Tidapp (Qident o, [l; r]) }
| term_arg located(term_arg)+
    {
      let id_app = convert_array $1 in
      let join f (a,_,e) = mk_term (Tapply (f,a)) $startpos e in
      (List.fold_left join id_app $2).term_desc
    }
| IF term THEN term ELSE term
    { Tif ($2, $4, $6) }
| LET pattern EQUAL term IN term
    { let re_pat pat d = { pat with pat_desc = d } in
      let cast t ty = { t with term_desc = Tcast (t,ty) } in
      let rec unfold d p = match p.pat_desc with
        | Pparen p | Pscope (_,p) -> unfold d p
        | Pcast (p,ty) -> unfold (cast d ty) p
        | Ptuple [] -> unfold (cast d (PTtuple [])) (re_pat p Pwild)
        | Pvar id -> Tlet (id, d, $6)
        | Pwild -> Tlet (id_anonymous p.pat_loc, d, $6)
        | _ -> Tcase (d, [$2, $6]) in
      unfold $4 $2 }
| LET attrs(lident_op_nq) EQUAL term IN term
    { Tlet ($2, $4, $6) }
| LET attrs(lident_nq) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| LET attrs(lident_op_nq) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| MATCH term WITH match_cases(term) END
    { Tcase ($2, $4) }
| quant comma_list1(quant_vars) triggers DARROW term
    { let l = List.concat $2 in
      Tquant ($1, l, $3, $5) }
| quant comma_list1(quant_vars) triggers IN term DOTDOT term DARROW term
    { let l = List.concat $2 in
      match l with
      | [(_, Some v, _, _)] ->
         let ineq_and = create_in_range $5 $7 v in
         let impl = mk_term_loc (Tbinop (ineq_and, Dterm.DTimplies, $9)) ineq_and.term_loc in
         Tquant ($1, l, $3, impl)
      | _ -> assert false (* TODO make normal error here *)
    }
| FUN binders ARROW term
    { Tquant (Dterm.DTlambda, $2, [], $4) }
| attr single_term %prec prec_attr
    { Tattr ($1, $2) }
| single_term cast
    { Tcast ($1, $2) }

lam_defn:
| binders EQUAL term  { Tquant (Dterm.DTlambda, $1, [], $3) }

term_arg: mk_term(term_arg_) { $1 }
term_dot: mk_term(term_dot_) { $1 }

term_arg_:
| qualid                    { Tident $1 }
| qualid QUOTE qualid
    {
      (* In case of quote, if 'Last or 'First is detected, we understand it as
         the application of First to the term. Otherwise, we fall back to
         rebuilding an id with a QUOTE inside it. *)
      match $3, $1 with
      | Qident id3, Qident id1  ->
         (* TODO we could be more precise or clean here *)
         if Strings.has_prefix "First" id3.id_str ||
              Strings.has_prefix "Last" id3.id_str then
           Tidapp ($3, [mk_term_loc (Tident $1) id1.id_loc])
         else
           Tident (Qident (mk_id (id1.id_str ^ "'" ^ id3.id_str) $startpos $endpos))
      | _, _ -> assert false
    }
| AMP qualid                { Tasref $2 }
| numeral                   { Tconst $1 }
| TRUE                      { Ttrue }
| FALSE                     { Tfalse }
| o = oppref ; a = term_arg { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_dot_:
| qualid                    { Tident $1 }
| o = oppref ; a = term_dot { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_block_:
| BEGIN term END                                    { $2.term_desc }
| LEFTPAR term RIGHTPAR                             { $2.term_desc }
| BEGIN END                                         { Ttuple [] }
| LEFTPAR RIGHTPAR                                  { Ttuple [] }
| LEFTBRC field_list1(term) RIGHTBRC                { Trecord $2 }
| LEFTBRC term_arg WITH field_list1(term) RIGHTBRC  { Tupdate ($2,$4) }

term_sub_:
| term_block_                                       { $1 }
| term_dot DOT qualid                               { Tidapp ($3,[$1]) }
| term_arg LEFTSQ term rightsq
    { Tidapp (get_op $4 $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ term LARROW term rightsq
    { Tidapp (upd_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT term rightsq
    { Tidapp (cut_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT rightsq
    { Tidapp (rcut_op $5 $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ DOTDOT term rightsq
    { Tidapp (lcut_op $5 $startpos($2) $endpos($2), [$1;$4]) }

field_list1(X):
| fl = semicolon_list1(separated_pair(lqualid, EQUAL, X)) { fl }

match_cases(X):
| cl = bar_list1(match_case(X)) { cl }

match_case(X):
| mc = separated_pair(pattern, ARROW, X) { mc }

quant_vars:
| binder_var+ cast? { List.map (fun (l,i) -> l, i, false, $2) $1 }

triggers:
| (* epsilon *)                                                         { [] }
| LEFTSQ separated_nonempty_list(BAR,comma_list1(single_term)) RIGHTSQ  { $2 }

%inline bin_op:
| ARROW    { Dterm.DTimplies }
| LRARROW  { Dterm.DTiff }
| OR       { Dterm.DTor }
| OR ELSE  { Dterm.DTor_asym }
| AND      { Dterm.DTand }
| AND THEN { Dterm.DTand_asym }
| BY       { Dterm.DTby }
| SO       { Dterm.DTso }

quant:
| FOR ALL  { Dterm.DTforall }
| FOR SOME  { Dterm.DTexists }

minus_numeral:
| MINUS INTEGER { Constant.(ConstInt (Number.neg_int $2)) }
| MINUS REAL    { Constant.(ConstReal (Number.neg_real $2))}

numeral:
| INTEGER { Constant.ConstInt $1 }
| REAL    { Constant.ConstReal $1 }

(* Patterns *)

mk_pat(X): X { mk_pat $1 $startpos $endpos }

pattern: mk_pat(pattern_) { $1 }
pat_arg: mk_pat(pat_arg_) { $1 }

pattern_:
| pat_conj_                             { $1 }
| mk_pat(pat_conj_) BAR pattern         { Por ($1,$3) }

pat_conj_:
| pat_uni_                              { $1 }
| comma_list2(mk_pat(pat_uni_))         { Ptuple $1 }

pat_uni_:
| pat_arg_                              { $1 }
| uqualid pat_arg+                      { Papp ($1,$2) }
| GHOST mk_pat(pat_uni_)                { Pghost $2 }
| mk_pat(pat_uni_) AS boption(GHOST) var_binder
                                        { Pas ($1,$4,$3) }
| mk_pat(pat_uni_) cast                 { Pcast ($1,$2) }

pat_arg_:
| UNDERSCORE                            { Pwild }
| var_binder                            { Pvar $1 }
| uqualid                               { Papp ($1,[]) }
| pat_block_                            { $1 }

pat_block_:
| LEFTPAR RIGHTPAR                      { Ptuple [] }
| LEFTPAR pattern RIGHTPAR              { Pparen $2 }
| LEFTBRC field_list1(pattern) RIGHTBRC { Prec $2 }

(* One-variable binders *)

var_binder: (* pattern variables *)
|     attrs(lident_nq)    { $1 }
| AMP attrs(lident_nq)    { set_ref $2 }

(* Qualified idents *)

qualid:
| ident                   { Qident $1 }

uqualid:
| uident                  { Qident $1 }

lqualid:
| lident                  { Qident $1 }

(* Idents *)

ident:
| uident          { $1 }
| lident          { $1 }
| lident_op       { $1 }

uident:
| UIDENT          { mk_id $1 $startpos $endpos }
| CORE_UIDENT     { mk_id $1 $startpos $endpos }

lident:
| LIDENT          { mk_id $1 $startpos $endpos }
| lident_keyword  { mk_id $1 $startpos $endpos }
| CORE_LIDENT     { mk_id $1 $startpos $endpos }
| REF             { mk_id "ref" $startpos $endpos }
(* we don't put REF in lident_keyword, because we do not
   want it in lident_nq, not even with an error message.
   This avoids a conflict in "let ref x = ...". *)

lident_nq:
| LIDENT          { mk_id $1 $startpos $endpos }
| lident_keyword  { mk_id $1 $startpos $endpos }
| CORE_LIDENT     { let loc = floc $startpos($1) $endpos($1) in
                    Loc.errorm ~loc core_ident_error $1 }

lident_keyword:
| RANGE           { "range" }
| FLOAT           { "float" }

quote_lident:
| QUOTE_LIDENT    { mk_id $1 $startpos $endpos }

(* Symbolic operation names *)

lident_op:
| LEFTPAR lident_op_str RIGHTPAR
    { mk_id $2 $startpos($2) $endpos($2) }
| LEFTPAR lident_op_str RIGHTPAR_USCORE
    { mk_id ($2^$3) $startpos $endpos }
| LEFTPAR lident_op_str RIGHTPAR_QUOTE
    { mk_id ($2^$3) $startpos $endpos }

lident_op_nq:
| LEFTPAR lident_op_str RIGHTPAR
    { mk_id $2 $startpos($2) $endpos($2) }
| LEFTPAR lident_op_str RIGHTPAR_USCORE
    { mk_id ($2^$3) $startpos $endpos }
| LEFTPAR lident_op_str RIGHTPAR_QUOTE
    { let loc = floc $startpos $endpos in
      Loc.errorm ~loc "Symbol (%s)%s cannot be user-defined" $2 $3 }

lident_op_str:
| op_symbol                         { Ident.op_infix $1 }
| op_symbol UNDERSCORE              { Ident.op_prefix $1 }
| MINUS     UNDERSCORE              { Ident.op_prefix "-" }
| EQUAL                             { Ident.op_infix "=" }
| MINUS                             { Ident.op_infix "-" }
| OPPREF UNDERSCORE?                { Ident.op_prefix $1 }
| LEFTSQ rightsq                    { Ident.op_get $2 }
| LEFTSQ rightsq LARROW             { Ident.op_set $2 }
| LEFTSQ LARROW rightsq             { Ident.op_update $3 }
| LEFTSQ DOTDOT rightsq             { Ident.op_cut $3 }
| LEFTSQ UNDERSCORE DOTDOT rightsq  { Ident.op_rcut $4 }
| LEFTSQ DOTDOT UNDERSCORE rightsq  { Ident.op_lcut $4 }

rightsq:
| RIGHTSQ         { "" }
| RIGHTSQ_QUOTE   { $1 }

op_symbol:
| OP1 { $1 }
| OP2 { $1 }
| OP3 { $1 }
| OP4 { $1 }
| LT  { "<" }
| GT  { ">" }

%inline oppref:
| o = OPPREF { mk_id (Ident.op_prefix o)  $startpos $endpos }

prefix_op:
| op_symbol { mk_id (Ident.op_prefix $1)  $startpos $endpos }
| MINUS     { mk_id (Ident.op_prefix "-") $startpos $endpos }

%inline infix_op_1:
| o = OP1   { mk_id (Ident.op_infix o)    $startpos $endpos }
| EQUAL     { mk_id (Ident.op_infix "=")  $startpos $endpos }
| LTGT      { mk_id (Ident.op_infix "<>") $startpos $endpos }
| LT        { mk_id (Ident.op_infix "<")  $startpos $endpos }
| GT        { mk_id (Ident.op_infix ">")  $startpos $endpos }

%inline infix_op_234:
| o = OP2   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP3   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP4   { mk_id (Ident.op_infix o)    $startpos $endpos }
| MINUS     { mk_id (Ident.op_infix "-")  $startpos $endpos }

(* Attributes and position markers *)

attrs(X): X attr* { add_attr $1 $2 }

attr:
| ATTRIBUTE { ATstr (Ident.create_attribute $1) }
| POSITION  { ATpos $1 }

(* Miscellaneous *)

bar_list1(X):
| ioption(BAR) ; xl = separated_nonempty_list(BAR, X) { xl }

with_list1(X):
| separated_nonempty_list(WITH, X)  { $1 }

comma_list2(X):
| X COMMA comma_list1(X) { $1 :: $3 }

comma_list1(X):
| separated_nonempty_list(COMMA, X) { $1 }

comma_list0(X):
| xl = separated_list(COMMA, X) { xl }

semicolon_list1(X):
| x = X ; ioption(SEMICOLON)                  { [x] }
| x = X ; SEMICOLON ; xl = semicolon_list1(X) { x :: xl }

located(X): X { $1, $startpos, $endpos }

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
