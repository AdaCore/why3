" Vim syntax file
" Language:     Why3
" Filenames:    *.why *.mlw
"
" Adapted from syntax file for Ocaml

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "why3"
  finish
endif

" Why3 is case sensitive.
syn case match

" " Script headers highlighted like comments
" syn match    whyComment   "^#!.*"

" lowercase identifier - the standard way to match
syn match    whyLCIdentifier /\<\(\l\|_\)\(\w\|'\)*\>/

syn match    whyKeyChar    "|"

" Errors
syn match    whyBraceErr   "}"
syn match    whyBrackErr   "\]"
syn match    whyParenErr   ")"

syn match    whyCommentErr "\*)"

syn match    whyCountErr   "\<downto\>"
syn match    whyCountErr   "\<to\>"

syn match    whyDoErr      "\<do\>"
syn match    whyDoneErr    "\<done\>"
syn match    whyThenErr    "\<then\>"
syn match    whyTheoryErr  "\<theory\>"
syn match    whyModuleErr  "\<module\>"
syn match    whyEndErr     "\<end\>"

" Some convenient clusters
syn cluster  whyAllErrs contains=whyBraceErr,whyBrackErr,whyParenErr,whyCommentErr,whyCountErr,whyDoErr,whyDoneErr,whyEndErr,whyThenErr,whyTheoryErr,whyModuleErr

syn cluster  whyContained contains=whyTodo,whyImport,whyExport,whyTheoryContents,whyModuleContents,whyScopeContents,whyModuleKeyword
" ,whyPreDef,whyModParam,whyModParam1,whyPreMPRestr,whyMPRestr,whyMPRestr1,whyMPRestr2,whyMPRestr3,whyModRHS,whyFuncWith,whyFuncStruct,whyModTypeRestr,whyModTRWith,whyWith,whyWithRest,whyModType,whyFullMod,whyVal

" Enclosing delimiters
syn region   whyEncl transparent matchgroup=whyKeyChar start="(" matchgroup=whyKeyChar end=")" contains=ALLBUT,@whyContained,whyParenErr
syn region   whyEncl transparent matchgroup=whyKeyChar start="{" matchgroup=whyKeyChar end="}"  contains=ALLBUT,@whyContained,whyBraceErr
syn region   whyEncl transparent start="\[" end="\]" contains=ALLBUT,@whyContained,whyBrackErr

" Comments
syn region   whyComment start="(\*" end="\*)" contains=whyComment,whyTodo
syn match    whyOperator "(\*)"

syn keyword  whyTodo contained TODO FIXME XXX NOTE

" Blocks
" FIXME? match and try should detect the absence of "with" ?
syn region   whyEnd matchgroup=whyKeyword start="\<begin\>" matchgroup=whyKeyword end="\<end\>" contains=ALLBUT,@whyContained,whyEndErr
syn region   whyEnd matchgroup=whyKeyword start="\<match\>" matchgroup=whyKeyword end="\<end\>" contains=ALLBUT,@whyContained,whyEndErr
syn region   whyEnd matchgroup=whyKeyword start="\<try\>" matchgroup=whyKeyword end="\<end\>" contains=ALLBUT,@whyContained,whyEndErr
syn region   whyNone matchgroup=whyKeyword start="\<for\>" matchgroup=whyKeyword end="\<\(to\|downto\)\>" contains=ALLBUT,@whyContained,whyCountErr
syn region   whyDo matchgroup=whyKeyword start="\<do\>" matchgroup=whyKeyword end="\<done\>" contains=ALLBUT,@whyContained,whyDoneErr
syn region   whyNone matchgroup=whyKeyword start="\<if\>" matchgroup=whyKeyword end="\<then\>" contains=ALLBUT,@whyContained,whyThenErr

" Theories and modules

syn region   whyTheory matchgroup=whyKeyword start="\<theory\>" matchgroup=whyModSpec end="\<\u\(\w\|'\)*\>" contains=@whyAllErrs,whyComment skipwhite skipempty nextgroup=whyModuleContents
syn region   whyModule matchgroup=whyKeyword start="\<module\>" matchgroup=whyModSpec end="\<\u\(\w\|'\)*\>" contains=@whyAllErrs,whyComment skipwhite skipempty nextgroup=whyModuleContents
syn region   whyScope matchgroup=whyKeyword start="\<scope\>" matchgroup=whyModSpec end="\<\u\(\w\|'\)*\>" contains=@whyAllErrs,whyComment,whyImport skipwhite skipempty nextgroup=whyModuleContents

syn region   whyModuleContents start="" matchgroup=whyModSpec end="\<end\>" contained contains=ALLBUT,@whyContained,whyEndErr,whyTheory,whyModule

syn region   whyNone matchgroup=whyKeyword start="\<\(use\|clone\)\>" matchgroup=whyModSpec end="\<\(\w\+\.\)*\u\(\w\|'\)*\>" contains=@whyAllErrs,whyComment,whyString,whyImport,whyExport
syn keyword  whyExport contained export
syn keyword  whyImport contained import

syn region   whyNone matchgroup=whyKeyword start="\<import\>" matchgroup=whyModSpec end="\<\(\u\(\w\|'\)*\.\)*\u\(\w\|'\)*\>" contains=@whyAllErrs,whyComment

syn region   whyNone matchgroup=whyKeyword start="\<\(axiom\|lemma\|goal\)\>" matchgroup=whyNone end="\<\w\(\w\|'\)\>\|" contains=@whyAllErrs,whyComment

syn keyword  whyKeyword  abstract any as break by
syn keyword  whyKeyword  coinductive constant continue
syn keyword  whyKeyword  else epsilon exists exception
syn keyword  whyKeyword  forall fun function ghost
syn keyword  whyKeyword  if in inductive
syn keyword  whyKeyword  label let
syn keyword  whyKeyword  meta model mutable not
syn keyword  whyKeyword  partial predicate private
syn keyword  whyKeyword  raise rec return so then type
syn keyword  whyKeyword  val while with

syn keyword  whyBoolean  true false

syn keyword  whyType     bool float int list map option real range
syn keyword  whyType     array ref unit

syn keyword  whySpec     absurd alias assert assume check diverges ensures invariant
syn keyword  whySpec     pure raises reads requires returns variant writes at old

syn match    whyConstructor  "(\s*)"
syn match    whyConstructor  "\u\(\w\|'\)*\>"
syn match    whyModPath      "\u\(\w\|'\)*\."he=e-1

syn region   whyString       start=+"+ skip=+\\\\\|\\"+ end=+"+

syn match    whyOperator     "->"
syn match    whyOperator     "<->\?"
syn match    whyOperator     "/\\"
syn match    whyOperator     "\\/"
syn match    whyOperator     "&&"
syn match    whyOperator     "<>"
syn match    whyKeyChar      "|"
syn match    whyKeyChar      ";"
" FIXME? is this too inefficient?
syn match    whyOperator     "[^<>~=:+*/%$&@^.|#!?]=[^<>~=:+*/%$&@^.|#!?]"ms=s+1,me=e-1
syn match    whyOperator                         "^=[^<>~=:+*/%$&@^.|#!?]"me=e-1
syn match    whyOperator     "[^<>~=:+*/%$&@^.|#!?]=$"ms=s+1

syn match    whyAnyVar       "\<_\>"

syn match    whyNumber        "\<-\=\d\(_\|\d\)*\>"
syn match    whyNumber        "\<-\=0[x|X]\(\x\|_\)\+\>"
syn match    whyNumber        "\<-\=0[o|O]\(\o\|_\)\+\>"
syn match    whyNumber        "\<-\=0[b|B]\([01]\|_\)\+\>"
syn match    whyFloat         "\<-\=\d\+[eE][-+]\=\d\+\>"
syn match    whyFloat         "\<-\=\d\+\.\d*\([eE][-+]\=\d\+\)\=\>"
syn match    whyFloat         "\<-\=0[x|X]\x\+\.\?\x*[pP][-+]\=\d\+\>"

" Synchronization
syn sync minlines=50
syn sync maxlines=500

syn sync match whyDoSync      grouphere  whyDo      "\<do\>"
syn sync match whyDoSync      groupthere whyDo      "\<done\>"

syn sync match whyEndSync     grouphere  whyEnd     "\<\(begin\|match\|try\)\>"
syn sync match whyEndSync     groupthere whyEnd     "\<end\>"

syn sync match whyTheorySync  grouphere  whyTheory  "\<theory\>"
syn sync match whyTheorySync  groupthere whyTheory  "\<end\>"

syn sync match whyModuleSync  grouphere  whyModule  "\<module\>"
syn sync match whyModuleSync  groupthere whyModule  "\<end\>"

syn sync match whyScopeSync   grouphere  whyScope   "\<scope\>"
syn sync match whyScopeSync   groupthere whyScope   "\<end\>"

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_why_syntax_inits")
  if version < 508
    let did_why_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink whyBraceErr	   Error
  HiLink whyBrackErr	   Error
  HiLink whyParenErr	   Error
  HiLink whyCommentErr     Error
  HiLink whyCountErr	   Error
  HiLink whyDoErr	   Error
  HiLink whyDoneErr	   Error
  HiLink whyEndErr	   Error
  HiLink whyThenErr	   Error
  HiLink whyTheoryErr	   Error
  HiLink whyModuleErr	   Error

  HiLink whyComment	   Comment

  HiLink whyModPath	   Include
  HiLink whyModSpec	   Include
  HiLink whyImport	   Keyword
  HiLink whyExport	   Keyword
  HiLink whyModuleKeyword  Keyword

  HiLink whyConstructor    Constant

  HiLink whyKeyword	   Keyword
  HiLink whyKeyChar	   Operator
  HiLink whyAnyVar	   Operator
  HiLink whyOperator	   Operator
  HiLink whySpec	   Identifier

  HiLink whyNumber	   Number
  HiLink whyFloat	   Float
  HiLink whyString	   String
  HiLink whyBoolean	   Boolean

  HiLink whyType	   Type

  HiLink whyTodo	   Todo

  HiLink whyEncl	   Keyword

  delcommand HiLink
endif

let b:current_syntax = "why3"

" vim: ts=8
