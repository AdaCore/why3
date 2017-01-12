(****************************************************************************)
(* This is extracted/adapted from the code found in the book Real World Ocaml
by Yaron Minsky, Anil Madhavapeddy, and Jason Hickey. Their 'unlicence' allows
it. *)
(****************************************************************************)
%start <Json.value> json_object
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token TRUE
%token FALSE
%token LEFTBRC RIGHTBRC
%token LEFTSQ
%token RIGHTSQ
%token COLON
%token COMMA
%token EOF
%%

json_object:
| EOF { Json.Null }
| LEFTBRC RIGHTBRC { Json.Null }
(* Left recursive rule are more efficient *)
| LEFTBRC members RIGHTBRC { Json.Obj (List.rev $2) }

members:
| json_pair { [ $1 ] }
| members COMMA json_pair { $3 :: $1 }

array:
| LEFTSQ RIGHTSQ { Json.Array [] }
| LEFTSQ elements RIGHTSQ { Json.Array (List.rev $2) }

elements:
| value { [$1] }
| elements COMMA value { $3 :: $1 }

json_pair:
| STRING COLON value { ($1, $3) }

value:
| STRING { Json.String $1 }
| INT { Json.Int $1 }
| FLOAT { Json.Float $1 }
| json_object { $1 }
| array { $1 }
| TRUE { Json.Bool true}
| FALSE { Json.Bool false }
