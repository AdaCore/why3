(****************************************************************************)
(* This is extracted/adapted from the code found in the book Real World Ocaml
by Yaron Minsky, Anil Madhavapeddy, and Jason Hickey. Their 'unlicence' allows
it. *)
(****************************************************************************)
%start <Json_util.json_object> json_object
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
| EOF { Json_util.Empty }
| LEFTBRC RIGHTBRC { Json_util.Empty }
(* Left recursive rule are more efficient *)
| LEFTBRC members RIGHTBRC { Json_util.Assoc (List.rev $2) }

members:
| json_pair { [ $1 ] }
| members COMMA json_pair { $3 :: $1 }

array:
| LEFTSQ RIGHTSQ { Json_util.Array [] }
| LEFTSQ elements RIGHTSQ { Json_util.Array (List.rev $2) }

elements:
| value { [$1] }
| elements COMMA value { $3 :: $1 }

json_pair:
| STRING COLON value { ($1, $3) }

value:
| STRING { Json_util.String $1 }
| INT { Json_util.Int $1 }
| FLOAT { Json_util.Float $1 }
| json_object { $1 }
| array { $1 }
| TRUE { Json_util.Bool true}
| FALSE { Json_util.Bool false }
