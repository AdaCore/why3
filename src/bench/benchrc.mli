

(**

[probs "myprobs"]
   file = "examples/monbut.why" #relatives to the rc file
   file = "examples/monprogram.mlw"
   theory = "monprogram.T"
   goal = "monbut.T.G"

   transform = "split_goal" #applied in the order
   transform = "..."
   transform = "..."

[tools "mytools"]
prover = cvc3
prover = altergo
#or only one
driver = "..."
command = "..."

loadpath = "..." #added to the one in why.conf
loadpath = "..."

timelimit = 30
memlimit = 300

use = "toto.T" #use the theory toto (allow to add metas)

transform = "simplify_array" #only 1 to 1

[bench "mybench"]
tools = "mytools"
tools = ...
probs = "myprobs"
probs = ...
output = "csv"
output = "average"
output = "timeline"
*)

open Bench
open Why
open Util


type id_tool = (string * string)
(* tool_name, prover_name *)

type id_prob = (string * string * string)
(* prob_name, file_name, theory name *)

type benchrc = { tools : id_tool tool list Mstr.t;
                 probs : id_prob prob Mstr.t;
                 benchs : (id_tool,id_prob) bench Mstr.t
               }

val read_file : Whyconf.config -> string -> benchrc
