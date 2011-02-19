

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
timeline = "prgbench.time"
average = "prgbench.avg"
csv = "prgbench.csv"
*)

open Bench
open Why
open Util


type benchrc = { tools : tool list Mstr.t;
                 probs : prob list Mstr.t;
                 benchs : bench Mstr.t
               }

val read_file : Whyconf.config -> string -> benchrc


val gen_from_file :
  format:string option ->
  prob_name:string ->
  file_path:string ->
  file_name:string ->
  Bench.gen_task
