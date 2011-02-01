(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Bench
open Why
open Util
open Theory


type id_tool = (string * string)
type id_prob = (string * string * string)

type benchrc = { tools : id_tool tool list Mstr.t;
                 probs : id_prob prob list Mstr.t;
                 benchs : (id_tool,id_prob) bench Mstr.t
               }

open Whyconf
open Rc

let absolute_filename dirname f =
  if f = "-" then f else
  if Filename.is_relative f then
    Filename.concat dirname f
  else
    f

let read_tools absf wc map (name,section) =
  (* loadpath *)
  let wc_main = get_main wc in
  let loadpath = get_stringl ~default:[] section "loadpath" in
  let loadpath = List.append loadpath (Whyconf.loadpath wc_main) in
  (* limit *)
  let timelimit = get_int ~default:(timelimit wc_main) section "timelimit" in
  let memlimit = get_int ~default:(memlimit wc_main) section "memlimit" in
  (* env *)
  let env = Lexer.create_env loadpath in
  (* transformations *)
  let transforms = get_stringl ~default:[] section "transform" in
  let lookup acc t = Trans.compose (Trans.lookup_transform t env) acc in
  let transforms = List.fold_left lookup Trans.identity transforms
  in
  (* use *)
  let use = get_stringl ~default:[] section "use" in
  let load_use task s =
    let file,th = match Util.split_string_rev s '.' with
      | [] | [_] -> eprintf "Bad theory qualifier %s" s; exit 1
      | a::l -> List.rev l,a in
    let th = Env.find_theory env file th in
    Task.use_export task th in
  let use = List.fold_left load_use None use in
  (* provers *)
  let provers = get_stringl ~default:[] section "prover" in
  let find_provers s =
    try let p = Mstr.find s (get_provers wc) in
        s,p.driver ,p.command
    with
      (* TODO add exceptions pehaps inside rc.ml in fact*)
      | Not_found -> eprintf "Prover %s not found.@." s; exit 1 in
  let provers = List.map find_provers provers in
  let provers =
    try
      let driver = get_string section "driver" in
      let command = get_string section "command" in
      ("driver",absf driver,command) :: provers
    with MissingField _ -> provers in
  let load_driver (n,d,c) = n,Driver.load_driver env d,c in
  let provers = List.map load_driver provers in
  let create_tool (n,driver,command) =
    { tval = name,n ;
      ttrans = transforms;
      tdriver = driver;
      tcommand = command;
      tenv = env;
      tuse = use;
      ttime = timelimit;
      tmem = memlimit
    } in
  Mstr.add name (List.map create_tool provers) map

let read_probs absf map (name,section) =
  (* transformations *)
  let transforms = get_stringl ~default:[] section "transform" in
  let gen_trans env =
    let lookup acc t = Trans.compose_l
      (try Trans.singleton (Trans.lookup_transform t env) with
          Trans.UnknownTrans _ -> Trans.lookup_transform_l t env) acc
    in
    let transforms = List.fold_left lookup Trans.identity_l transforms in
    transforms
  in
  (* format *)
  let format = get_stringo section "format" in
  (* files *)
  let files = get_stringl ~default:[] section "file" in
  let gen fname env task =
    try
      let read_one fname =
        let cin = open_in (absf fname) in
        let m = Env.read_channel ?format:format env fname cin in
        close_in cin;
        let ths = Mnm.bindings m in
        List.rev_map (fun (n,th) -> ((name,fname,n),th)) ths
      in
      let map (name,th) = name,Task.split_theory th None task in
      let fold acc (n,l) =
        List.rev_append (List.rev_map (fun v -> (n,v)) l) acc in
      read_one fname |> List.rev_map map |> List.fold_left fold []
    with exn -> eprintf "%a@." Exn_printer.exn_printer exn; exit 1
  in
  Mstr.add name
    (List.rev_map
       (fun file -> { ptask   = gen file; ptrans   = gen_trans}) files)
    map

let read_bench absf mtools mprobs map (name,section) =
  let tools = get_stringl section "tools" in
  let lookup s =
    try Mstr.find s mtools
    with Not_found -> eprintf "Undefined tools %s@." s;
      exit 1 in
  let tools = list_flatten_rev (List.map lookup tools) in
  let probs = get_stringl section "probs" in
  let lookup s =
    try Mstr.find s mprobs
    with Not_found -> eprintf "Undefined probs %s@." s;
      exit 1 in
  let probs = list_flatten_rev (List.map lookup probs) in
  let averages = get_stringl ~default:[] section "average" in
  let outputs = List.fold_left
    (cons (fun s -> Average (absf s)))
    [] averages in
  let timelines = get_stringl ~default:[] section "timeline" in
  let outputs = List.fold_left
    (cons (fun s -> Timeline (absf s)))
    outputs timelines in
  let csvs = get_stringl ~default:[] section "csv" in
  let outputs = List.fold_left
    (cons (fun s -> Csv (absf s)))
    outputs csvs in
  Mstr.add name
    { bname = name; btools = tools; bprobs = probs; boutputs = outputs} map


let read_file wc f =
  let rc = from_file f in
  let absf = absolute_filename (Filename.dirname f) in
  let tools = get_family rc "tools" in
  let tools = List.fold_left (read_tools absf wc) Mstr.empty tools in
  let probs = get_family rc "probs" in
  let probs = List.fold_left (read_probs absf) Mstr.empty probs in
  let benchs = get_family rc "bench" in
  let benchs = List.fold_left (read_bench absf tools probs)
    Mstr.empty benchs in
  {tools = tools;
   probs = probs;
   benchs = benchs}
