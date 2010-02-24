
open Format
open Pp
open Term

(** Error reporting *)

type error = 
  | UnboundNamespace of string
  | OpenTheory
  | CloseTheory
  | NoOpenedTheory
  | NoOpenedNamespace

exception Error of error

let error e = raise (Error e)

(** The environment type *)

module M = Map.Make(String)

type namespace = {
  tysymbols : tysymbol M.t;  (* type symbols *)
  fsymbols  : fsymbol M.t;   (* function symbols *)
  psymbols  : psymbol M.t;   (* predicate symbols *)
  namespace : namespace M.t;      
}

type decl = 
  unit (* TODO *)

type theory = {
  th_ns   : namespace;
  th_decl : decl list;
}

type t = {
  loadpath : string list;
  theories : theory M.t;
  ns_stack : (namespace * namespace) list; (* stack of imports/exports *)
}

(** Creating environments *)

let empty_ns = {
  tysymbols = M.empty;
  fsymbols  = M.empty;
  psymbols  = M.empty;
  namespace = M.empty;
}

let is_empty_ns ns =
  M.is_empty ns.tysymbols &&
  M.is_empty ns.fsymbols  &&
  M.is_empty ns.psymbols  &&
  M.is_empty ns.namespace

let create lp = {
  loadpath = lp;
  theories = M.empty;
  ns_stack = [];
}

let open_theory t = match t.ns_stack with
  | [] -> { t with ns_stack = [empty_ns, empty_ns] }
  | _  -> error OpenTheory
  
let close_theory t s = match t.ns_stack with
  | [_, e] -> 
      let th = { th_ns = e; th_decl = [] (* TODO *) } in
      { t with theories = M.add s th t.theories }
  | _ -> 
      error CloseTheory

let open_namespace t = match t.ns_stack with
  | (i, _) :: _ as st ->
      { t with ns_stack = (i, empty_ns) :: st }
  | [] ->
      error NoOpenedTheory

let close_namespace t s = match t.ns_stack with
  | (_, e0) :: (i, e) :: st ->
      let add ns = { ns with namespace = M.add s e0 ns.namespace } in
      { t with ns_stack = (add i, add e) :: st }
  | [_] ->
      error NoOpenedNamespace
  | [] ->
      error NoOpenedTheory

let add_tysymbol x ty env = { env with tysymbols = M.add x ty env.tysymbols }
let add_fsymbol x ty env = { env with fsymbols = M.add x ty env.fsymbols }
let add_psymbol x ty env = { env with psymbols = M.add x ty env.psymbols }

(* let self_id = "(\*self*\)" *)
(* let self env = M.find self_id env.theories *)
(* let empty = { empty_env with theories = M.add self_id empty_env M.empty } *)

(* let add_self f x v env = *)
(*   f x v { env with theories = *)
(*       M.add self_id (f x v (self env)) env.theories } *)

(* let add_tysymbol = add_self add_tysymbol *)
(* let add_fsymbol  = add_self add_fsymbol *)
(* let add_psymbol  = add_self add_psymbol *)
(* let add_theory   = add_self add_theory *)

(** Querying environments *)

let ns env = match env.ns_stack with
  | (ns, _) :: _ -> ns
  | [] -> error NoOpenedTheory

let find_tysymbol s env = M.find s env.tysymbols
let find_fsymbol s env = M.find s env.fsymbols
let find_psymbol s env = M.find s env.psymbols

type path =
  | Pident of string
  | Pdot of path * string

let find_local_namespace s env = 
  try M.find s env.namespace
  with Not_found -> error (UnboundNamespace s)

let rec find_namespace q env = match q with
  | Pident t -> find_local_namespace t env
  | Pdot (q, t) -> let env = find_namespace q env in find_local_namespace t env

let rec find f q env = match q with
  | Pident x -> f x env
  | Pdot (m, x) -> let env = find_namespace m env in f x env

let find_tysymbol p env = find find_tysymbol p (ns env)


(** Error reporting *)

let report fmt = function
  | UnboundNamespace s ->
      fprintf fmt "unbound namespace %s" s
  | OpenTheory ->
      fprintf fmt "cannot open a new theory in a non-empty context"
  | CloseTheory ->
      fprintf fmt "cannot close theory: there are still unclosed namespaces"
  | NoOpenedTheory ->
      fprintf fmt "no opened theory"
  | NoOpenedNamespace ->
      fprintf fmt "no opened namespace"

(** Debugging *)

let rec print_env fmt env =
  fprintf fmt "@[<hov 2>types: ";
  M.iter (fun x ty -> fprintf fmt "%s -> %a;@ " x Name.print ty.Ty.ts_name)
    env.tysymbols;
  fprintf fmt "@]@\n@[<hov 2>function symbols: ";
  M.iter (fun x s -> fprintf fmt "%s -> %a;@ " x Name.print s.fs_name)
    env.fsymbols;
  fprintf fmt "@]@\n@[<hov 2>predicate symbols: ";
  M.iter (fun x s -> fprintf fmt "%s -> %a;@ " x Name.print s.ps_name)
    env.psymbols;
  fprintf fmt "@]@\n@[<hov 2>namespace: ";
  M.iter (fun x th -> fprintf fmt "%s -> [@[%a@]];@ " x print_env th)
    env.namespace;
  fprintf fmt "@]"

let print fmt t =
  print_env fmt (ns t)

(*
Local Variables: 
compile-command: "make -C .. test"
End: 
*)
