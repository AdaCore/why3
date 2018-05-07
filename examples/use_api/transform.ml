

open Why3

(* push negations down *)

(* BEGIN{negate} *)
open Term

let rec negate (t:term) : term =
  match t.t_node with
  | Ttrue -> t_false
  | Tfalse -> t_true
  | Tnot t -> t
  | Tbinop(Tand,t1,t2) -> t_and (negate t1) (negate t2)
  | Tbinop(Tor,t1,t2) -> t_or (negate t1) (negate t2)
  | Tquant(Tforall,tq) ->
     let vars,triggers,t' = t_open_quant tq in
     let tq' = t_close_quant vars triggers (negate t') in
     t_exists tq'
  | Tquant(Texists,tq) ->
     let vars,triggers,t' = t_open_quant tq in
     let tq' = t_close_quant vars triggers (negate t') in
     t_forall tq'
  | _ -> t_not t

let traverse (t:term) : term = t_map negate t
(* END{negate} *)

(* BEGIN{register} *)
let negate_goal pr t = [Decl.create_prop_decl Decl.Pgoal pr (traverse t)]

let negate_trans = Trans.goal negate_goal

let () = Trans.register_transform
           "push_negation_down" negate_trans
           ~desc:"In the current goal, push negation down, across logical connectives."
(* END{register} *)
