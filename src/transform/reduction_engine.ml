
open Term

type rule = vsymbol list * term list * term
type engine = rule list Mls.t


(*

  A configuration is a pair (t,s) where t is a stack of terms and s is a
  stack of function symbols.

  A configuration ([t1;..;tn],[f1;..;fk]) represents a whole term, its
  model, as defined recursively by

    model([t],[]) = t

    model(t1::..::tn::t,f::s) = model(f(t1,..,tn)::t,s)
      where f as arity n

  A given term can be "exploded" into a configuration by reversing the
  rules above

  During reduction, the terms in the first stack are kept in normal
  form. The normalization process can be defined as the repeated
  application of the following rules.

  ([t],[]) --> t  // t is in normal form

  if f(t1,..,tn) is not a redex then
  (t1::..::tn::t,f::s) --> (f(t1,..,tn)::t,s)

  if f(t1,..,tn) is a redex l sigma for a rule l -> r then
  (t1::..::tn::t,f::s) --> (subst(sigma) @ t,explode(r) @ s)




*)

type value =
| Term of term    (* invariant: is in normal form *)
(* TODO, for optimization
| Int of BigInt.t
*)

type substitution = term Mvs.t

type cont =
| Kapp of lsymbol * Ty.ty option
| Kif of term * term * substitution
| Klet of vsymbol * term * substitution
| Kcase of term_branch list * substitution
| Keps of vsymbol
| Kquant of quant * vsymbol list * trigger
| Kbinop of binop
| Knot
| Keval of term * substitution

type config = {
  value_stack : value list;
  cont_stack : cont list;
}


exception NoMatch

let first_order_matching (vars : Svs.t) (largs : term list)
    (args : term list) : substitution =
  let rec loop sigma largs args =
    match largs,args with
      | [],[] -> sigma
      | t1::r1, t2::r2 ->
        begin
(*
          Format.eprintf "matching terms %a and %a...@."
            Pretty.print_term t1 Pretty.print_term t2;
*)
          match t1.t_node with
            | Tvar vs when Svs.mem vs vars ->
              begin
                try let t = Mvs.find vs sigma in
                    if t_equal t t2 then
                      loop sigma r1 r2
                    else
                      raise NoMatch
                with Not_found ->
                  loop (Mvs.add vs t2 sigma) r1 r2
              end
            | Tapp(ls1,args1) ->
              begin
                match t2.t_node with
                  | Tapp(ls2,args2) when ls_equal ls1 ls2 ->
                    loop sigma (List.rev_append args1 r1)
                      (List.rev_append args2 r2)
                  | _ -> raise NoMatch
              end
            | _ ->
(*
              Format.eprintf "are these terms equal ?...";
*)
              if t_equal t1 t2 then
                begin
(*
                  Format.eprintf " yes!@.";
*)
                  loop sigma r1 r2
                end
              else
                begin
(*
                  Format.eprintf " no@.";
*)
                  raise NoMatch
                end
        end
      | _ -> raise NoMatch
  in
  loop Mvs.empty largs args



exception Undetermined

let rec matching sigma t p =
  match p.pat_node with
  | Pwild -> sigma
  | Pvar v -> Mvs.add v t sigma
  | Por(p1,p2) ->
    begin
      try matching sigma t p1
      with NoMatch -> matching sigma t p2
    end
  | Pas(p,v) -> matching (Mvs.add v t sigma) t p
  | Papp(ls1,pl) ->
    match t.t_node with
      | Tapp(ls2,tl) ->
        if ls_equal ls1 ls2 then
          List.fold_left2 matching sigma tl pl
        else
          if ls2.ls_constr > 0 then raise NoMatch
          else raise Undetermined
      | _ -> raise Undetermined




let rec reduce engine c =
  match c.value_stack, c.cont_stack with
  | _, [] -> assert false
  | st, Keval (t,sigma) :: rem -> reduce_eval st t sigma rem
  | [], Kif _ :: _ -> assert false
  | v :: st, Kif(t2,t3,sigma) :: rem ->
    begin
      match v with
      | Term { t_node = Ttrue } ->
        { value_stack = st ;
          cont_stack = Keval(t2,sigma) :: rem }
      | Term { t_node = Tfalse } ->
        { value_stack = st ;
          cont_stack = Keval(t3,sigma) :: rem }
      | Term t1 ->
        { value_stack =
            Term (t_if t1 (t_subst sigma t2) (t_subst sigma t3)) :: st;
          cont_stack = rem ;
        }
(* TODO
      | Int _ -> assert false (* would be ill-typed *)
*)
    end
  | [], Klet _ :: _ -> assert false
  | (Term t1) :: st, Klet(v,t2,sigma) :: rem ->
    { value_stack = st;
      cont_stack = Keval(t2, Mvs.add v t1 sigma) :: rem;
    }
  | [], Kcase _ :: _ -> assert false
  | (Term t1) :: st, Kcase(tbl,sigma) :: rem ->
    reduce_match st t1 tbl sigma rem
  | ([] | [_]), Kbinop _ :: _ -> assert false
  | (Term t1) :: (Term t2) :: st, Kbinop op :: rem ->
    { value_stack = Term (t_binary_simp op t1 t2) :: st;
      cont_stack = rem;
    }
  | [], Knot :: _ -> assert false
  | (Term t) :: st, Knot :: rem ->
    { value_stack = Term (t_not t) :: st;
      cont_stack = rem;
    }
  | st, Kapp(ls,ty) :: rem ->
    reduce_app st ls ty rem
  | [], Keps _ :: _ -> assert false
  | Term t :: st, Keps v :: rem ->
    { value_stack = Term (t_eps_close v t) :: st;
      cont_stack = rem;
    }
  | [], Kquant _ :: _ -> assert false
  | Term t :: st, Kquant(q,vl,tr) :: rem ->
    { value_stack = Term (t_quant_close q vl tr t) :: st;
      cont_stack = rem;
    }

and reduce_match st u tbl sigma cont =
  let rec iter tbl =
    match tbl with
    | [] -> assert false (* pattern matching not exhaustive *)
    | b::rem ->
      let p,t = t_open_branch b in
      try
        let sigma' = matching sigma u p in
        { value_stack = st;
          cont_stack = Keval(t,sigma') :: cont;
        }
      with NoMatch -> iter rem
  in
  try iter tbl with Undetermined ->
    { value_stack = Term (t_case u tbl) :: st;
      cont_stack = cont;
    }


and reduce_eval st t sigma rem =
  match t.t_node with
  | Tvar v ->
    begin
      try
        let t = Mvs.find v sigma in
        { value_stack = Term t :: st ;
          cont_stack = rem;
        }
      with Not_found -> assert false
    end
  | Tif(t1,t2,t3) ->
    { value_stack = st;
      cont_stack = Keval(t1,sigma) :: Kif(t2,t3,sigma) :: rem;
    }
  | Tlet(t1,tb) ->
    let v,t2 = t_open_bound tb in
    { value_stack = st ;
      cont_stack = Keval(t1,sigma) :: Klet(v,t2,sigma) :: rem }
  | Tcase(t1,tbl) ->
    { value_stack = st;
      cont_stack = Keval(t1,sigma) :: Kcase(tbl,sigma) :: rem }
  | Tbinop(op,t1,t2) ->
    { value_stack = st;
      cont_stack = Keval(t1,sigma) :: Keval(t2,sigma) :: Kbinop op :: rem;
    }
  | Tnot t1 ->
    { value_stack = st;
      cont_stack = Keval(t1,sigma) :: Knot :: rem;
    }
  | Teps tb ->
    let v,t1 = t_open_bound tb in
    { value_stack = st ;
      cont_stack = Keval(t1,sigma) :: Keps v :: rem;
    }
  | Tquant(q,tq) ->
    let vl,tr,t1 = t_open_quant tq in
    { value_stack = st;
      cont_stack = Keval(t1,sigma) :: Kquant(q,vl,tr) :: rem;
    }
  | Tapp(ls,tl) ->
    let args = List.rev_map (fun t -> Keval(t,sigma)) tl in
    { value_stack = st;
      cont_stack = List.rev_append args (Kapp(ls,t.t_ty) :: rem);
    }
  | Ttrue | Tfalse | Tconst _ ->
    { value_stack = Term t :: st;
      cont_stack = rem;
    }

and reduce_app st ls ty rem =
  let rec extract_first n acc l =
    if n = 0 then acc,l else
      match l with
      | Term x :: r ->
        extract_first (n-1) (x::acc) r
      | [] -> assert false
  in
  let arity = List.length ls.ls_args in
  let args,rem_st = extract_first arity [] st in
(*
  try
    let f = Hls.find builtins ls in
    f ls tl ty
  with Not_found ->
*)
(*
    try
      let d = Ident.Mid.find ls.ls_name env.tknown in
      match d.Decl.d_node with
      | Decl.Dtype _ | Decl.Dprop _ -> assert false
      | Decl.Dlogic dl ->
        (* regular definition *)
        let d = List.assq ls dl in
        let l,t = Decl.open_ls_defn d in
        let env' = multibind_vs l tl env in
        compute_in_term env' t
      | Decl.Dparam _ | Decl.Dind _ ->
        t_app ls tl ty
      | Decl.Ddata dl ->
        (* constructor or projection *)
        match tl with
        | [ { t_node = Tapp(ls1,tl1) } ] ->
          (* if ls is a projection and ls1 is a constructor,

             we should compute that projection *)
          let rec iter dl =
            match dl with
            | [] -> t_app ls tl ty
            | (_,csl) :: rem ->
              let rec iter2 csl =
                match csl with
                | [] -> iter rem
                | (cs,prs) :: rem2 ->
                  if ls_equal cs ls1
                  then
                    (* we found the right constructor *)
                    let rec iter3 prs tl1 =
                      match prs,tl1 with
                      | (Some pr)::prs, t::tl1 ->
                        if ls_equal ls pr
                        then (* projection found! *) t
                        else
                          iter3 prs tl1
                      | None::prs, _::tl1 ->
                        iter3 prs tl1
                      | _ -> t_app ls tl ty
                    in iter3 prs tl1
                  else iter2 rem2
              in iter2 csl
          in iter dl
        | _ -> t_app ls tl ty
    with Not_found ->
*)
(*
      Format.eprintf "[Compute] definition of logic symbol %s not found@."
        ls.ls_name.Ident.id_string;
*)
      { value_stack = Term (t_app ls args ty) :: rem_st;
        cont_stack = rem;
      }



(* TODO *)

let rec many_steps engine c n =
  match c.value_stack, c.cont_stack with
  | [Term t], [] -> t
  | _, [] -> assert false
  | _ -> if n = 0 then assert false else
      let c = reduce engine c in
      many_steps engine c (n-1)

let normalize engine t = 
  let c = { value_stack = []; cont_stack = [Keval(t,Mvs.empty)] } in
  many_steps engine c 1000

let create () = Mls.empty

exception NotARewriteRule of string

let add_rule _t _e = assert false
