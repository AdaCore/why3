
open Term






(* {2 builtin symbols} *)

let builtins = Hls.create 17

let ls_minus = ref ps_equ (* temporary *)

(* all builtin functions *)

exception Undetermined

let const_equality c1 c2 =
  match c1,c2 with
  | Number.ConstInt i1, Number.ConstInt i2 ->
    BigInt.eq (Number.compute_int i1) (Number.compute_int i2)
  | _ -> raise Undetermined

let value_equality t1 t2 =
  match (t1.t_node,t2.t_node) with
  | Tconst c1, Tconst c2 -> const_equality c1 c2
  | _ -> raise Undetermined

let to_bool b = if b then t_true else t_false

let eval_equ _ls l _ty =
  match l with
  | [t1;t2] ->
    begin
      try to_bool (value_equality t1 t2)
      with Undetermined -> t_equ t1 t2
    end
  | _ -> assert false


let eval_true _ls _l _ty = t_true

let eval_false _ls _l _ty = t_false

exception NotNum

let big_int_of_const c =
  match c with
    | Number.ConstInt i -> Number.compute_int i
    | _ -> raise NotNum

let const_of_big_int n =
  t_const (Number.ConstInt (Number.int_const_dec (BigInt.to_string n)))

let eval_int_op op ls l ty =
  match l with
  | [{t_node = Tconst c1};{t_node = Tconst c2}] ->
    begin
      try const_of_big_int (op (big_int_of_const c1) (big_int_of_const c2))
      with NotNum | Division_by_zero ->
        t_app ls l ty
    end
  | _ -> t_app ls l ty

let eval_int_rel op ls l ty =
  match l with
  | [{t_node = Tconst c1};{t_node = Tconst c2}] ->
    begin
      try to_bool (op (big_int_of_const c1) (big_int_of_const c2))
      with NotNum | Division_by_zero ->
        t_app ls l ty
    end
  | _ -> t_app ls l ty

let eval_int_uop op ls l ty =
  match l with
  | [{t_node = Tconst c1}] ->
    begin
      try const_of_big_int (op (big_int_of_const c1))
      with NotNum | Division_by_zero ->
        t_app ls l ty
    end
  | _ -> t_app ls l ty


let built_in_theories =
  [ ["bool"],"Bool", [],
    [ "True", None, eval_true ;
      "False", None, eval_false ;
    ] ;
    ["int"],"Int", [],
    [ "infix +", None, eval_int_op BigInt.add;
      "infix -", None, eval_int_op BigInt.sub;
      "infix *", None, eval_int_op BigInt.mul;
      "prefix -", Some ls_minus, eval_int_uop BigInt.minus;
      "infix <", None, eval_int_rel BigInt.lt;
      "infix <=", None, eval_int_rel BigInt.le;
      "infix >", None, eval_int_rel BigInt.gt;
      "infix >=", None, eval_int_rel BigInt.ge;
    ] ;
    ["int"],"MinMax", [],
    [ "min", None, eval_int_op BigInt.min;
      "max", None, eval_int_op BigInt.max;
    ] ;
    ["int"],"ComputerDivision", [],
    [ "div", None, eval_int_op BigInt.computer_div;
      "mod", None, eval_int_op BigInt.computer_mod;
    ] ;
    ["int"],"EuclideanDivision", [],
    [ "div", None, eval_int_op BigInt.euclidean_div;
      "mod", None, eval_int_op BigInt.euclidean_mod;
    ] ;
(*
    ["map"],"Map", ["map", builtin_map_type],
    [ "const", Some ls_map_const, eval_map_const;
      "get", Some ls_map_get, eval_map_get;
      "set", Some ls_map_set, eval_map_set;
    ] ;
*)
  ]

let add_builtin_th env (l,n,t,d) =
  try
    let th = Env.find_theory env l n in
    List.iter
      (fun (id,r) ->
        let ts = Theory.ns_find_ts th.Theory.th_export [id] in
        r ts)
      t;
    List.iter
      (fun (id,r,f) ->
        let ls = Theory.ns_find_ls th.Theory.th_export [id] in
        Hls.add builtins ls f;
        match r with
          | None -> ()
          | Some r -> r := ls)
      d
  with Not_found ->
    Format.eprintf "[Compute] theory %s not found@." n

let get_builtins env =
  Hls.clear builtins;
  Hls.add builtins ps_equ eval_equ;
  List.iter (add_builtin_th env) built_in_theories



(* {2 the reduction machine} *)


type rule = Svs.t * term list * term

type engine =
  { known_map : Decl.decl Ident.Mid.t;
    rules : rule list Mls.t;
  }


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

exception Irreducible

let one_step_reduce engine ls args =
  try
    let rules = Mls.find ls engine.rules in
    let rec loop rules =
      match rules with
        | [] -> raise Irreducible
        | (vars,largs,rhs)::rem ->
          begin
            try
              let sigma = first_order_matching vars largs args in
              sigma,rhs
            with NoMatch ->
              loop rem
          end
    in loop rules
  with Not_found ->
    raise Irreducible

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
    reduce_app engine st ls ty rem
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

and reduce_app engine st ls ty rem_cont =
  let rec extract_first n acc l =
    if n = 0 then acc,l else
      match l with
      | Term x :: r ->
        extract_first (n-1) (x::acc) r
      | [] -> assert false
  in
  let arity = List.length ls.ls_args in
  let args,rem_st = extract_first arity [] st in
  try
    let f = Hls.find builtins ls in
    let t = f ls args ty in
    { value_stack = Term t :: rem_st;
      cont_stack = rem_cont;
    }
  with Not_found ->
    try
      let d = Ident.Mid.find ls.ls_name engine.known_map in
      match d.Decl.d_node with
      | Decl.Dtype _ | Decl.Dprop _ -> assert false
      | Decl.Dlogic dl ->
        (* regular definition *)
        let d = List.assq ls dl in
        let l,t = Decl.open_ls_defn d in
        let type_subst = Ty.oty_match Ty.Mtv.empty ty t.t_ty in
        let t = t_ty_subst type_subst Mvs.empty t in
        let sigma =
          try
            List.fold_right2 Mvs.add l args Mvs.empty
          with Invalid_argument _ -> assert false
        in
        { value_stack = rem_st;
          cont_stack = Keval(t,sigma) :: rem_cont;
        }
      | Decl.Dparam _ | Decl.Dind _ ->
        (* try a rewrite rule *)
        begin
          try
            let sigma,rhs = one_step_reduce engine ls args in
            let type_subst = Ty.oty_match Ty.Mtv.empty ty rhs.t_ty in
            Format.eprintf "subst of rhs: ";
            Ty.Mtv.iter
              (fun tv ty -> Format.eprintf "%a -> %a,"
                Pretty.print_tv tv Pretty.print_ty ty)
              type_subst;
            Format.eprintf "@.";
            let rhs = t_ty_subst type_subst Mvs.empty rhs in
            let sigma =
              Mvs.map (t_ty_subst type_subst Mvs.empty) sigma
            in
            { value_stack = rem_st;
              cont_stack = Keval(rhs,sigma) :: rem_cont;
            }
          with Irreducible ->
            raise Not_found
        end
      | Decl.Ddata dl ->
        (* constructor or projection *)
        match args with
        | [ { t_node = Tapp(ls1,tl1) } ] ->
          (* if ls is a projection and ls1 is a constructor,
             we should compute that projection *)
          let rec iter dl =
            match dl with
            | [] -> raise Not_found
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
                        then (* projection found! *)
                          { value_stack = Term t :: rem_st;
                            cont_stack = rem_cont;
                          }
                        else
                          iter3 prs tl1
                      | None::prs, _::tl1 ->
                        iter3 prs tl1
                      | _ -> raise Not_found
                    in iter3 prs tl1
                  else iter2 rem2
              in iter2 csl
          in iter dl
        | _ -> raise Not_found
    with Not_found ->
      { value_stack = Term (t_app ls args ty) :: rem_st;
        cont_stack = rem_cont;
      }



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






(* the rewrite engine *)

let create env km =
  get_builtins env;
  { known_map = km ;
    rules = Mls.empty;
  }

exception NotARewriteRule of string

let extract_rule t =
  let rec aux acc t =
    match t.t_node with
      | Tquant(Tforall,q) ->
        let vs,_,t = t_open_quant q in
        aux (List.fold_left (fun acc v -> Svs.add v acc) acc vs) t
      | Tbinop(Tiff,t1,t2) ->
        begin
          match t1.t_node with
            | Tapp(ls,args) -> acc,ls,args,t2
            | _ -> raise
              (NotARewriteRule "lhs of <-> should be a predicate symbol")
        end
      | Tapp(ls,[t1;t2]) when ls == ps_equ ->
        begin
          match t1.t_node with
            | Tapp(ls,args) -> acc,ls,args,t2
            | _ -> raise
              (NotARewriteRule "lhs of = should be a function symbol")
        end
      | _ -> raise
        (NotARewriteRule "rule should be of the form forall ... t1 = t2 or f1 <-> f2")


  in
  aux Svs.empty t


let add_rule t e =
  let vars,ls,args,r = extract_rule t in
  let rules =
    try Mls.find ls e.rules
    with Not_found -> []
  in
  {e with rules =
      Mls.add ls ((vars,args,r)::rules) e.rules}
