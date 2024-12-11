(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**

   {1 Abstract syntax trees}

 *)

(* open Why3 *)
(* to comment out when inside Why3 *)

type var_type =
  | Tunit
  | Tint
  | Tbool

type label = Here | Old

type expression =
    | Evar of Abstract.why_var * label
    | Ecst of string
    | Eadd of expression * expression
    | Esub of expression * expression
    | Emul of expression * expression
    | Ediv of expression * expression
    | Emod of expression * expression
    | Ebwtrue
    | Ebwfalse
    | Ebwnot of expression
    | Ebwand of expression * expression
    | Ebwor of expression * expression

let e_var v lab = Evar(v,lab)
let e_cst c = Ecst c

let e_add e1 e2 = Eadd(e1,e2)
let e_sub e1 e2 = Esub(e1,e2)
let e_mul e1 e2 = Emul(e1,e2)
let e_div e1 e2 = Ediv(e1,e2)
let e_mod e1 e2 = Emod(e1,e2)

let e_bwtrue = Ebwtrue
let e_bwfalse = Ebwfalse

let bwnot_simp e =
  match e with
  | Ebwtrue -> Ebwfalse
  | Ebwfalse -> Ebwtrue
  | Ebwnot e -> e
  | _ -> Ebwnot e

let bwor_simp e1 e2 =
  match e1, e2 with
  | Ebwtrue,_ | _,Ebwtrue -> Ebwtrue
  | Ebwfalse,_ -> e2
  | _,Ebwfalse -> e1
  | _ -> Ebwor(e1,e2)

let bwand_simp e1 e2 =
  match e1, e2 with
  | Ebwfalse,_ | _,Ebwfalse -> Ebwfalse
  | Ebwtrue,_ -> e2
  | _,Ebwtrue -> e1
  | _ -> Ebwand(e1,e2)

let rec subst_e (x:Abstract.why_var) (t:expression) (e:expression) : expression =
  match e with
  | Evar (var, Here) -> if var = x then t else e
  | Evar (_, Old) -> assert false
  | Eadd (e1, e2) -> Eadd(subst_e x t e1, subst_e x t e2)
  | Esub (e1, e2) -> Esub(subst_e x t e1, subst_e x t e2)
  | Emul (e1, e2) -> Emul(subst_e x t e1, subst_e x t e2)
  | Ediv (e1, e2) -> Ediv(subst_e x t e1, subst_e x t e2)
  | Emod (e1, e2) -> Emod(subst_e x t e1, subst_e x t e2)
  | Ebwnot e -> Ebwnot(subst_e x t e)
  | Ebwand (e1, e2) -> Ebwand(subst_e x t e1, subst_e x t e2)
  | Ebwor (e1, e2) -> Ebwor(subst_e x t e1, subst_e x t e2)
  | Ecst _ | Ebwtrue | Ebwfalse -> e

let e_let_in_expression v e1 e2 = subst_e v e1 e2

type atomic_condition =
    | Ceq of expression * expression
    | Cne of expression * expression
    | Clt of expression * expression
    | Cle of expression * expression
    | Cgt of expression * expression
    | Cge of expression * expression
    | C_is_true of expression

let c_eq_int e1 e2 = Ceq(e1,e2)
let c_ne_int e1 e2 = Cne(e1,e2)

let c_le e1 e2 = Cle(e1,e2)
let c_lt e1 e2 = Clt(e1,e2)
let c_ge e1 e2 = Cge(e1,e2)
let c_gt e1 e2 = Cgt(e1,e2)

let rec c_is_true e =
  match e with
  | Ebwnot e -> c_is_false e
  | _ -> C_is_true e

and c_is_false e =
  match e with
  | Ebwnot e -> c_is_true e
  | _ -> C_is_true (Ebwnot e)


let neg_atomic_cond : atomic_condition -> atomic_condition = fun c ->
    match c with
    | Ceq (e1, e2) -> Cne (e1, e2)
    | Cne (e1, e2) -> Ceq (e1, e2)
    | Clt (e1, e2) -> Cge (e1, e2)
    | Cle (e1, e2) -> Cgt (e1, e2)
    | Cgt (e1, e2) -> Cle (e1, e2)
    | Cge (e1, e2) -> Clt (e1, e2)
    | C_is_true e -> c_is_false e

let c_eq_bool e1 e2 =
  match e1,e2 with
  | _, Ebwtrue -> c_is_true e1
  | Ebwtrue, _ -> c_is_true e2
  | _, Ebwfalse -> c_is_false e1
  | Ebwfalse, _ -> c_is_false e2
  | _ ->
    c_is_true (bwor_simp (bwand_simp e1 e2)
                 (bwand_simp (bwnot_simp e1) (bwnot_simp e2)))

let c_ne_bool e1 e2 =
  match e1,e2 with
  | _, Ebwtrue -> c_is_false e1
  | Ebwtrue, _ -> c_is_false e2
  | _, Ebwfalse -> c_is_true e1
  | Ebwfalse, _ -> c_is_true e2
  | _ ->
    c_is_true (bwor_simp (bwand_simp e1 (bwnot_simp e2))
                 (bwand_simp (bwnot_simp e1) e2))

type condition =
    | BTrue
    | BFalse
    | BAnd of condition * condition
    | BOr of condition * condition
    | BAtomic of atomic_condition
    | Bite of condition * condition * condition (* For printing only ! *)



let true_cond = BTrue
let false_cond = BFalse

let atomic_cond c = BAtomic c

let rec neg_cond : condition -> condition = fun c ->
    match c with
    | BTrue -> BFalse
    | BFalse -> BTrue
    | BAnd (c1, c2) -> BOr (neg_cond c1, neg_cond c2)
    | BOr (c1, c2) -> BAnd (neg_cond c1, neg_cond c2)
    | Bite _ -> assert false
    | BAtomic c -> BAtomic (neg_atomic_cond c)

let or_cond c1 c2 =
   match c1, c2 with
   | BTrue,_ | _,BTrue -> BTrue
   | BFalse,_ -> c2
   | _,BFalse -> c1
   | _ -> BOr(c1, c2)

let and_cond c1 c2 =
   match c1, c2 with
   | BTrue,_ -> c2
   | _,BTrue -> c1
   | BFalse,_ | _,BFalse -> BFalse
   | _ -> BAnd(c1,c2)

let rec subst_c (x:Abstract.why_var) (t:expression) (c:condition) : condition =
  match c with
  | BTrue -> BTrue
  | BFalse -> BFalse
  | BAnd (c1, c2) -> and_cond (subst_c x t c1) (subst_c x t c2)
  | BOr (c1, c2) -> or_cond (subst_c x t c1) (subst_c x t c2)
  | Bite _ -> assert false
  | BAtomic a ->
     let a' =
       match a with
       | Ceq (e1, e2) -> Ceq (subst_e x t e1, subst_e x t e2)
       | Cne (e1, e2) -> Cne (subst_e x t e1, subst_e x t e2)
       | Clt (e1, e2) -> Clt (subst_e x t e1, subst_e x t e2)
       | Cle (e1, e2) -> Cle (subst_e x t e1, subst_e x t e2)
       | Cgt (e1, e2) -> Cgt (subst_e x t e1, subst_e x t e2)
       | Cge (e1, e2) -> Cge (subst_e x t e1, subst_e x t e2)
       | C_is_true e -> C_is_true (subst_e x t e)
     in BAtomic a'


let e_let_in_condition v e c = subst_c v e c

let ternary_condition c c1 c2 =
  (* `if c then c1 else c2` is equivalent to
     `(c /\ c1) \/ (not c /\ c2)` *)
  or_cond (and_cond c c1) (and_cond (neg_cond c) c2)

let ternary_condition_no_simpl c c1 c2 = Bite(c,c1,c2)

(** {2 Statements} *)

type fun_id = {
    fun_name : string;
    fun_tag : int;
  }

let compare_fun_id v1 v2 =
  Stdlib.compare v1.fun_tag v2.fun_tag

module FuncMap = Map.Make(struct
                  type t = fun_id
                  let compare = compare_fun_id
                end)


let print_fun_id fmt id =
  Format.fprintf fmt "%s" id.fun_name

let create_fun_id =
  let c = ref 0 in
  fun name -> incr c; {
      fun_name = name;
      fun_tag = !c;
    }

type memo_env = Abstract.why_env * condition

type statement_node =
    | Swhile of condition * (string option * condition) list * statement
    | Sfcall of (Abstract.why_var * statement * Abstract.var_value) option *
                (Abstract.why_var * Abstract.var_value * expression) list *
                fun_id * expression list * memo_env option ref *
                Abstract.memo_add_env option ref * Abstract.memo_add_env option ref *
                Abstract.memo_havoc option ref * statement option ref
    | Site of condition * statement * statement
    | Sblock of statement list
    | Sassert of condition
    | Sassume of condition
    | Shavoc of Abstract.why_env * condition * Abstract.memo_havoc option ref
    | Sletin of Abstract.why_var * Abstract.var_value * expression * statement
    | Sbreak

and statement = {
    stmt_tag : string;
    stmt_node : statement_node;
  }

let mk_stmt tag n = { stmt_tag = tag; stmt_node = n }

let rec copy_stmt s =
  { s with stmt_node = copy_stmt_node s.stmt_node }

and copy_stmt_node n =
  match n with
  | Swhile(c,invs,b) -> Swhile(c,invs,copy_stmt b)
  | Sfcall(ret,lets,f,args,_,_,_,_,_) ->
    let ret = Option.map (fun (v,s,x) -> (v,copy_stmt s,x)) ret in
    Sfcall(ret,lets,f,args,ref None,ref None,ref None,ref None, ref None)
  | Site(c,s1,s2) -> Site(c,copy_stmt s1,copy_stmt s2)
  | Sblock sl -> Sblock(List.map copy_stmt sl)
  | Sletin(v,x,e,s) -> Sletin(v,x,e,copy_stmt s)
  | Shavoc(env,c,_) -> Shavoc(env,c,ref None)
  | Sassert _ | Sassume _ | Sbreak -> n

let calling_fresh_allowed = ref true

let fresh_var ty =
  assert !calling_fresh_allowed;
  let open Abstract in
  match ty with
  | Tunit -> UnitValue
  | Tint -> IntValue (fresh_apron_var ())
  | Tbool -> BoolValue (fresh_bdd_var ())

let rec oldify v e =
  match e with
  | Evar(_,Old) -> assert false
  | Evar(x,Here) when Abstract.compare_var x v = 0 -> e_var x Old
  | Evar(_,Here) | Ecst _ | Ebwfalse | Ebwtrue -> e
  | Eadd(e1,e2)-> e_add (oldify v e1) (oldify v e2)
  | Esub(e1,e2)-> e_sub (oldify v e1) (oldify v e2)
  | Emul(e1,e2)-> e_mul (oldify v e1) (oldify v e2)
  | Ediv(e1,e2)-> e_div (oldify v e1) (oldify v e2)
  | Emod(e1,e2)-> e_mod (oldify v e1) (oldify v e2)
  | Ebwand(e1,e2)-> bwand_simp (oldify v e1) (oldify v e2)
  | Ebwor(e1,e2)-> bwor_simp (oldify v e1) (oldify v e2)
  | Ebwnot(e) -> bwnot_simp (oldify v e)

let s_assign tag ty v e =
  let n =
    match ty with
    | Tunit ->
      Sblock []
    | Tint ->
      let w = Abstract.fresh_apron_var () in
      let env = Abstract.(VarMap.add v (IntValue w) VarMap.empty) in
      let eold = oldify v e in
      let c = c_eq_int (e_var v Here) eold in
      Shavoc(env,atomic_cond c, ref None)
    | Tbool ->
      let b = Abstract.fresh_bdd_var () in
      let env = Abstract.(VarMap.add v (BoolValue b) VarMap.empty) in
      let eold = oldify v e in
      let c = c_eq_bool (e_var v Here) eold in
      Shavoc(env,atomic_cond c, ref None)
  in
  mk_stmt tag n

let s_assert tag c =
  mk_stmt tag (Sassert c)

let s_assume tag c =
  mk_stmt tag (Sassume c)

let s_sequence tag s1 s2 =
  match s1.stmt_node, s2.stmt_node with
  | Sblock [],_ -> s2
  | _,Sblock [] -> s1
  | Sblock l1, Sblock l2 -> { s2 with stmt_node = Sblock (l1 @ l2) }
  | Sblock l1, _ -> { s1 with stmt_node = Sblock (l1 @ [s2]) }
  | _,Sblock l2 -> { s2 with stmt_node = Sblock (s1 :: l2) }
  | _,_ -> { stmt_tag = tag ; stmt_node = Sblock [s1;s2] }

let s_block tag sl =
  mk_stmt tag (Sblock sl)

let s_ite tag c e1 e2 =
  mk_stmt tag (Site(c,e1,e2))

let s_while tag cond invs body =
  mk_stmt tag (Swhile(cond, invs, body))

let s_call tag ret lets f el =
  let lets =
    List.fold_right
      (fun (ty,v,e) acc ->
         let av = fresh_var ty in
         (v,av,e) :: acc)
      lets []
  in
  let n =
    match ret with
    | None -> Sfcall(None,lets,f,el, ref None, ref None, ref None, ref None, ref None)
    | Some (ty,v,e) ->
       let ab = fresh_var ty in
       Sfcall(Some(v,e,ab),lets,f,el, ref None, ref None, ref None, ref None, ref None)
  in
  mk_stmt tag n

let s_havoc tag writes c =
  let open Abstract in
  let m =
    VarMap.fold
      (fun v ty acc -> VarMap.add v (fresh_var ty) acc)
      writes VarMap.empty
  in
  mk_stmt tag (Shavoc(m,c,ref None))

let s_let_in tag ty v e s =
  let av = fresh_var ty in
  mk_stmt tag (Sletin(v,av,e,s))

let s_break tag  =
  mk_stmt tag Sbreak


type fun_kind =
  | Fun_let of statement * expression option
  (** functions defined with a body and possibly a returned expression *)
  | Fun_val of Abstract.why_env * (Abstract.why_var * Abstract.var_value) option * condition
  (** functions declared with a contract: a writes clause,
      an optional result variable, and a post-condition *)

type param_value = Param_ref of var_type | Param_noref of Abstract.var_value

type func = {
    func_name : fun_id;
    func_params : (Abstract.why_var * param_value) list;
    func_def : fun_kind
  }
(** function declarations. *)

let declare_function_let ~(name:fun_id)
      ~(params:(bool * var_type * Abstract.why_var) list)
      ~(body:statement) ~(return:(var_type * expression) option) : func =
  let func_params =
    List.map
      (fun (is_ref,ty,v) ->
        let av =
          if is_ref then Param_ref ty else
            Param_noref (fresh_var ty)
        in (v,av))
      params
  in
  let return =
    match return with
    | Some (_,e) -> Some e
    | None -> None
  in
  let func_def = Fun_let(body,return) in
  {
    func_name = name;
    func_params;
    func_def;
  }

let declare_function_val ~(name:fun_id)
      ~(params:(bool * var_type * Abstract.why_var) list)
      ~(writes:var_type Abstract.VarMap.t)
      ~(result:(var_type * Abstract.why_var) option)
      ~(post:condition) : func =
  let open Abstract in
  let func_params =
    List.map
      (fun (is_ref,ty,v) ->
        let av =
          if is_ref then Param_ref ty else
            Param_noref(fresh_var ty)
        in (v,av))
      params
  in
  let writes =
    VarMap.fold
      (fun v ty acc -> VarMap.add v (fresh_var ty) acc)
      writes VarMap.empty
  in
  let result = match result with
    | None -> None
    | Some (ty,v) -> Some (v, fresh_var ty)
  in
  let func_def = Fun_val(writes,result,post) in
  {
    func_name = name;
    func_params;
    func_def;
  }



type why1program =
  {
    name       : string;
    vars       : Abstract.var_value Abstract.VarMap.t;
    functions  : func FuncMap.t;
    statements : statement
  }

let map_to_varmap (map: var_type Abstract.VarMap.t) : Abstract.var_value Abstract.VarMap.t =
  let open Abstract in
  let to_abstract v t varmap =
    let var = match t with
      | Tunit -> UnitValue
      | Tint -> IntValue (fresh_apron_var ())
      | Tbool -> BoolValue (fresh_bdd_var ())
    in
    VarMap.add v var varmap in
  VarMap.fold to_abstract map VarMap.empty


let mk_program ~name ~variables ~functions ~main =
  calling_fresh_allowed := false;
  { name = name;
    vars = map_to_varmap variables;
    functions;
    statements = main;
  }

let reset_ast_generation () =
  Abstract.reset_fresh_var_generators ();
  calling_fresh_allowed := true


(** {2 Printing} *)


let print_type fmt t =
  match t with
  | Tunit -> Format.fprintf fmt "unit"
  | Tint -> Format.fprintf fmt "int"
  | Tbool -> Format.fprintf fmt "bool"

let rec print_expression fmt e =
    match e with
    | Evar (v, Here) -> Format.fprintf fmt "%a" Abstract.print_var v
    | Evar (v, Old) -> Format.fprintf fmt "@@%a" Abstract.print_var v
    | Ecst i -> Format.fprintf fmt "%s" i
    | Eadd(e1, e2) -> Format.fprintf fmt "(%a + %a)" print_expression e1 print_expression e2
    | Esub(e1, e2) -> Format.fprintf fmt "(%a - %a)" print_expression e1 print_expression e2
    | Emul(e1, e2) -> Format.fprintf fmt "(%a * %a)" print_expression e1 print_expression e2
    | Ediv(e1, e2) -> Format.fprintf fmt "(%a / %a)" print_expression e1 print_expression e2
    | Emod(e1, e2) -> Format.fprintf fmt "(%a %% %a)" print_expression e1 print_expression e2
    | Ebwtrue -> Format.fprintf fmt "True"
    | Ebwfalse -> Format.fprintf fmt "False"
    | Ebwnot e' -> Format.fprintf fmt "~%a" print_expression e'
    | Ebwand(e1, e2) -> Format.fprintf fmt "(%a & %a)" print_expression e1 print_expression e2
    | Ebwor(e1, e2) -> Format.fprintf fmt "(%a | %a)" print_expression e1 print_expression e2



let rec print_condition fmt c =
    match c with
    | BTrue -> Format.fprintf fmt "T"
    | BFalse -> Format.fprintf fmt "F"
    | BAnd (c1, c2) -> Format.fprintf fmt "@[<hv 2>(%a@ &&@ %a)@]" print_condition c1 print_condition c2
    | BOr (c1, c2) -> Format.fprintf fmt "@[<hv 2>(%a ||@ %a)@]" print_condition c1 print_condition c2
    | Bite(c,c1,c2) -> Format.fprintf fmt "@[<hv 2>(if %a@ then %a@ else %a)@]"
                         print_condition c print_condition c1 print_condition c2
    | BAtomic a ->
        match a with
        | Ceq(e1, e2) -> Format.fprintf fmt "@[<hv 2>%a =@ %a@]" print_expression e1 print_expression e2
        | Cne(e1, e2) -> Format.fprintf fmt "@[<hv 2>%a <>@ %a@]" print_expression e1 print_expression e2
        | Clt(e1, e2) -> Format.fprintf fmt "@[<hv 2>%a <@ %a@]" print_expression e1 print_expression e2
        | Cle(e1, e2) -> Format.fprintf fmt "@[<hv 2>%a <=@ %a@]" print_expression e1 print_expression e2
        | Cgt(e1, e2) -> Format.fprintf fmt "@[<hv 2>%a >@ %a@]" print_expression e1 print_expression e2
        | Cge(e1, e2) -> Format.fprintf fmt "@[<hv 2>%a >=@ %a@]" print_expression e1 print_expression e2
        | C_is_true e' -> print_expression fmt e'

let print_lets fmt lets =
  List.iter
    (fun (v,_,e) ->
       Format.fprintf fmt "let @[<hv 0>%a =@ @[%a@]@]@ in@ "
         Abstract.print_var v print_expression e)
    lets

let rec print_statement_node fmt s =
  let open Format in
  match s with
  | Sfcall(None,lets,id,el,_,_,_,_,_) ->
    fprintf fmt "@[%a%a(%a)@]"
      print_lets lets
      print_fun_id id
      (Pp.print_list Pp.comma print_expression) el
  | Sfcall(Some (x,s,_),lets,id,el,_,_,_,_,_) ->
     fprintf fmt "@[<hv 0>letcall %a <- @[%a%a(%a)@]@ in@ @[%a@]@ endletcall@]"
       Abstract.print_var x
       print_lets lets
       print_fun_id id
       (Pp.print_list Pp.comma print_expression) el print_statement s
  | Swhile(c,invs,s) ->
    fprintf fmt "@[<hv 2>while @[%a@] do@ " print_condition c;
    List.iter (fun (n, c) ->
                match n with
                | None -> fprintf fmt "@[invariant @[%a@]@]@ " print_condition c
                | Some(n) -> fprintf fmt "@[invariant @[@%s] @[%a@]@]@ " n print_condition c) invs;
    fprintf fmt "@[%a@]@]" print_statement s
  | Site(c,s1,s2) ->
     fprintf fmt "@[<hv 2>if @[%a@]@ then@ @[%a@]@ else@ @[%a@]@ endif@]"
       print_condition c print_statement s1 print_statement s2
  | Sassert c ->
     fprintf fmt "@[<hv 2>assert @[%a@]@]" print_condition c
  | Sassume c ->
     fprintf fmt "@[<hv 2>assume @[%a@]@]" print_condition c
  | Sblock (s::sl) ->
     fprintf fmt "@[<hv 2>{ @[%a@]" print_statement s;
     List.iter (function s -> fprintf fmt ";@ @[%a@]" print_statement s) sl;
     fprintf fmt " }@]"
  | Sblock [] ->
     fprintf fmt "skip";
  | Shavoc (m, c, _) ->
     fprintf fmt "@[<hv 2>havoc writes {%a} @]" Abstract.print_env m;
     fprintf fmt "@[<hv 2>ensures @[%a@]@]" print_condition c
  | Sletin(v,_,e,s) ->
     fprintf fmt "@[<hv 0>let @[<hv 0>%a =@ @[%a@]@]@ in@ @[%a@]@ endlet@]"
       Abstract.print_var v print_expression e print_statement s
  | Sbreak -> fprintf fmt "break"

and print_statement fmt s =
  match s.stmt_tag with
  | "" -> print_statement_node fmt s.stmt_node
  | atr ->
     Format.fprintf fmt "@[[%s]@ %a@]" atr print_statement_node s.stmt_node

let print_param fmt (v, av) =
  match av with
  | Param_ref ty ->
     Format.fprintf fmt "ref %a: %a" Abstract.print_var v print_type ty
  | Param_noref av ->
     Format.fprintf fmt "%a(%a)"
       Abstract.print_var v Abstract.print_var_value av


let print_func_def fmt (_d: fun_kind) : unit =
  Format.fprintf fmt "<funcdef>"

let print_func fmt (_, f : fun_id * func) : unit =
  Format.fprintf fmt
    "@[<hv 2>{ func_name  = %a ;@ func_params = [ @[%a@] ] ;@ func_def = @[%a@]@ }@]"
    print_fun_id f.func_name
    Pp.(print_list semi print_param) f.func_params
    print_func_def f.func_def


let print_program fmt p =
  Format.fprintf fmt
    "@[<hv 2>{ vars = @[%a@] ;@ functions = @[%a@] ;@ main = @[%a@]@ }@]"
    Abstract.print_env p.vars
    Pp.(print_list semi print_func) (FuncMap.bindings p.functions)
    print_statement p.statements
