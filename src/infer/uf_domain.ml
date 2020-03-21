open Domain
open Apron
open Term

module Make(S:sig
    module    Dom : DOMAIN
    val       env : Env.env
    val  th_known : Decl.known_map
    val mod_known : Pdecl.known_map
  end) : TERM_DOMAIN = struct

  module Dom = S.Dom

  module Ai_logic = Ai_logic.Make(struct
      let       env = S.env
      let  th_known = S.th_known
      let mod_known = S.mod_known
    end)
  open Ai_logic

  exception Not_handled of Term.term

  (* utility function that make equivalent classes and
     sum the last component *)
  let sum_list a =
    let a = List.sort (fun (i, _) (j, _) ->
        compare i j) a in
    let rec merge = function
      | [] -> []
      | [b] -> [b]
      | (a, b) :: (c, d) :: q ->
        if a = c then merge ((a, b + d) :: q)
        else (a, b) :: merge ((c, d) :: q)
    in merge a

  module TermToVar   = O2oterm.Make(struct type t = Var.t end)
  module TermToClass = O2oterm.Make(struct type t = Union_find.t end)
  module VarPool = struct
    module S = Set.Make(struct type t = Var.t
                               let compare = compare end)
    include S
    let to_list a = S.fold (fun a l -> a :: l) a []
  end

  type uf_man = {
    variable_mapping: (Apron.Var.t, Term.term) Hashtbl.t;
    mutable apron_mapping: Var.t Term.Mterm.t;
    mutable region_mapping: (Ity.pvsymbol * Term.term) list Ity.Mreg.t;
    mutable region_var: Term.vsymbol list Ity.Mreg.t;
    mutable env: Environment.t;

    mutable defined_terms: unit Mterm.t;

    (* UF_QF *)
    mutable class_to_term: TermToClass.t;
  }

  type uf_t = {
    classes: Union_find.set;
    uf_to_var: TermToVar.t;
    var_pool: VarPool.t;
  }


  type man = Dom.man * uf_man
  type env = unit
  type t = Dom.t * uf_t

  let tmp_pool = ["$p1";"$p2"; "$p3"] |> List.map Var.of_string

  let build_var_pool n =
    let rec build_var_pool_aux = function
      | 0 -> []
      | n -> let v = Var.of_string (Format.sprintf "$%d" n) in
             v :: build_var_pool_aux (n - 1)
    in
    build_var_pool_aux n |> VarPool.of_list

  let npool = 10

  let create_manager () =
    let apron_mapping = Term.Mterm.empty in
    let var_pool = build_var_pool npool in
    let vars = Array.of_list (VarPool.to_list var_pool @ tmp_pool) in
    let uf_man = {
        variable_mapping = Hashtbl.create 512;
        apron_mapping;
        region_mapping = Ity.Mreg.empty;
        region_var = Ity.Mreg.empty;
        env = Environment.make vars [||];
        defined_terms = Mterm.empty;
        class_to_term = TermToClass.empty; } in
    Dom.create_manager (), uf_man

  let empty_uf_domain = {
    classes = Union_find.empty;
    uf_to_var = TermToVar.empty;
    var_pool = build_var_pool npool;
  }

  let bottom (man, uf_man) _ =
    Dom.bottom man uf_man.env, empty_uf_domain

  let top (man, uf_man) _ =
    Dom.top man uf_man.env, empty_uf_domain

  let canonicalize (man, _) (a, _) =
    Dom.canonicalize man a

  let is_bottom (man, _) (a, _) =
    Dom.is_bottom man a

  let get_class_for_term uf_man t =
    try TermToClass.to_t uf_man.class_to_term t with Not_found ->
      let c = Union_find.new_class () in
      uf_man.class_to_term <- TermToClass.add uf_man.class_to_term t c;
      c

  (* let get_equivs uf_man uf t =
   *   let tcl = TermToClass.to_t uf_man.class_to_term t in
   *   Union_find.get_class tcl uf |> List.map (TermToClass.to_term uf_man.class_to_term) *)

  let apply_equal (man, uf_man) ud d l =
    List.fold_left (fun (d, v) t ->
        try
          match v with
          | None -> d, Some (TermToVar.to_t ud.uf_to_var t)
          | Some var ->
            let expr = Linexpr1.make uf_man.env in
            let var' = TermToVar.to_t ud.uf_to_var t in
            Linexpr1.set_coeff expr var (Coeff.s_of_int (-1));
            Linexpr1.set_coeff expr var' (Coeff.s_of_int 1);
            let lincons = Lincons1.make expr Lincons1.EQ in
            let lincons_array = Lincons1.array_make uf_man.env 1 in
            Lincons1.array_set lincons_array 0 lincons;
            let d = Dom.meet_lincons_array man d lincons_array in
            d, v
        with Not_found -> d, v
      ) (d, None) l
    |> fst

  exception Constant

  let t_z_const a =
    if a >= 0 then t_nat_const a
    else t_app min_u_int [t_nat_const (-a)] (Some Ty.ty_int)

 (* let engine = Reduction_engine0.create {compute_defs = true; compute_builtin = true; compute_def_set = Term.Sls.empty; } env known_logical_ident*)

  (* we assume that there will be no overflow (oops) *)
  let rec eval_term t =
    let t = t (* Reduction_engine0.normalize ~limit:50 engine  t*) in
    if Ty.ty_equal (t_type t) Ty.ty_int then
      let rec eval_num t =
        let open Number in
        match t.t_node with
        | Tvar _ -> Some t, 0
        | Tconst (Constant.ConstInt n) ->
          (None, BigInt.to_int n.il_int)
        | Tapp (func, args) when Term.ls_equal func ad_int ->
          List.fold_left (fun (a, b) c ->
              let tc, cc = eval_num c in
              match tc, a with
              | None, None -> None, b + cc
              | Some t, Some v ->
                 Some (t_app ad_int [v; t] (Some Ty.ty_int)), b + cc
              | Some t, None | None, Some t -> Some t, b + cc
            ) (None, 0) args
        | Tapp (func, [a;b]) when Term.ls_equal func min_int ->
          let ta, ca = eval_num a in
          let tb, cb = eval_num b in
          begin
            match ta, tb with
            | None, None -> None, ca - cb
            | Some t, Some v -> Some (t_app_infer min_int [t; v]), ca - cb
            | Some t, None -> Some t, ca - cb
            | None, Some t -> Some (t_app_infer min_u_int [t]), ca - cb
          end
        | Tapp (func, [a]) when Term.ls_equal func min_u_int ->
          let ta, ca = eval_num a in
          begin
            match ta with
            | None -> None, - ca
            | Some a -> Some (t_app min_u_int [a] (Some Ty.ty_int)), - ca
          end
        | Tapp (func, args) ->
          let t = t_app func (List.map eval_term args) (Some (t_type t)) in
          Some t, 0
        | _ -> Some t, 0
      in
      match eval_num t with
      | Some t, 0 -> t
      | Some t, a -> t_app ad_int [t; t_z_const a] (Some Ty.ty_int)
      | None, _ -> raise Constant
    else
      t_map eval_term t

  let rec replaceby a b t =
    if t_equal t a then b
    else t_map (replaceby a b) t

  let do_eq (man, uf_man) a b =
    if not (Ty.ty_equal (t_type a) Ity.ty_unit) then
      fun (d, ud) ->
        let cla = get_class_for_term uf_man a in
        let clb = get_class_for_term uf_man b in
        let ud = { ud with classes = Union_find.union cla clb ud.classes; } in
        let all_values = Union_find.flat ud.classes in
        let all_terms =
          List.map (fun cl ->
              TermToClass.to_term uf_man.class_to_term cl, ()) all_values
        in
        let all_values = all_terms
                         |> Term.Mterm.of_list in
        let all_terms = all_terms |> List.map fst in
        Term.Mterm.fold (fun v () (d, ud) ->
            (* This is far from perfect. If there is a function f, then terms `f a` and `f b` will be marked as equal.
             * But if there is g: 'a -> 'b -> 'c, then `g a b` and `g b a` can not be marked as such. (As the replacement is global.)
             * However, it is unclear wether it is or it is not a limitation. *)
            let v' = replaceby a b v in
            let v'' = replaceby b a v in
            let v' = try eval_term v' with Constant -> v in
            let v'' = try eval_term v'' with Constant -> v in
            let v' = if List.exists (t_equal v') all_terms then v'
                     else v in
            let v'' = if List.exists (t_equal v'') all_terms then v''
                      else v in
            if t_equal v v' && t_equal v v'' then d, ud
            else
              begin
                let cl  = get_class_for_term uf_man v
                and cl' = get_class_for_term uf_man v'
                and cl'' = get_class_for_term uf_man v'' in
                let cl_cl' = Union_find.union cl cl' ud.classes in
                let ud = { ud with classes = Union_find.union cl cl'' cl_cl' } in
                let d =
                  if Ty.ty_equal (t_type v) Ty.ty_int then
                    Union_find.get_class cl ud.classes
                    |> List.map (TermToClass.to_term uf_man.class_to_term)
                    |> apply_equal (man, uf_man) ud d
                  else d
                in d, ud
              end
          ) all_values (d, ud)
    else fun x -> x

  (* probably not clever enough, will not work with a complex CFG with exceptions etc *)
  let print fmt (a, _) = Dom.print fmt a

  let get_var_for_term _ ref_dom term =
    let uf_to_var = !ref_dom.uf_to_var in
    try TermToVar.to_t uf_to_var term with Not_found ->
      let apron_var = VarPool.choose !ref_dom.var_pool in
      let uf_to_var = TermToVar.add uf_to_var term apron_var in
      let var_pool = VarPool.remove apron_var !ref_dom.var_pool in
      ref_dom := { !ref_dom with var_pool; uf_to_var };
      apron_var

  let eq_var (man, uf_man) b v1 v2 =
    if v1 <> v2 then
      let expr = Linexpr1.make uf_man.env in
      Linexpr1.set_coeff expr v1 (Coeff.s_of_int 1);
      Linexpr1.set_coeff expr v2 (Coeff.s_of_int (-1));
      let lincons = Lincons1.make expr Lincons1.EQ in
      let lincons_array = Lincons1.array_make uf_man.env 1 in
      Lincons1.array_set lincons_array 0 lincons;
      Dom.meet_lincons_array man b lincons_array
    else b

  let invariant_uf b =
    let s = ref VarPool.empty in
    try
      let k = ref b.uf_to_var in
      while true do
        let _, v = TermToVar.choose !k in
        s := VarPool.add v !s;
        k := TermToVar.remove_t !k v;
      done;
    with Not_found ->
      assert (VarPool.is_empty (VarPool.inter b.var_pool !s ));
      assert (VarPool.equal (VarPool.union b.var_pool !s )
                (build_var_pool npool))


  (* let print_uf b =
   *   let k = ref b.uf_to_var in
   *   try
   *     while true do
   *       let t, v = TermToVar.choose !k in
   *       if Debug.test_flag infer_debug then
   *         (p t; Format.eprintf " ---> %s@." (Var.to_string v));
   *       k := TermToVar.remove_t !k v;
   *     done;
   *   with
   *   | Not_found -> Format.eprintf "uf_to_var ended.@." *)

  let join_uf (man, uf_man) b d c =
    invariant_uf b;
    invariant_uf d;
    let classes = Union_find.join b.classes d.classes in
    let rc = ref c in
    let vars_to_replace = ref [] in
    let tmp_pool = ref tmp_pool in
    let var_pool = ref d.var_pool in
    let f_term t _ v = vars_to_replace := (t, v) :: !vars_to_replace in
    let f_t v1 _ t =
      let var_tmp = List.hd !tmp_pool in
      tmp_pool := List.tl !tmp_pool;
      rc := eq_var (man, uf_man) !rc v1 var_tmp;
      rc := Dom.forget_array man !rc [|v1|] false;
      var_pool := VarPool.add v1 !var_pool;
      vars_to_replace := (t, var_tmp) :: !vars_to_replace;
      assert (
          try TermToVar.to_term d.uf_to_var var_tmp |> ignore; false
          with Not_found -> true) in
    let uf_to_var = TermToVar.union d.uf_to_var b.uf_to_var f_t f_term in
    let var_pool = !var_pool in
    let var_pool = VarPool.inter b.var_pool var_pool in
    let b = { classes; uf_to_var; var_pool } in
    let rud = ref b in
    List.iter (fun (t, v) ->
        try
          let new_var = get_var_for_term uf_man rud t in
          rc := eq_var (man, uf_man) !rc v new_var;
          if v <> new_var then rc := Dom.forget_array man !rc [|v|] false;
        with Not_found ->
          Format.eprintf "REACHED END OF THE POOL@.@.@.";
          rc := Dom.forget_array man !rc [|v|] false;
      ) !vars_to_replace;
    invariant_uf !rud;
    !rc, !rud


  let join (man, uf_man) (a, b) (c, d) =
    (* Why3 terms and APRON variables must be kept consistent. So. First there is
     * the case where two different terms are linked to the same APRON variable.
     * One on them must be erased. *)
    (* And this takes care of one term linked to 2 variables. (They are made equal,
     * and then forgotten.) *)
    let c, b = join_uf (man, uf_man) b d c in
    let a = Dom.join man a c in
    a, b

  let join_list man l = match l with
    | [] -> assert false
    | t::q -> List.fold_left (join man) t q

  let push_label (man, uf_man) _ i (a, b) =
    Dom.push_label man uf_man.env i a, b

  let warning_t s t =
    Format.eprintf "-- warning: %s -- triggered by " s;
    Pretty.print_term Format.err_formatter t;
    Format.eprintf " of type ";
    Pretty.print_ty Format.err_formatter (Term.t_type t);
    Format.eprintf "@."

  let ident_ret =
    Ident.{pre_name = "$pat";
          pre_attrs = Sattr.empty;
          pre_loc   = None; }

  let access_field constr constr_args a i (proj, t) =
      match a.t_node with
      | Tapp (func, args) when func.ls_constr = 1 ->
        List.nth args i
      | Tvar _ | _ ->
        match proj with
        | None ->
          let return = create_vsymbol ident_ret t in
          let pat = List.mapi (fun k t ->
              if k = i then pat_var return else pat_wild t
                      ) constr_args in
          t_case a [t_close_branch (pat_app constr pat (t_type a)) (t_var return)]
        | Some s -> t_app s [a] (Some t)

  let get_subvalues a ity =
    let open Ty in
    let myty = t_type a in
    let aux ity =
      match myty.ty_node with
      | _ when ty_equal myty ty_bool -> []
      | _ when ty_equal myty ty_int -> [a, None]
      | Tyapp (tys, vars) ->
        begin
          let vars = Ty.ts_match_args tys vars in
          match (Ident.Mid.find tys.ts_name known_logical_ident).Decl.d_node with
          | Decl.Ddata ([_, [ls, ls_projs]]) ->
            let l =
              let my_ls_args = List.map (fun i -> Ty.ty_inst vars i) ls.ls_args in
              let args_projs = List.combine my_ls_args ls_projs in
              let inst (arg_type, proj) = match proj with
                | Some s -> Some s,
                             (match s.ls_value with
                              | Some t ->
                                 let l = Ty.ty_inst vars t in
                                 assert (Ty.ty_equal l arg_type);
                                 l
                              | None -> assert false)
                | None -> None, arg_type in
              let inst_args = List.map inst args_projs in
              List.mapi (access_field ls my_ls_args a) inst_args
            in
            begin
              match ity with
              | None -> List.map (fun a -> a, None) l
              | Some its ->
                 let pdecl = Pdecl.((find_its_defn known_pdecl its).itd_fields) in
                 List.combine l (List.map (fun a -> Some a) pdecl)
            end
          (*| Decl.Dtype ({ts_def = _; ts_args = _; _ }) ->
            (* untested code*)
            let () = assert false in
            aux ity*)
          | Decl.Ddata [_; _] ->
             warning_t "Multiple constructors is not supported in \
                        abstract interpretation." a; []
          | Decl.Ddata _ ->
             warning_t "Recursive types is not supported in abstract \
                        interpretation." a; []
          | Decl.Dtype _  ->
             (* This happens when a type is private or has an
                invariant: it can't be accesed * by the logic, so we
                give up and only look for projections by looking * at
                program projections. *)
            begin
              try
                let its = Ity.restore_its tys in
                (match ity with
                 | None -> ()
                 | Some s -> assert (Ity.its_equal its s));
                let pdecl = Pdecl.((find_its_defn known_pdecl its).itd_fields) in
                let f b =
                  let l = match Expr.(b.rs_logic) with
                    | Expr.RLls l -> l
                    | _ -> assert false in
                  let this_ty = Expr.(Ity.(ty_of_ity b.rs_cty.cty_result)) in
                  let ty = Ty.ty_inst vars this_ty in
                  t_app l [a] (Some ty), if ity = None then None else Some b
                in List.map f pdecl
              with Not_found -> failwith "could not restore its"
            end
          | Decl.Dind _ ->
             warning_t "Could not find type declaration (got inductive \
                        predicate)."
               a; []
          | Decl.Dlogic _ ->
             warning_t "Could not find type declaration (got logic \
                        declaration)."
               a; []
          | Decl.Dprop _ ->
            warning_t "Could not find type declaration (got propsition) for: "
              a; []
          | Decl.Dparam _ ->
            warning_t "Could not find type declaration (got param)."
              a; []
        end
      | Tyvar _ ->
         warning_t "Comparison of values with an abstract type, the \
                    interpretation will not be precise" a; []
    in aux ity

  exception Bad_domain of Dom.t

  let rec extract_term (man, uf_man) is_in (dom, b) v =
    let find_var a =
      try
        let candidate = Hashtbl.find uf_man.variable_mapping a in
        if is_in candidate then raise Not_found else candidate
      with Not_found ->
            try
              TermToVar.to_term b.uf_to_var a
            with Not_found ->
              raise (Bad_domain (Dom.forget_array man dom [|a|] false))
    in
    match Dom.get_linexpr man dom v with
    | Some l ->
      begin try
          let t = Ai_logic.varlist_to_term find_var l in
          assert (Ty.ty_equal (t_type t) Ty.ty_int); Some t
        with Bad_domain a -> extract_term (man, uf_man) is_in (a, b) v
      end
    | None -> None

  let to_term (man, uf_man) (a, b) =
    let find_var = fun a ->
      try Hashtbl.find uf_man.variable_mapping a
      with Not_found ->
        try TermToVar.to_term b.uf_to_var a
        with Not_found ->
          Format.eprintf "Couldn't find variable %s@." (Var.to_string a);
          raise Not_found
    in
    let t = Dom.to_term S.env (S.th_known, S.mod_known) man a find_var in
    let t = Union_find.fold_class (fun t a b ->
                let a = TermToClass.to_term uf_man.class_to_term a in
                let b = TermToClass.to_term uf_man.class_to_term b in
                t_and t (t_equ a b)) t b.classes
    in t


  (* let get_class_for_term_ro uf_man t =
   *   TermToClass.to_t uf_man.class_to_term t *)

  (* Get a set of (apron) linear expressions from a constraint stated
   * in why3 logic.
   *
   * The resulting list of linear expressions is weaker than the original
   * why3 formula.
   * In the most imprecise case, it returns an empty list.
   *)
  let meet_term: man -> Term.term -> (t -> t) =
    let meetid = ref 0 in
    fun (man, uf_man) t ->
      incr meetid;
      (* First inline everything, for instance needed for references
       * where !i is (!) i and must be replaced by (contents i) *)
      let t = t_replace_all t in
      (* Let's try to remove the nots that we can *)
      let t = t_descend_nots t in
      let var_of_term t =
        try Some (Term.Mterm.find t uf_man.apron_mapping)
        with Not_found -> None
      in

      (* Assuming that t is an arithmetic term, this computes the
       * number of ocurrence of variables
       * ando the constant of the arithmetic expression.
       * It returns (variables, constant)
       *
       * For instance, 4 + x + y set cst to 4, and constr
       * to [(x, 1), (y, 1)] *)
      let rec term_to_var_list rud coeff t =
        let re = term_to_var_list rud in
        let open Number in
        match t.t_node with
        | Tvar _ -> begin
            match var_of_term t with
            | Some var -> ([(var, coeff)], 0)
            | None -> Format.eprintf "Variable undefined: ";
                      Pretty.print_term Format.err_formatter t;
                      Format.eprintf "@."; failwith "undefined var" end
        | Tconst (Constant.ConstInt n) ->
          ([], coeff * (BigInt.to_int n.il_int))
        | Tapp (func, args) when Term.ls_equal func ad_int ->
          List.fold_left (fun (a, b) c ->
              let c, d = re coeff c in
              (a @ c, b + d)) ([], 0)args
        | Tapp (func, [a;b]) when Term.ls_equal func min_int ->
          let c, d = re coeff a in
          let e, f = re (-coeff) b in
          (c @ e, d + f)
        | Tapp (func, [a]) when Term.ls_equal func min_u_int ->
          re (-coeff)  a;
        | Tapp (func, [{t_node = Tconst (Constant.ConstInt n); _}; a])
        | Tapp (func, [a; {t_node = Tconst (Constant.ConstInt n); _};])
             when Term.ls_equal func mult_int ->
           re ((BigInt.to_int n.il_int) * coeff) a
        | _ -> (* maybe a record access *)
          begin
            match var_of_term t with
            | None ->
              begin
                try
                  let myvar = get_var_for_term uf_man rud t in
                  let cl = get_class_for_term uf_man t in
                  let classes = Union_find.union cl cl !rud.classes in
                  rud := { !rud with classes };
                  ([myvar, coeff], 0)
                with Not_found ->
                  Format.eprintf "REACHED END OF THE POOL@.@.@.@.@.";
                  raise (Not_handled t)
              end
            | Some s -> ([s, coeff], 0)
          end
      in

      (* This takes an epsilon-free formula and returns a list of linear
         expressions weaker than the original formula. *)
      let rec aux t =
        let is_int_comp ls t =
          Ty.ty_equal (t_type t) Ty.ty_int &&
            (ls_equal ps_equ ls || ls_equal lt_int ls ||
             ls_equal gt_int ls || ls_equal le_int ls ||
             ls_equal ge_int ls) in
        try
          match t.t_node with
          | Tbinop (Tand, a, b) ->
            let fa = aux a in
            let fb = aux b in
            (fun (d, a) -> fb (fa (d, a)))
          | Tbinop (Tor, a, b) ->
            let fa = aux a in
            let fb = aux b in
            (fun (d, a) ->
               let a1 = fa (d, a) in
               let a2 = fb (d, a) in
               join (man, uf_man) a1 a2)
          | Tapp (func, [a; b]) when is_int_comp func a ->
            (* FIXME: >, <=, >=, booleans *)
            let base_coeff, eq_type =
              if ls_equal ps_equ func then 1, Lincons1.EQ
              else if ls_equal lt_int func then 1, Lincons1.SUP
              else if ls_equal gt_int func then -1, Lincons1.SUP
              else if ls_equal le_int func then 1, Lincons1.SUPEQ
              else if ls_equal ge_int func then -1, Lincons1.SUPEQ
              else assert false
            in
            let g =
              if ls_equal ps_equ func then do_eq (man, uf_man) a b
              else fun x -> x
            in
            (fun (d, d') ->
               let d, d' = g (d, d') in
               let f = ref d' in
               let va, ca = term_to_var_list f (-base_coeff) a in
               let vb, cb = term_to_var_list f base_coeff b in
               let d' = !f in
               let c = ca + cb in
               let v = sum_list (va @ vb) in
               let expr = Linexpr1.make uf_man.env in
               let constr = List.map (fun (var, coeff) ->
                   Coeff.Scalar (Scalar.of_int coeff), var) v in
               Linexpr1.set_list expr constr None;
               let cons = Lincons1.make expr eq_type in
               Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int c));
               let arr = Lincons1.array_make uf_man.env 1 in
               Lincons1.array_set arr 0 cons;
               Dom.meet_lincons_array man d arr, d')
          | Tapp (func, [a;b]) when ls_equal ps_equ func ->
            let f_uf = do_eq (man, uf_man) a b in
            let subv_a = get_subvalues a None in
            let subv_b = get_subvalues b None in
            List.fold_left (fun f ((a, _), (b, _)) ->
                let g = aux (t_app ps_equ [a; b] None) in
                (fun abs -> f (g abs)))
              f_uf (List.combine subv_a subv_b)
          | Tif (a, b, c) ->
            let fa = aux a in
            let fa_not = aux (t_descend_nots a) in
            let fb = aux b in
            let fc = aux c in
            (fun d ->
               let a1 = fb (fa d) in
               let a2 = fc (fa_not d) in
               join (man, uf_man) a1 a2)
          | Ttrue -> (fun d -> d)
          | _ when t_equal t t_bool_true || t_equal t t_true -> (fun d -> d)
          | Tfalse -> (fun _ -> Dom.bottom man uf_man.env, empty_uf_domain)
          | _ when t_equal t t_bool_false || t_equal t t_false ->
             (fun _ -> Dom.bottom man uf_man.env, empty_uf_domain)
          | _ -> raise (Not_handled t)
        with Not_handled t ->
          Format.eprintf "Couldn't understand entirely the post condition: ";
          Pretty.print_term Format.err_formatter t;
          Format.eprintf "@.";
          (fun d -> d)
      in
      (fun d -> aux t d)

  let is_leq (man, uf_man) (a, b) (c, d) =
    let c', _ = join_uf (man, uf_man) b d c in
    let b_dom = Dom.is_leq man a c' in
    let b_uf = Union_find.is_leq b.classes d.classes in
    b_dom && b_uf

  let var_id = ref 0

  let ensure_variable uf_man v t =
    if not (Environment.mem_var uf_man.env v) then
      begin
        Hashtbl.add uf_man.variable_mapping v t;
        uf_man.env <- Environment.add uf_man.env [|v|] [||]
      end

  let add_lvariable_to_env (_, uf_man) vsym =
    incr var_id;
    let open Ty in
    let logical_term = t_var vsym in
    try let _ = Mterm.find logical_term uf_man.defined_terms in ()
    with Not_found ->
      uf_man.defined_terms <- Mterm.add logical_term () uf_man.defined_terms;
      ignore (Format.flush_str_formatter ());
      if Ty.ty_equal (t_type logical_term) ty_int then
        begin
          let reg_name =
            Format.asprintf "%d%a" !var_id Pretty.print_term logical_term in
          let v = Var.of_string reg_name in
          assert (not (Environment.mem_var uf_man.env v));
          ensure_variable uf_man v logical_term;
          uf_man.apron_mapping <-
            Term.Mterm.add logical_term v uf_man.apron_mapping
        end
      else if Ty.ty_equal (t_type logical_term) ty_bool then
        begin
          let reg_name =
            Format.asprintf "%d%a" !var_id Pretty.print_term logical_term in
          let v =
            Var.of_string reg_name in
          assert (not (Environment.mem_var uf_man.env v));
          ensure_variable uf_man v logical_term;
          uf_man.apron_mapping <-
            Term.Mterm.add logical_term v uf_man.apron_mapping;
        end
      else
        begin
          let subv = get_subvalues logical_term None in
          List.iter (fun (t, _) ->
              ignore (Format.flush_str_formatter ());
              let v = Format.asprintf "%d%a.%a"
                        !var_id Pretty.print_term logical_term
                        Pretty.print_term t in
              let v = Var.of_string v in
              ensure_variable uf_man v t;
              uf_man.apron_mapping <- Term.Mterm.add t v uf_man.apron_mapping) subv
        end


  let cached_vreturn = ref (Ty.Mty.empty)

  let ident_ret =
    Ident.{pre_name  = "$reg";
           pre_attrs = Ident.Sattr.empty;
           pre_loc   = None; }

  let create_vreturn man ty =
    assert (not (Ty.ty_equal ty Ity.ty_unit));
    try Ty.Mty.find ty !cached_vreturn with Not_found ->
      let v  = Term.create_vsymbol ident_ret ty in
      add_lvariable_to_env man v;
      cached_vreturn := Ty.Mty.add ty v !cached_vreturn;
      v

  let add_variable_to_env (man, uf_man) psym =
    incr var_id;
    let open Expr in
    let open Ty in
    let open Ity in
    let open Pretty in
    let variable_type = psym.pv_ity in
    let logical_term =
      match Expr.term_of_expr ~prop:false (Expr.e_var psym) with
      | Some s -> s
      | None -> assert false
    in
    ignore (Format.flush_str_formatter ());
    match variable_type.ity_node, (Term.t_type logical_term).ty_node with
    | _ when Ty.ty_equal (t_type logical_term) ty_int ->
      let reg_name =
        Format.asprintf "%d%a" !var_id print_term logical_term in
      let v = Var.of_string reg_name in
      assert (not (Environment.mem_var uf_man.env v));
      ensure_variable uf_man v logical_term;
      uf_man.apron_mapping <-
        Term.Mterm.add logical_term v uf_man.apron_mapping
    | _ when Ty.ty_equal (t_type logical_term) ty_bool ->
      let reg_name = Format.asprintf "%d%a" !var_id print_term logical_term in
      let v = Var.of_string reg_name in
      assert (not (Environment.mem_var uf_man.env v));
      ensure_variable uf_man v logical_term;
      uf_man.apron_mapping <- Term.Mterm.add logical_term v uf_man.apron_mapping;
    | _ when ity_equal variable_type Ity.ity_unit-> ()
    | Ityreg reg, Tyapp (_, _) ->
      begin
        let reg_name = Format.asprintf "%a" print_reg_name reg in
        let vret = create_vreturn (man, uf_man) (t_type logical_term) in
        let vret = t_var vret in
        let subv = get_subvalues vret (Some reg.reg_its) in
        let subv_r = get_subvalues logical_term (Some reg.reg_its) in
        let subv = List.combine subv subv_r in
        let proj_list =
          List.fold_left
            (fun acc ((generic_region_term, pfield), (real_term, _)) ->
              let pfield = match pfield with
                | Some s -> s
                | None -> assert false
              in
              ignore (Format.flush_str_formatter ());
              let v = Pretty.print_term Format.str_formatter generic_region_term
                      |> Format.flush_str_formatter
                      |> Format.sprintf "r$%s.%s" reg_name
                      |> Var.of_string
              in
              ensure_variable uf_man v real_term;
              let accessor = match pfield.rs_field with
                | Some s -> s
                | None -> assert false
              in
              uf_man.apron_mapping <-
                Term.Mterm.add real_term v uf_man.apron_mapping;
              (accessor, real_term) :: acc
            ) [] subv
        in
        let old_projs, old_vars =
          try
            Mreg.find reg uf_man.region_mapping,
            Mreg.find reg uf_man.region_var
          with Not_found -> [], []
        in
        uf_man.region_mapping <-
          Mreg.add reg (proj_list @ old_projs) uf_man.region_mapping;
        uf_man.region_var <-
          Mreg.add reg (psym.pv_vs :: old_vars) uf_man.region_var
      end
    | Ityapp _, _ ->
      let subv = get_subvalues logical_term None in
      List.iter (fun (t, _) ->
          ignore (Format.flush_str_formatter ());
          let v = Format.asprintf "%d%a.%a" !var_id print_pv
                    psym print_term t in
          let v = Var.of_string v in
          ensure_variable uf_man v t;
          uf_man.apron_mapping <- Term.Mterm.add t v uf_man.apron_mapping) subv;
    | _ ->
       (* We can safely give up on a, as no integer variable can
          descend from it (because it is well typed) *)
       Format.eprintf "Variable could not be added properly: ";
       Pretty.print_term Format.err_formatter logical_term;
       Format.eprintf " of type ";
       print_ity Format.err_formatter variable_type;
       Format.eprintf "@.";
       ()

  let is_in t myt =
    let found = ref false in
    let rec is_in myt =
      if t_equal t myt then found := true;
      t_map is_in myt
    in
    is_in myt |> ignore;
    !found

  let rec tdepth t =
    1 + t_fold (fun k' t -> max (tdepth t) k') 0 t

  let rec forget_term (man, uf_man) t =
    let f = fun (a, b) ->
      let a, b =
        try
          let var = Term.Mterm.find t uf_man.apron_mapping in
          let t' = extract_term (man, uf_man) (is_in t) (a, b) var in
          let a, b = match t' with
            | Some t' -> do_eq (man, uf_man) t t' (a, b)
            | None -> a, b
          in
          Dom.forget_array man a [|var|] false, b
        with Not_found -> a, b
      in
      let (a, b), alt =
        try
          let cl = Union_find.get_class (get_class_for_term uf_man t) b.classes in
          let tl = List.map (TermToClass.to_term uf_man.class_to_term) cl in
          let tc = List.find (fun t' -> not (is_in t t')) tl in
          do_eq (man, uf_man) tc t (a, b), Some tc
        with Not_found -> (a, b), None
      in
      let all_values' = Union_find.flat b.classes in
      let all_values' = List.map (fun c ->
          c, TermToClass.to_term uf_man.class_to_term c) all_values' in
      let all_values =
          (get_class_for_term uf_man t, t) ::
          List.filter (fun (_, a) ->
              is_in t a && not (t_equal t a) ) all_values' in
      let int_values, other_values =
        List.partition (fun (_, t) ->
            Ty.ty_equal (t_type t) Ty.ty_int) all_values in
      let b = List.fold_left (fun b (cl, _) ->
          let classes = snd (Union_find.forget cl b.classes) in
          { b with classes}) b other_values in
      let forgot_var = t in
      let a, b = List.fold_left (fun (a, b) (cl, t) ->
          let old_cl = b.classes in
          let classes = snd (Union_find.forget cl b.classes) in
          let b = { b with classes } in
          try
            let apron_var = TermToVar.to_t b.uf_to_var t in
            let uf_to_var = TermToVar.remove_term b.uf_to_var t in
            try
              let alt_cl = Union_find.get_class cl old_cl in
              let alt_cl, classes = match alt with
                | Some alt ->
                   let new_t = replaceby forgot_var alt t in
                   let new_cl = get_class_for_term uf_man new_t in
                   new_cl :: alt_cl,
                   snd (Union_find.forget cl (Union_find.union cl new_cl old_cl))
                | None -> alt_cl, b.classes
              in
              let f c =
                if c <> cl then
                  let t = TermToClass.to_term uf_man.class_to_term c in
                  try TermToVar.to_t b.uf_to_var t |> ignore; None
                  with Not_found -> if tdepth t < 4 then Some t else None
                else None
              in
              let alt_cl = List.map f alt_cl in
              let cl_t = List.find (function Some _ -> true | _ -> false) alt_cl in
              let alt_term = match cl_t with Some x -> x | _ -> assert false in
              let uf_to_var = TermToVar.add uf_to_var alt_term apron_var in
              a, { b with uf_to_var; classes }
            with Not_found ->
              Dom.forget_array man a [|apron_var|] false,
              { b with var_pool = VarPool.add apron_var b.var_pool; uf_to_var }
          with Not_found ->  a, b
        ) (a, b) int_values
      in
      a, b
    in
    List.fold_left (fun f (a, _) ->
        if t_equal a t then f
        else (fun d  -> f (forget_term (man, uf_man) a d)))
      f (get_subvalues t None)

  let forget_var m v = forget_term m (t_var v)

  let forget_region (man, uf_man) v _ =
    let members = Ity.Mreg.find v uf_man.region_mapping |> List.map snd in
    let vars = Ity.Mreg.find v uf_man.region_var in
    let f = List.fold_left (fun f t ->
        let a = forget_term (man, uf_man) t in
        fun x -> f x |> a) (fun x -> x) members in
    List.fold_left (fun f v ->
        fun (d, ud) ->
          let acl = get_class_for_term uf_man (t_var v) in
          let ud = { ud with classes = snd (Union_find.forget acl ud.classes) } in
          let d = f (d, ud) in
          d) f vars

  let widening (man, uf_man) (a, b) (c, d) =
    let c, e = join_uf (man, uf_man) b d c in
    let a = Dom.widening man a c in
    a, e

  let is_join_precise (man, uf_man) (a, b) (c, d) =
    let c, b = join_uf (man, uf_man) b d c in
    match Dom.is_join_precise man a c with
    | None -> None
    | Some d -> Some (d, b)

  let make_consistent _ a b = a, b

end
