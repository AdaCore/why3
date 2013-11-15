signature WHY3 =
sig
  val setup: theory -> theory
end

structure Why3: WHY3 =
struct

(**** XML utilities ****)

fun get_opt_att s atts = AList.lookup (op =) atts s;

fun get_att s atts = (case get_opt_att s atts of
    SOME x => x
  | NONE => error ("Missing attribute " ^ s));

fun get_att_default x s atts = (case get_opt_att s atts of
    SOME y => y
  | NONE => x);

fun get_name atts = get_att "name" atts;

fun variant fs (XML.Elem ((s, atts), ts)) =
      (case AList.lookup (op =) fs s of
         SOME f => (f atts ts handle General.Match =>
           error ("Failed to parse element " ^ s))
       | NONE => error ("Bad element: " ^ s))
  | variant _ _ = error "Element expected";

fun elem s f (XML.Elem ((s', atts), ts)) =
      if s = s' then f atts ts
      else error ("Element " ^ s ^ " expected")
  | elem _ _ _ = error "Element expected";

fun optional _ x [] = x
  | optional f _ [x] = f x;

fun option _ [] = NONE
  | option f [x] = SOME (f x);

fun get_bool s atts = (case get_att_default "false" s atts of
    "false" => false
  | "true" => true
  | _ => error "Bad value for boolean attribute");

fun strip_whspc (XML.Elem (p, ts)) =
      SOME (XML.Elem (p, map_filter strip_whspc ts))
  | strip_whspc (txt as XML.Text s) =
      if forall Symbol.is_blank (raw_explode s)
      then NONE else SOME txt;

fun parse_xml s =
  (case strip_whspc (XML.parse s) of
     SOME x => x
   | NONE => error "Bad input");


(**** terms and types ****)

(* replace occurrences of dummy_pattern by distinct variables *)
fun replace_dummies (Const (@{const_name dummy_pattern}, T)) used =
      let val (x, used') = Name.variant "x" used
      in (Free (x, T), used') end
  | replace_dummies (t $ u) used =
      let
        val (t', used') = replace_dummies t used;
        val (u', used'') = replace_dummies u used';
      in (t' $ u', used'') end
  | replace_dummies t used = (t, used);

fun make_case t ps =
  Syntax.const @{const_name case_guard} $ @{term True} $ t $
  fold_rev (fn (l, r) => fn u =>
      let val (l', _) = replace_dummies l
        (Name.context |>
         Term.declare_term_frees l |>
         Term.declare_term_frees r)
      in
        Syntax.const @{const_name case_cons} $
        fold (fn p => fn b =>
            Syntax.const @{const_name case_abs} $
            Term.absfree p b)
          (Term.add_frees l [])
          (Syntax.const @{const_name case_elem} $ l' $ r) $ u
      end)
    ps (Syntax.const @{const_name case_nil});

val get_tvar = prefix "'" o get_name;

fun typ f = variant
  [("type", fn atts => fn Ts => Type (f atts, map (typ f) Ts)),
   ("tvar", fn atts => fn [] => TFree (get_tvar atts, dummyS)),
   ("fun", fn _ => fn Ts as _ :: _ => op ---> (split_last (map (typ f) Ts))),
   ("pred", fn _ => fn Ts => map (typ f) Ts ---> @{typ bool}),
   ("prodt", K
      (fn [] => HOLogic.unitT
        | Ts => foldr1 HOLogic.mk_prodT (map (typ f) Ts)))];

fun term f g = variant
  [("const", fn atts => fn Ts =>
      Const (f atts, optional (typ g) dummyT Ts)),
   ("var", fn atts => fn Ts =>
      Free (get_name atts, optional (typ g) dummyT Ts)),
   ("abs", fn atts => fn [T, t] =>
      Term.absfree (get_name atts, typ g T) (term f g t)),
   ("app", fn _ => fn t :: ts => list_comb (term f g t, map (term f g) ts)),
   ("num", fn atts => fn Ts => HOLogic.mk_number
      (optional (typ g) dummyT Ts)
      (case Int.fromString (get_att "val" atts) of SOME i => i)),
   ("case", fn _ => fn t :: ps => make_case (term f g t)
      (map (elem "pat" (K (fn [l, r] => (term f g l, term f g r)))) ps)),
   ("prod", K
      (fn [] => HOLogic.unit
        | ts => foldr1 HOLogic.mk_prod (map (term f g) ts)))];


(**** declarations ****)

datatype decl =
    Lemma of string * term list * term list
  | Axiom of string * term list
  | Typedecl of string * string list * typ option
  | Param of string * typ
  | Definition of term
  | Datatype of (string * string list * (string * typ list) list) list
  | Inductive of bool * (string * typ * (string * term) list) list
  | Function of term list

fun err_unfinished () = error "An unfinished Why3 environment is still open.";
fun err_no_env () = error "No Why3 environment is currently open.";

fun merge_names ((consts1, types1), (consts2, types2)) =
  (Symtab.merge (op =) (consts1, consts2),
   Symtab.merge (op =) (types1, types2));

structure Why3_Data = Theory_Data
(
  type T =
    {theories: (string Symtab.table * string Symtab.table) Symtab.table,
     env:
       {thyname: string,
        decls: decl list,
        vcs: (thm list option * term list * term list) Symtab.table} option}
  val empty : T = {theories = Symtab.empty, env = NONE}
  val extend = I
  fun merge ({theories = theories1, env = NONE},
        {theories = theories2, env = NONE}) =
        {theories = Symtab.join (K merge_names) (theories1, theories2),
         env = NONE}
    | merge _ = err_unfinished ()
)

fun lookup_vc thy name =
  (case Why3_Data.get thy of
     {env = SOME {vcs, ...}, ...} => Symtab.lookup vcs name
   | _ => NONE);

val is_closed = is_none o #env o Why3_Data.get;

fun mk_vc name_concl prems concls =
  (Element.Assumes (map_index (fn (i, t) =>
     ((Binding.name ("H" ^ string_of_int (i + 1)), []), [(t, [])])) prems),
   Element.Shows (map_index (fn (i, t) =>
     (if name_concl then (Binding.name ("C" ^ string_of_int (i + 1)), [])
      else Attrib.empty_binding,
      [(t, [HOLogic.mk_Trueprop
          (Var (("C", i + 1), HOLogic.boolT))])])) concls));

fun get_vc thy vc_name =
  (case lookup_vc thy vc_name of
    SOME (proved, prems, concls) =>
      if is_some proved then
        error ("The verification condition " ^
          quote vc_name ^ " has already been proved.")
      else mk_vc false prems concls
  | NONE => error ("There is no verification condition " ^
      quote vc_name ^ "."));

fun pp_vcs msg vcs = Pretty.big_list msg (map (Pretty.str o fst) vcs);

fun pp_open_vcs [] = Pretty.str "All verification conditions have been proved."
  | pp_open_vcs vcs = pp_vcs
      "The following verification conditions remain to be proved:" vcs;

fun partition_vcs vcs = Symtab.fold_rev
  (fn (name, (SOME thms, ps, cs)) =>
        apfst (cons (name, (thms, ps, cs)))
    | (name, (NONE, ps, cs)) =>
        apsnd (cons (name, (ps, cs))))
  vcs ([], []);

fun insert_break prt = Pretty.blk (0, [Pretty.fbrk, prt]);

fun print_open_vcs f vcs =
  (Pretty.writeln (f (pp_open_vcs (snd (partition_vcs vcs)))); vcs);

fun mark_proved name thms = Why3_Data.map (fn
    {theories,
     env = SOME {thyname, decls, vcs}} =>
      {theories = theories,
       env = SOME {thyname = thyname, decls = decls,
         vcs = print_open_vcs insert_break (Symtab.map_entry name
           (fn (_, ps, cs) => (SOME thms, ps, cs)) vcs)}}
  | x => x);

fun add_name kind sel th (p as (x, _)) tab =
  Symtab.map_entry th (sel (Symtab.update_new p)) tab
  handle Symtab.DUP _ =>
    error ("The " ^ kind ^ " " ^ x ^ " is already defined.");

fun add_item add intrn x thy = Why3_Data.map
  (fn {theories, env = env as SOME {thyname, ...}} =>
        {theories = add thyname (x, intrn thy x) theories,
         env = env}
    | _ => err_no_env ()) thy;

val add_const = add_item (add_name "constant" apfst) Sign.intern_const;
val add_type = add_item (add_name "type" apsnd) Sign.intern_type;

fun lookup_name kind sel tab s s' = (case Symtab.lookup tab s of
    NONE => error ("The theory " ^ s ^ " was not found")
  | SOME tab' => (case Symtab.lookup (sel tab') s' of
        NONE => error ("The " ^ kind ^ " " ^ s' ^
          " was not found in theory " ^ s)
      | SOME name => name));

fun lookup_const tab = lookup_name "constant" fst tab;
fun lookup_type tab = lookup_name "type" snd tab;

fun prep_name lookup ctxt atts =
  (case Why3_Data.get (Proof_Context.theory_of ctxt) of
     {theories, env = SOME {thyname, ...}} =>
       let val name = get_name atts
       in case (get_bool "local" atts, get_opt_att "path" atts) of
           (false, NONE) => name
         | (true, _) => lookup theories thyname name
         | (_, SOME thyname') => lookup theories thyname' name
       end
   | _ => err_no_env ());

fun read_type ctxt x = Syntax.check_typ ctxt
  (typ (prep_name lookup_type ctxt) x);

fun read_term ctxt x = Syntax.check_term ctxt
  (term (prep_name lookup_const ctxt) (prep_name lookup_type ctxt) x);

fun read_prop ctxt x = HOLogic.mk_Trueprop (read_term ctxt x);

fun prep_datatypes ctxt dts =
  let val ctxt' = fold (fn (s, args, _) =>
    Typedecl.typedecl (Binding.name s, map (rpair dummyS) args, NoSyn) #>
    snd #> Local_Theory.background_theory (add_type s)) dts ctxt
  in map (fn (b, args, constrs) =>
    (b, args, map (apsnd (map (read_type ctxt'))) constrs)) dts
  end;

fun read_statement ctxt f atts [prems, concls] = f
  (get_name atts,
   elem "prems" (K (map (read_prop ctxt))) prems,
   elem "concls" (K (map (read_prop ctxt))) concls);

val read_ty_params = elem "params" (K (map (elem "param" (K o get_tvar))));

fun read_decl ctxt = variant
  [("lemma", read_statement ctxt Lemma),
   ("axiom", read_statement ctxt (fn (name, prems, concls) =>
      Axiom (name, map (fn concl =>
        Logic.list_implies (prems, concl)) concls))),
   ("typedecl", fn atts => fn params :: rhs => Typedecl
      (get_name atts,
       read_ty_params params,
       option (read_type ctxt) rhs)),
   ("param", fn atts => fn [ty] => Param
      (get_name atts, read_type ctxt ty)),
   ("definition", fn _ => fn [t] => Definition (read_prop ctxt t)),
   ("datatypes", fn _ => fn xs => Datatype (prep_datatypes ctxt
      (map (elem "datatype" (fn atts => fn [params, constrs] =>
         (get_name atts,
          read_ty_params params,
          elem "constrs"
            (K (map (elem "constr" (fn atts => fn ys =>
               (get_name atts, ys))))) constrs))) xs))),
   ("inductive", fn atts => fn xs => Inductive
      (get_bool "coind" atts,
       map (elem "pred" (fn atts => fn ty :: rls =>
         (get_name atts,
          read_type ctxt ty,
          map (elem "rule" (fn atts => fn [prems, concl] =>
            (get_name atts,
             Logic.list_implies
               (elem "prems" (K (map (read_prop ctxt))) prems,
                read_prop ctxt concl)))) rls))) xs)),
   ("function", fn _ => fn xs => Function
      (map (elem "eqn" (fn atts => fn [t] =>
         read_prop ctxt t)) xs))];

val head_of_eqn =
  HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst #> head_of #> dest_Free;

fun globalize f thy =
  Local_Theory.exit_global (f (Named_Target.theory_init thy));

(* split up term containing case combinators into several terms *)
fun expand_cases ctxt t =
  let
    fun rename fmap = Term.map_aterms
      (fn Free (s, T) => Free (the_default s (AList.lookup (op =) fmap s), T)
        | t => t);

    fun rename_case used (l, r) =
      let val (fmap, _) = fold_map
        (fn s => apfst (pair s) o Name.variant s)
        (Term.add_free_names l []) used
      in (rename fmap l, rename fmap r) end;

    fun strip_case used t =
      if null (loose_bnos t)
      then Option.map (apsnd (map (rename_case used)))
        (Case_Translation.strip_case ctxt false t)
      else NONE;

    fun mk_ctxt f = Option.map (fn (x, ps) => (x, map (apsnd f) ps));

    fun strip_case' used t = (case strip_case used t of
        NONE => (case t of
            t1 $ t2 => (case strip_case' used t1 of
                NONE => mk_ctxt (fn u => t1 $ u) (strip_case' used t2)
              | p => mk_ctxt (fn u => u $ t2) p)
          | Abs (s, T, r) => mk_ctxt (fn u => Abs (s, T, u))
              (strip_case' used r)
          | _ => NONE)
      | p => p);

    fun expand t =
      (case strip_case' (Term.declare_term_frees t Name.context) t of
         NONE => [t]
       | SOME (x, ps) => maps (fn (l, r) =>
           expand (Term.subst_atomic [(x, l)] r)) ps)
  in expand t end;

fun mk_decl (Axiom (s, ts)) =
      Specification.axiomatization
        [] [((Binding.name s, []), ts)] #> snd
  | mk_decl (Typedecl (s, args, opt_rhs)) =
      globalize (case opt_rhs of
         NONE => Typedecl.typedecl
           (Binding.name s, map (rpair dummyS) args, NoSyn) #> snd
       | SOME T => Typedecl.abbrev
           (Binding.name s, args, NoSyn) T #> snd) #>
      add_type s
  | mk_decl (Param (s, T)) =
      Specification.axiomatization
        [(Binding.name s, SOME T, NoSyn)] [] #> snd #>
      add_const s
  | mk_decl (Definition eqn) =
      globalize (Specification.definition
        (NONE, (Attrib.empty_binding, eqn)) #> snd) #>
      add_const (fst (head_of_eqn eqn))
  | mk_decl (Datatype dts) =
      Datatype.add_datatype Datatype_Aux.default_config
        (map (fn (s, args, constrs) =>
           ((Binding.name s, map (rpair dummyS) args, NoSyn),
            map (fn (s', Ts) =>
              (Binding.name s', Ts, NoSyn)) constrs)) dts) #> snd #>
      fold (fn (s, _, constrs) => add_type s #>
        fold (add_const o fst) constrs) dts
  | mk_decl (Inductive (coind, preds)) =
      Inductive.add_inductive_global
        {quiet_mode = true, verbose = false,
         alt_name = Binding.empty, coind = coind,
         no_elim = false, no_ind = false, skip_mono = false}
        (map (fn (s, T, _) => ((Binding.name s, T), NoSyn)) preds) []
        (maps (map (apfst (rpair [] o Binding.name)) o #3) preds) [] #> snd #>
      fold (add_const o #1) preds
  | mk_decl (Function eqns) =
      let val eqns' = map head_of_eqn eqns
      in
        globalize (fn lthy => Function_Fun.add_fun
          (map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) eqns')
          (map (pair Attrib.empty_binding) (maps (expand_cases lthy) eqns))
          Function_Fun.fun_config lthy) #>
        fold (add_const o fst) eqns'
      end
  | mk_decl _ = I;

fun init_decls thyname consts types = Why3_Data.map
  (fn {theories, env = NONE} =>
        {theories = Symtab.update_new
           (thyname, (Symtab.make consts, Symtab.make types))
           theories handle Symtab.DUP _ =>
             error ("Theory " ^ thyname ^ " has already been loaded."),
         env = SOME
           {thyname = thyname,
            decls = [],
            vcs = Symtab.empty}}
    | _ => err_unfinished ());

fun put_decls decls = Why3_Data.map
  (fn {theories, env = SOME {thyname, ...}} =>
        {theories = theories,
         env = SOME
           {thyname = thyname,
            decls = decls,
            vcs = print_open_vcs I (fold
              (fn Lemma (s, ps, cs) => Symtab.update_new (s, (NONE, ps, cs))
                | _ => I) decls Symtab.empty
              handle Symtab.DUP k => error ("Verification condition " ^ k ^
                " has already been declared."))}}
    | _ => err_no_env ());

fun close incomplete thy =
  thy |>
  Why3_Data.map (fn
      {theories, env = SOME {thyname, vcs, ...}} =>
        let
          val (proved, unproved) = partition_vcs vcs;
          val _ = Thm.join_proofs (maps (#1 o snd) proved)
        in
          (if null unproved
           then writeln ("Finished Why3 theory " ^ thyname)
           else (if incomplete then warning else error)
             (Pretty.string_of (pp_open_vcs unproved));
           {theories = theories, env = NONE})
        end
    | _ => err_no_env ()) |>
  Sign.parent_path;

fun realized_decl (Param _) = true
  | realized_decl (Typedecl (_, _, NONE)) = true
  | realized_decl _ = false;

fun collect_realized ds = fold
  (fn Param (s, _) => apfst (insert (op =) s)
    | Typedecl (s, _, NONE) => apsnd (insert (op =) s)
    | _ => I) ds ([], []);

fun process_decls consts types x = elem "theory" (fn atts =>
  (fn imports :: xs => elem "realized" (fn _ => fn rs => fn thy =>
        let
          val thyname = get_name atts;
          val realize = get_bool "realize" atts;
          val (ds, thy') = thy |>
            Sign.add_path thyname |>
            init_decls thyname consts types |>
            fold_map (fn x => fn thy =>
              let val d = read_decl (Named_Target.theory_init thy) x
              in
                (d, ((not realize orelse not (realized_decl d)) ? mk_decl d) thy)
              end) xs
        in put_decls ds thy' end) imports
    | _ => error "Bad theory specification")) x


(**** pretty printing ****)

fun string_of_status NONE = "(* unproved *)"
  | string_of_status (SOME _) = "(* proved *)";

fun pretty_typ s [] = Pretty.str s
  | pretty_typ s [v] = Pretty.block
      [Pretty.str v, Pretty.brk 1, Pretty.str s]
  | pretty_typ s vs = Pretty.block
      [Pretty.list "(" ")" (map Pretty.str vs), Pretty.brk 1, Pretty.str s];

fun blocks prfx1 prfx2 xs f = fst (fold_map (fn x => fn prfx =>
    (Pretty.block (Pretty.str prfx :: Pretty.brk 1 :: f x),
     prfx2))
  xs prfx1);

fun pretty_decl (p, f) ctxt (Lemma (s, prems, concls)) =
      let
        val SOME (opt, _, _) = lookup_vc (Proof_Context.theory_of ctxt) s;
        val ctxt' = fold Variable.auto_fixes (prems @ concls) ctxt;
        val (context, stmt) = mk_vc true prems concls
      in
        if p opt then
          SOME (Pretty.big_list ("lemma " ^ s ^ ": " ^ f opt)
            (Element.pretty_ctxt ctxt' context @
             Element.pretty_stmt ctxt' stmt))
        else NONE
      end
  | pretty_decl _ ctxt (Axiom (s, ts)) =
      let val ctxt' = fold Variable.auto_fixes ts ctxt
      in SOME (Pretty.block
        ([Pretty.str "axiomatization where", Pretty.brk 1,
          Pretty.str s, Pretty.str ":", Pretty.brk 1] @
         separate (Pretty.brk 1)
           (map (Pretty.quote o Syntax.pretty_term ctxt') ts)))
      end
  | pretty_decl _ ctxt (Typedecl (s, args, opt_rhs)) = SOME (Pretty.block
      (case opt_rhs of
         NONE => [Pretty.str "typedecl", Pretty.brk 1,
           pretty_typ s args]
       | SOME T => [Pretty.str "type_synonym", Pretty.brk 1,
           pretty_typ s args, Pretty.str " =", Pretty.brk 1,
           Pretty.quote (Syntax.pretty_typ ctxt T)]))
  | pretty_decl _ ctxt (Param (s, T)) = SOME (Pretty.block
      [Pretty.str "axiomatization", Pretty.brk 1,
       Pretty.str s, Pretty.str " ::", Pretty.brk 1,
       Pretty.quote (Syntax.pretty_typ ctxt T)])
  | pretty_decl _ ctxt (Definition eqn) =
      let
        val ctxt' = Variable.auto_fixes eqn ctxt;
        val (s, T) = head_of_eqn eqn
      in SOME (Pretty.block [Pretty.str "definition ", Pretty.str s,
        Pretty.str " ::", Pretty.brk 1,
        Pretty.quote (Syntax.pretty_typ ctxt' T),
        Pretty.str " where", Pretty.fbrk,
        Pretty.quote (Syntax.pretty_term ctxt' eqn)])
      end
  | pretty_decl _ ctxt (Datatype dts) = SOME (Pretty.chunks
      (blocks "datatype" "and" dts (fn (s, args, constrs) =>
         [pretty_typ s args,
          Pretty.str " =", Pretty.brk 1] @
          Pretty.separate " |"
            (map (fn (s', Ts) => Pretty.block
                 (separate (Pretty.brk 1) (Pretty.str s' ::
                    (map (Pretty.quote o
                       Syntax.pretty_typ ctxt) Ts))))
               constrs))))
  | pretty_decl _ ctxt (Inductive (coind, preds)) =
      let val ctxt' = fold (fold (Variable.auto_fixes o snd) o #3) preds ctxt
      in
        SOME (Pretty.chunks
          (blocks ((coind ? prefix "co") "inductive") "and" preds
             (fn (s, T, _) =>
                [Pretty.str s, Pretty.str " ::", Pretty.brk 1,
                 Pretty.quote (Syntax.pretty_typ ctxt' T)]) @
           Pretty.str "where" ::
           blocks " " "|" (maps #3 preds) (fn (s, t) =>
             [Pretty.str s, Pretty.str ":",
              Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt' t)])))
      end
  | pretty_decl _ ctxt (Function eqns) =
      let val ctxt' = fold Variable.auto_fixes eqns ctxt
      in
        SOME (Pretty.chunks
          (blocks "fun" "and" eqns (fn t =>
             let val (s, T) = head_of_eqn t
             in
               [Pretty.str s, Pretty.str " ::", Pretty.brk 1,
                Pretty.quote (Syntax.pretty_typ ctxt' T)]
             end) @
           Pretty.str "where" ::
           blocks " " "|" eqns
             (single o Pretty.quote o Syntax.pretty_term ctxt')))
      end;

fun show_status thy sel =
  (case Why3_Data.get thy of
     {env = SOME {decls, ...}, ...} =>
       Pretty.writeln (Pretty.chunks2 (map_filter (pretty_decl sel
         (Proof_Context.init_global thy)) decls))
   | _ => ());


(**** commands ****)

fun why3_open ((name, consts), types) thy = process_decls
  (map (apsnd (Sign.intern_const thy)) consts)
  (map (apsnd (Sign.intern_type thy)) types)
  (parse_xml (snd (Thy_Load.load_file thy (Path.explode name)))) thy;

fun prove_vc vc_name lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val (ctxt, stmt) = get_vc thy vc_name
  in
    Specification.theorem Thm.theoremK NONE
      (fn thmss => (Local_Theory.background_theory
         (mark_proved vc_name (flat thmss))))
      (Binding.name vc_name, []) [] [ctxt] stmt false lthy
  end;

val _ =
  Outer_Syntax.command @{command_spec "why3_open"}
    "open a new Why3 environment and load a Why3-generated .xml file"
    (Parse.name --
     Scan.optional (Parse.reserved "constants" |-- Parse.!!! (Scan.repeat1
       (Parse.name --| Args.$$$ "=" -- Parse.!!! Parse.xname))) [] --
     Scan.optional (Parse.reserved "types" |-- (Scan.repeat1
       (Parse.name --| Args.$$$ "=" -- Parse.!!! Parse.xname))) [] >>
     (Toplevel.theory o why3_open));

val _ =
  Outer_Syntax.command @{command_spec "why3_vc"}
    "enter into proof mode for a specific verification condition"
    (Parse.name >> (fn name =>
      (Toplevel.print o Toplevel.local_theory_to_proof NONE (prove_vc name))));

val _ =
  Outer_Syntax.improper_command @{command_spec "why3_status"}
    "show the name and state of all loaded verification conditions"
    (Scan.optional
       (Args.parens
          (   Args.$$$ "proved" >> K (is_some, K "")
           || Args.$$$ "unproved" >> K (is_none, K "")))
       (K true, string_of_status) >> (fn args =>
        Toplevel.keep (fn state => show_status (Toplevel.theory_of state) args)))

val _ =
  Outer_Syntax.command @{command_spec "why3_end"}
    "close the current Why3 environment"
    (Scan.optional (@{keyword "("} |-- Parse.!!!
         (Parse.reserved "incomplete" --| @{keyword ")"}) >> K true) false >>
       (Toplevel.theory o close));

val setup = Theory.at_end (fn thy =>
  let
    val _ = is_closed thy
      orelse error ("Found the end of the theory, " ^
        "but the last Why3 environment is still open.")
  in NONE end);

end;
