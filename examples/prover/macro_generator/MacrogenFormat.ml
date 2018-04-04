
type 'n types =
  | TypeVar of 'n
  | DeclaredType of 'n

type 'n constructor =
  | Var
  | BCons of 'n * ( 'n * 'n types option) list * 'n types list
    (* BCons (C , [ t,u ; t2,u2 ] [ v1 ; v2 ; v3 ] :
       C : [ x_t : u1 . [ x_t2 : u2 . v1 v2 v3 ] ].
       x_{t} is bound at the right as a variable for declared type t. *)

type 'n typedef =
  (* TypeAssumption (t,[v_1...v_n] : assume
     type t using variables in types v_1...v_n. *)
  | TypeAssumption of 'n * 'n list
  (* Add definition. The list may be incomplete/contains variables
     not really used. In the second case, the variables will be added. *)
  | TypeDefinition of 'n * 'n constructor list * 'n list

type 'n decls = { var_parameters : 'n list ;
  binder_types : 'n typedef list }

let rec mapt f = function
  | DeclaredType t -> DeclaredType ( f t )
  | TypeVar x -> TypeVar (f x)

let mapc f = function
  | BCons ( c , b , e ) -> BCons ( f c , List.map (fun (x,y) -> match y with
    | None -> f x , None
    | Some y -> f x , Some (mapt f y) ) b ,
    List.map (mapt f) e )
  | Var -> Var

let mapdef f = function
  | TypeDefinition ( t , c , fv ) ->
    TypeDefinition ( f t , List.map (mapc f) c , List.map f fv )
  | TypeAssumption ( t , fv ) -> TypeAssumption ( f t , List.map f fv )

let mapdecl f { var_parameters ; binder_types } =
  { var_parameters = List.map f var_parameters ;
    binder_types =  List.map (mapdef f) binder_types }

module SMap = Map.Make(String)
module IntO = struct type t = int let compare = compare end
module IMap = Map.Make(IntO)
module ISet = Set.Make(IntO)

module type PrivS = sig
  type base
  type t = private base
  val make : base -> t
end

module Priv : functor (X:sig type t end) -> PrivS with type base = X.t =
  functor (X:sig type t end) -> struct
    type base = X.t
    type t = base
    let make x = x
  end

module CName : PrivS with type base = int = Priv(IntO)
module TName : PrivS with type base = int = Priv(IntO)
module VName : PrivS with type base = int = Priv(IntO)

module TO = struct type t = TName.t let compare (t1:TName.t) (t2:TName.t) =
  compare (t1:>int) (t2:>int) end
module CO = struct type t = CName.t let compare (c1:CName.t) (c2:CName.t) =
  compare (c1:>int) (c2:>int) end

module TMap = Map.Make(TO)
module TSet = Set.Make(TO)
module CSet = Set.Make(CO)

(* change names from string to faster integers. *)

let translate_names decls =
  let name_gen = ref 0 in
  let translate = ref SMap.empty in
  let rename s =
    try SMap.find s !translate
    with Not_found -> let u = !name_gen in
      name_gen := u + 1 ; translate := SMap.add s u !translate ;
      u in
  let u = mapdecl rename decls in
  let trback = SMap.fold ( fun s i acc ->
    IMap.add i s acc ) !translate IMap.empty in
  u , trback

type internal_types =
  | ITVar of VName.t
  | ITDecl of TName.t

type constructors = {
  var_present : bool ;
  cons_list : ( CName.t * ( TName.t * internal_types option) list * internal_types list ) list
}

type internal_typedef =
  | ITypeDef of constructors * TName.t list
  | ITypeAssumption of TName.t list

(* second integer : rank of apparition in file. Used for
   determining ordering : for example, the binder type variables
   should be ordered by rank of apparition in input file *)

type internal_decl =
  { var_params : VName.t list ;
    type_decls : (internal_typedef * int ) TMap.t ;
    names : string IMap.t }

let make_itype t = match t with
  | TypeVar v -> ITVar (VName.make v)
  | DeclaredType t -> ITDecl ( TName.make t)

let make_cons_list cons_set cl =
  let cs,cm = List.fold_left ( fun (cs,cm) -> function
    | BCons ( c , b , e ) -> let c' = CName.make c in
      if CSet.mem c' cs
      then assert false (* TODO->send error "duplicate constructor". *)
      else let b' = List.map ( fun ( x , t ) -> match t with
        | None -> TName.make x , None
        | Some t -> TName.make x , Some ( make_itype t ) ) b in
        let e' = List.map make_itype e in
        CSet.add c' cs, { cm with cons_list = (c',b',e')::cm.cons_list }
    | Var -> ( if cm.var_present
      then assert false (* TODO : decide if I send error here (* "duplicate var" *) *) ) ;
      cs,{cm with var_present = true } )
  (cons_set,{var_present = false ; cons_list = []}) cl in
  cs,{cm with cons_list = List.rev cm.cons_list}

let make_decl_map d =
  let _ , dmap , _ = List.fold_left ( fun (cs,dm,rank) -> function
    | TypeDefinition (tn,cstr,fv) -> let tn = TName.make tn in
      if TMap.mem tn dm
      then assert false (* TODO : error (duplicate type name) *)
      else let cs,csl = make_cons_list cs cstr in
        cs,TMap.add tn (ITypeDef (csl,List.map TName.make fv),rank) dm,rank + 1
    | TypeAssumption (tn,fv) -> let tn = TName.make tn in
      if TMap.mem tn dm
      then assert false (* TODO : error (duplicate type name) *)
      else cs,TMap.add tn (ITypeAssumption (List.map TName.make fv),rank) dm,rank + 1)
    (CSet.empty,TMap.empty,0) d in
  dmap

let convert_decl d0 =
  let { var_parameters ; binder_types } , names = translate_names d0 in
  { names ;
    var_params = List.map VName.make var_parameters ;
    type_decls = make_decl_map binder_types }

let type_def tn { type_decls ; _ } =
  let td , _ = TMap.find tn type_decls in td

(* TODO : various "unbound ident" check. *)

(* TODO : constructor "Var_" forbidden check. *)

(* edges of the dependency graph. *)
let dependents_fold f def acc = match def with
  | ITypeDef ( c , _ ) -> let fold_cons acc c =
      let _ , l1 , l2 = c in
      let acc = List.fold_left ( fun acc ( _ , t ) ->
          match t with
            | None -> acc
            | Some t -> match t with
              | ITVar _ -> acc
              | ITDecl u -> f u acc
        ) acc l1
      in
      List.fold_left ( fun acc -> function
        | ITVar _ -> acc
        | ITDecl u -> f u acc
        ) acc l2
    in
    List.fold_left fold_cons acc c.cons_list
  | ITypeAssumption _ -> acc

(* scc computation of the dependency graph
   return 1) the scc index of each type,
     2) the vertices in each scc. *)

let make_scc dm =
  let table = ref TMap.empty in
  let sccg = ref IMap.empty in
  let s = ref [] in
  let p = ref [] in
  let c = ref 1 in
  let scc = ref 0 in
  let rec pop_until num p = match p with
    | [] -> assert false
    | x :: q-> if TMap.find x !table >= num
      then p
      else pop_until num q in
  let rec process tn =
    let _ = table := TMap.add tn (- !c) !table in
    let _ = c := !c + 1 in
    let _ = s := tn :: !s in
    let _ = p := tn :: !p in
    let smake s _ =
      (* "let try" idiom would be better if available. *)
      match try Some (TMap.find s !table)
        with Not_found -> None with
        | None -> process s
        | Some x -> if x < 0
          then p := pop_until x !p
          else () in
    let td = type_def tn dm in
    let _ = dependents_fold smake td () in
    let rec pop_until sccn tn s acc = match s with
      | [] -> assert false
      | x :: q -> let acc = x :: acc in
        table := TMap.add x sccn !table ;
        if x = tn
        then q , acc
        else pop_until sccn tn q acc in
    match !p with
      | x :: q when x = tn -> p := q ;
        let sccn = !scc in
        let _ = scc := sccn + 1 in
        let ns , cpt = pop_until sccn tn !s [] in
        sccg := IMap.add sccn cpt !sccg ;
        s := ns
      | _ -> () in
  TMap.iter ( fun tn _ ->
    if not(TMap.mem tn !table)
    then process tn ) dm.type_decls ;
  !table,!sccg

(* compute set of potential binding variables occuring in each type,
   e.g fixpoint of propagation starting from given binding list + current type if it
   contains variable constructor. Straightforward from scc.
   After this, the list of binding vars associated to each type is exact. *)

let compute_binding_vars dm =
  let get_scc , get_types = make_scc dm in
  let tb = ref IMap.empty in
  let rec get_binding_vars sccn =
    try IMap.find sccn !tb
    with Not_found -> let all = IMap.find sccn get_types in
      (* dependents in scc quotiented graph + base set from current component. *)
      let dep,base = List.fold_left (fun (dep,base) tn ->
        let td = type_def tn dm in
        let dep = dependents_fold (fun tnd dep ->
          let sccnd = TMap.find tnd get_scc in
          if sccnd = sccn
          then dep
          else ISet.add sccnd dep ) td dep in
        let v,base = match td with
          | ITypeDef (c,v) ->
            v , if c.var_present then TSet.add tn base else base
          | ITypeAssumption v -> v , base in
        let base = List.fold_left (fun acc v -> TSet.add v acc ) base v in
        (dep,base) ) (ISet.empty,TSet.empty) all in
      let res = ISet.fold (fun sccnd acc ->
        TSet.union acc (get_binding_vars sccnd)) dep base in
      tb := IMap.add sccn res !tb ; res in
  let reorder bv =
    let compare t1 t2 =
      let _ , r1 = TMap.find t1 dm.type_decls in
      let _ , r2 = TMap.find t2 dm.type_decls in
      compare r1 r2 in
    List.sort compare bv in
  { names = dm.names ;
    var_params = dm.var_params ;
    type_decls = TMap.mapi (fun tn (td,rank) -> match td with
    | ITypeAssumption v -> ITypeAssumption (reorder v) , rank
    | ITypeDef ( c , _ ) -> let sccn = TMap.find tn get_scc in
      let bv = get_binding_vars sccn in
      ITypeDef ( c , reorder ( TSet.elements bv ) ) , rank ) dm.type_decls }

let type_name (tn:TName.t) dm = IMap.find (tn:>int) dm.names

let cons_name (cn:CName.t) dm = IMap.find (cn:>int) dm.names

let var_name (vn:VName.t) dm = IMap.find (vn:>int) dm.names

open Format

let print_params dm fmt =
  List.iter (fun v -> fprintf fmt " 'a%s" (var_name v dm)) dm.var_params

let level tn blv = try TMap.find tn blv with Not_found -> 0

let inc_level tn blv = TMap.add tn (level tn blv + 1) blv

let bvar_list = function ITypeAssumption v | ITypeDef (_,v) -> v

let print_tindex fmt (tn:TName.t) =
  fprintf fmt "%d" (tn:>int)

let print_binding_param dm prefix blevels fmt tn =
  let bl = level tn blevels in
  let rec print_p fmt = function
    | 0 -> fprintf fmt "'%s%a" prefix print_tindex tn
    | n -> fprintf fmt "(option@ %a)" print_p (n-1) in
  fprintf fmt "@[<hov 2>%a@]" print_p bl

let print_type_app dm ?(blevels=TMap.empty) prefix fmt tn =
  let tname = type_name tn dm in
  let td = type_def tn dm in
  fprintf fmt "%s%t" tname (print_params dm) ;
  let v = bvar_list td in
  List.iter (fun vn ->
    fprintf fmt "@ %a" (print_binding_param dm prefix blevels) vn) v

let print_type dm ?(blevels=TMap.empty) prefix fmt = function
  | ITVar x -> fprintf fmt "'a%s" (var_name x dm)
  | ITDecl tn -> print_type_app dm ~blevels prefix fmt tn

let make_first_case_printer p1 p2 =
  let first = ref true in
  fun fmt -> if !first
    then begin first := false ; fprintf fmt "%t" p1 end
    else fprintf fmt "%t" p2

let make_first_case_sprinter s1 s2 =
  let make s fmt = fprintf fmt "%s" s in
  make_first_case_printer (make s1) (make s2)

let print_type_defs fmt dm =
  let reorder tp =
    let compare ( _ , ( _ , r1 ) ) ( _ , ( _ , r2 ) ) = compare r1 r2 in
    List.sort compare tp in
  let tlist = TMap.bindings dm.type_decls in
  let tlist = reorder tlist in
  let print_decl = make_first_case_sprinter "type" "with" in
  List.iter (fun ( tn , ( td , _ ) ) ->
    match td with ITypeAssumption _ -> ()
      | ITypeDef ( c , v ) -> 
        let tname = type_name tn dm in
        fprintf fmt "@[<hov 2>%t @[<hov 2>%a@] =@ " print_decl (print_type_app dm "b") tn ;
        begin if c.var_present
          then fprintf fmt "| Var_%s 'b%a@\n" tname print_tindex tn end ;
        List.iter (fun ( cn , bl , tl ) ->
          let cname = cons_name cn dm in
          fprintf fmt "| %s@[<hov 2>" cname ;
          let rec print_parameters blevels bl = match bl with
            | [] -> blevels
            | ( vn , t ) :: q -> let nblevels =
                let u = try 1 + TMap.find vn blevels with Not_found -> 1 in
                TMap.add vn u blevels in
              match t with
                | None -> print_parameters nblevels q
                | Some t -> fprintf fmt "@ (%a)" (print_type dm ~blevels "b") t ;
                  print_parameters nblevels q
          in
          let blevels = print_parameters TMap.empty bl in
          List.iter (fprintf fmt "@ (%a)" (print_type dm ~blevels "b")) tl ;
          fprintf fmt "@]@\n"
        ) c.cons_list ;
      fprintf fmt "@]@\n"
  ) tlist

(* print a case in a pattern-matching and return the list of variables. *)

let print_cons_case ?(vbase="v") dm fmt ( cn , bl , tl ) =
  let cname = cons_name cn dm in
  fprintf fmt "| %s@[<hov 2>" cname ;
  let vars , blevels , cnt = List.fold_left (
    fun ( vars , blevels , cnt ) ( bound_one , associated_binding ) ->
        let nblevels = inc_level bound_one blevels in
        match associated_binding with
          | None -> ( vars , nblevels , cnt )
          | Some tp -> let vname = vbase ^ (string_of_int cnt) in
            fprintf fmt "@ %s" vname ;
            ( ( vname , blevels , tp ) :: vars , nblevels , cnt + 1 )
      ) ( [] , TMap.empty , 0 ) bl in
  let vars , _ = List.fold_left (
    fun ( vars , cnt ) cons_type ->
      let vname = vbase ^ (string_of_int cnt) in
      fprintf fmt "@ %s" vname ;
      ( ( vname , blevels , cons_type ) :: vars , cnt + 1 ) ) ( vars , cnt ) tl in
  fprintf fmt "@] ->@ " ; List.rev vars

(* print full pattern-matching. *)

let print_pattern_match ?(vbase="v") dm tn c var_case cons_case fmt vname =
  fprintf fmt "match %s with@\n" vname ;
  let tname = type_name tn dm in
  begin if c.var_present
    then begin
    let vname = vbase ^ "0" in
    fprintf fmt "  @[<hov 2>| Var_%s %s ->@ %a@]@\n" tname vname var_case vname
  end end ;
  List.iter (fun x ->
    fprintf fmt "  @[<hov 2>" ;
    let vars = print_cons_case ~vbase dm fmt x in
    fprintf fmt "%a@]@\n" (cons_case x) vars) c.cons_list ;
  fprintf fmt "end"

let make_for_defs dm f =
  TMap.iter (fun tn (td,_) -> match td with
    | ITypeAssumption _ -> ()
    | ITypeDef (c,v) ->
      f tn c v) dm.type_decls

let make_for_bdefs dm f =
  make_for_defs dm (fun tn c -> function
    | [] -> ()
    | v -> f tn c v)

let make_for_vdefs dm f =
  make_for_defs dm (fun tn c v ->
    if c.var_present
    then f tn c v
    else ())

let lemma_cons_case f (cn,_,_) fmt v =
  fprintf fmt "@[<hov 2>" ;
  List.iter (fun (vname,blv,ct) ->
    match ct with
      | ITVar _ -> ()
      | ITDecl tn -> fprintf fmt "%a ;@ " (f blv tn) vname
  ) v ;
  fprintf fmt "()@]"

let blemma_cons_case dm f (cn,_,_) fmt v =
  fprintf fmt "@[<hov 2>" ;
  List.iter (fun (vname,blv,ct) ->
    match ct with
      | ITVar _ -> ()
      | ITDecl tn when bvar_list (type_def tn dm) = [] -> ()
      | ITDecl tn -> fprintf fmt "%a ;@ " (f blv tn) vname
  ) v ;
  fprintf fmt "()@]"

let reconstruct_cons_case dm f (cn,_,_) fmt v =
  let cname = cons_name cn dm in
  fprintf fmt "%s@[<hov 2> " cname;
  List.iter (fun (vname,blv,ct) ->
    match ct with
      | ITVar _ -> fprintf fmt "%s@ " vname
      | ITDecl tn when bvar_list (type_def tn dm) = [] -> fprintf fmt "%s@ " vname
      | ITDecl tn -> fprintf fmt "(%a)@ " (f blv tn) vname
  ) v ;
  fprintf fmt "@]"

let print_size_defs fmt dm =
  let print_kw = make_first_case_sprinter "function" "with" in
  let print_decl tn c v is_nat =
    let prefix = if is_nat then "nat_" else "" in
    let tp = if is_nat then "nat" else "int" in
    let one = if is_nat then "one_nat" else "1" in
    let add = if is_nat then fun fmt p -> fprintf fmt "add_nat s (%t)" p
      else fun fmt p -> fprintf fmt "s + %t" p in
    let var_case fmt vname = fprintf fmt "%s" one in
    let cons_case _ fmt v =
      fprintf fmt "let s = %s in@\n" one ;
      List.iter (fun (vname,_,ct) -> match ct with
        | ITVar _ -> ()
        | ITDecl tn -> let tname = type_name tn dm in
          let rec_call fmt = fprintf fmt "%ssize_%s %s" prefix tname vname in
          fprintf fmt "let s = %a in@\n" add rec_call ) v ;
      fprintf fmt "s" in
    let tname = type_name tn dm in
    fprintf fmt "@[<hov 2>%t %ssize_%s (t:@[<hov 2>%a@]) : %s =@ %a@]@\n@\n"
      print_kw prefix tname (print_type_app dm "b") tn tp
      (print_pattern_match dm tn c var_case cons_case) "t" in
  make_for_defs dm (fun tn c v ->
    print_decl tn c v true ; print_decl tn c v false )

let print_size_lemmae fmt dm =
  let print_kw = make_first_case_sprinter "let rec" "with" in
  let print_decl tn c v =
    let tname = type_name tn dm in
    let var_case fmt _ = fprintf fmt "()" in
    let cons_case = lemma_cons_case (fun blv tn fmt vname ->
      let tname = type_name tn dm in
      fprintf fmt "size_%s_positive %s" tname vname ) in
    fprintf fmt "@[<hov 2>%t lemma size_%s_positive (t:@[<hov 2>%a@]) : unit@\n\
    ensures { size_%s t > 0 }@\n\
    variant { @[<hov 2>nat_to_int (nat_size_%s t)@] }@]@\n\
    @[<hov 2>=@ %a@]@\n@\n"
      print_kw tname (print_type_app dm "b") tn tname tname
      (print_pattern_match dm tn c var_case cons_case) "t" in
  make_for_defs dm print_decl

let print_lift sub dm prefix blv fmt tn =
  let tname = type_name tn dm in
  let lifting = if sub
    then (fun fmt -> fprintf fmt "olifts_%s" tname )
    else (fun fmt -> fprintf fmt "olift" ) in
  let rec aux fmt = function
    | 0 -> fprintf fmt "%t" prefix
    | n -> fprintf fmt "(%t@ %a)" lifting aux (n-1) in
  let aux fmt n = fprintf fmt "@[<hov 2>%a@]" aux n in
  let n0 = level tn blv in
  if sub
  then begin fprintf fmt "@[<hov 2>(rename_subst_%s@ %a" tname aux n0 ;
      let v = bvar_list (type_def tn dm) in
      let rec composed fmt = function
        | 0 -> fprintf fmt "identity"
        | n -> fprintf fmt "(compose some@ %a)" composed (n-1) in
      List.iter (fun tn' ->
        if tn = tn'
        then fprintf fmt "@ identity"
        else fprintf fmt "@ @[<hov 2>%a@]" composed (level tn' blv) ) v ;
      fprintf fmt ")@]"
    end
  else aux fmt n0

let print_subst_type sub dm p1 p2 fmt tn =
  if sub
  then fprintf fmt "func '%s%a @[<hov 2>(%a)@]"
    p1 print_tindex tn (print_type_app dm p2) tn
  else fprintf fmt "func '%s%a '%s%a" p1 print_tindex tn p2 print_tindex tn

let print_subst_def dm fmt sub =
  let print_kw = make_first_case_sprinter "function" "with" in
  let fprefix = if sub then "subst" else "rename" in
  let print_decl tn c v =
    let tname = type_name tn dm in
    let var_case = if sub
      then fun fmt vname ->
        fprintf fmt "s%a %s" print_tindex tn vname
      else fun fmt vname ->
        fprintf fmt "Var_%s (s%a %s)" tname print_tindex tn vname in
    let print_args blv fmt v =
      let prefix tn fmt = fprintf fmt "s%a" print_tindex tn in
      List.iter (fun tn ->
          fprintf fmt "@ %t" (fun fmt ->
            print_lift sub dm (prefix tn) blv fmt tn)) v in
    let cons_case = reconstruct_cons_case dm (fun blv tn fmt vname ->
      let tname = type_name tn dm in
      let v = bvar_list (type_def tn dm) in
      fprintf fmt "@[<hov 2>%s_%s@ %s%a@]" fprefix tname vname 
      (print_args blv) v) in
    fprintf fmt "@[<hov 2>%t %s_%s @[<hov 2>(t:@[<hov 2>%a@])" print_kw fprefix tname
    (print_type_app dm "b") tn ;
    List.iter (fun tn -> 
      fprintf fmt "@ (s%a : %a)"
      print_tindex tn (print_subst_type sub dm "b" "c") tn) v ;
    fprintf fmt "@] : %a =@ %a@]@\n@\n" (print_type_app dm "c") tn
      (print_pattern_match dm tn c var_case cons_case) "t"
  in
  make_for_bdefs dm print_decl

let print_composition dm sub1 side1 sub2 side2 fmt tn =
  if sub1
  then begin let tname = type_name tn dm in
    let p = if sub2 then "subst_compose" else "rename_subst" in
    fprintf fmt "(@[<hov 2>%s_%s %t" p tname side1 ;
    let v = bvar_list (type_def tn dm) in
    List.iter (fun tn ->
      fprintf fmt "@ %a" side2 tn) v ;
    fprintf fmt "@])" end
  else fprintf fmt "(@[<hov 2>rcompose %t@ %a@])"
    side1 side2 tn

let print_composition_lemma dm fmt (sub1,sub2) =
  let print_kw = make_first_case_sprinter "let rec" "with" in
  let fp s = if s then "subst" else "rename" in
  let fp1 , fp2 , fpc = fp sub1 , fp sub2 , fp (sub1 || sub2) in
  let prefix id tn fmt = fprintf fmt "s%s%a" id print_tindex tn in
  let print_args blv fmt v =
      List.iter (fun tn ->
          fprintf fmt "@ %a@ %a"
          (print_lift sub1 dm (prefix "1" tn) blv) tn
          (print_lift sub2 dm (prefix "2" tn) blv) tn) v in
  let print_nargs id fmt v =
    List.iter (fun tn -> fprintf fmt "@ s%s%a" id print_tindex tn) v in
  let print_cargs fmt v =
    List.iter (fun tn ->
      let side1 fmt = fprintf fmt "s1%a" print_tindex tn in
      let side2 fmt tn = fprintf fmt "s2%a" print_tindex tn in
      fprintf fmt "@ %a" (print_composition dm sub1 side1 sub2 side2) tn) v in
  let print_decl tn c v =
    let tname = type_name tn dm in
    let var_case fmt _ = fprintf fmt "()" in
    let cons_case = blemma_cons_case dm (fun blv tn fmt vname ->
        let tname = type_name tn dm in
        let v = bvar_list (type_def tn dm) in
        fprintf fmt "@[<hov 2>composition_lemma_%s_%s_%s %s%a@]"
        fp1 fp2 tname vname (print_args blv) v ) in
    fprintf fmt "@[<hov 2>%t lemma composition_lemma_%s_%s_%s @[<hov 2>(t:@[<hov 2>%a@])"
    print_kw fp1 fp2 tname (print_type_app dm "b") tn ;
    List.iter (fun tn ->
      fprintf fmt "@ (s1%a : %a)@ (s2%a : %a)"
      print_tindex tn (print_subst_type sub1 dm "b" "c" ) tn
      print_tindex tn (print_subst_type sub2 dm "c" "d" ) tn) v ;
    fprintf fmt "@] : unit@\n\
      @[<hov 2>ensures { @[<hov 2>%s_%s (@[<hov 2>%s_%s t %a@])@ %a@] =@ \
        @[<hov 2>%s_%s t@ %a@] }@]@\n\
      variant { size_%s t }@]@\n@[<hov 2>=@ %a@]@\n"
      fp2 tname fp1 tname (print_nargs "1") v (print_nargs "2") v
      fpc tname print_cargs v
      tname (print_pattern_match dm tn c var_case cons_case) "t" in
  make_for_bdefs dm print_decl

let print_identity_lemma dm fmt sub =
  let print_kw = make_first_case_sprinter "let rec" "with" in
  let fp = if sub then "subst" else "rename" in
  let print_decl tn c v =
    let tname = type_name tn dm in
    let print_identities = if sub
      then fun fmt ->
        List.iter (fun tn -> let tname = type_name tn dm in
          fprintf fmt "@ subst_id_%s" tname) v
      else fun fmt ->
        List.iter (fun _ -> fprintf fmt "@ identity") v in
    let var_case fmt _ = fprintf fmt "()" in
    let cons_case = blemma_cons_case dm (fun blv tn fmt vname ->
      let tname = type_name tn dm in
      fprintf fmt "identity_lemma_%s_%s %s" fp tname vname) in
    fprintf fmt "@[<hov 2>%t lemma identity_lemma_%s_%s (t:@[<hov 2>%a@]) : unit@\n\
      ensures { @[<hov 2>%s_%s t%t@] = t }@\n\
      variant { size_%s t }@]@\n@[<hov 2>=@ %a@]@\n"
    print_kw fp tname (print_type_app dm "b") tn
    fp tname print_identities
    tname (print_pattern_match dm tn c var_case cons_case) "t" in
  make_for_bdefs dm print_decl

let print_associativity_lemma dm fmt (sub1,sub2,sub3) =
  let fp = function true -> "subst" | false -> "rename" in
  let fp1,fp2,fp3 = fp sub1,fp sub2,fp sub3 in
  let print_decl tn c v =
    let tname = type_name tn dm in
    fprintf fmt "@[<hov 2>let lemma@ associativity_lemma_%s_%s_%s_%s@ (s1:@[<hov 2>%a@])"
    fp1 fp2 fp3 tname (print_subst_type sub1 dm "b" "c" ) tn ;
    (if sub1
    then List.iter (fun tn ->
      fprintf fmt "@ (s2%a:@[<hov 2>%a@])@ (s3%a:@[<hov 2>%a@])"
      print_tindex tn (print_subst_type sub2 dm "c" "d" ) tn
      print_tindex tn (print_subst_type sub3 dm "d" "e" ) tn ) v
    else begin fprintf fmt "@ (s2%a:@[<hov 2>%a@])"
          print_tindex tn (print_subst_type sub2 dm "c" "d") tn ;
      if sub2
      then List.iter (fun tn ->
          fprintf fmt "@ (s3%a:@[<hov 2>%a@])"
          print_tindex tn (print_subst_type sub3 dm "d" "e") tn ) v
      else fprintf fmt "@ (s3%a:@[<hov 2>%a@])"
        print_tindex tn (print_subst_type sub2 dm "d" "e") tn
    end);
    let print_first fmt =
      let side1 fmt = fprintf fmt "s1" in
      let side2 fmt tn =
        let side1 fmt = fprintf fmt "s2%a" print_tindex tn in
        let side2 fmt tn = fprintf fmt "s3%a" print_tindex tn in
        print_composition dm sub2 side1 sub3 side2 fmt tn in
      print_composition dm sub1 side1 (sub2||sub3) side2 fmt tn in
    let print_second fmt =
      let side1 fmt =
        let side1 fmt = fprintf fmt "s1" in
        let side2 fmt tn = fprintf fmt "s2%a" print_tindex tn in
        print_composition dm sub1 side1 sub2 side2 fmt tn in
      let side2 fmt tn = fprintf fmt "s3%a" print_tindex tn in
      print_composition dm (sub1||sub2) side1 sub3 side2 fmt tn in
    fprintf fmt "@\nensures { %t =@ %t }@]@\n@[<hov 2>=@ \
      @[<hov 2>assert { extensionalEqual %t@ %t }@]@]@\n@\n"
      print_first print_second print_first print_second in
  make_for_vdefs dm print_decl

(* case with left side a renaming come directly from functions axiom,
   hence do not need to be generated. The same hold for right identity. *)
let print_left_identity_lemma dm fmt sub2 =
  let fp2 = if sub2 then "subst" else "rename" in
  let cop = if sub2 then "subst_compose" else "rename_subst" in
  let print_decl tn c v =
    let tname = type_name tn dm in
    fprintf fmt "@[<hov 2>let lemma identity_neutral_left_%s_%s"
      fp2 tname ;
    List.iter (fun tn ->
       fprintf fmt "@ (s%a:%a)" print_tindex tn
         (print_subst_type sub2 dm "b" "c") tn) v ;
    let print_first fmt =
      fprintf fmt "@[<hov 2>%s_%s (subst_id_%s:%a)"
        cop tname tname (print_subst_type true dm "b" "b") tn ;
      List.iter (fprintf fmt "@ s%a" print_tindex) v ;
      fprintf fmt "@]" in
    let print_second = if sub2
      then fun fmt -> fprintf fmt "s%a" print_tindex tn
      else fun fmt -> fprintf fmt "subst_of_rename_%s s%a" tname print_tindex tn in
    fprintf fmt " : unit@\n@[<hov 2>ensures { %t =@ %t }@]@]@\n@[<hov 2>=@ \
      @[<hov 2>assert { extensionalEqual (%t)@ (%t) }@]@]@\n@\n"
      print_first print_second print_first print_second in
  make_for_vdefs dm print_decl

let print_right_identity_lemma dm fmt sub2 =
  let fp2 = if sub2 then "subst" else "rename" in
  let cop = if sub2 then "subst_compose" else "rename_subst" in
  let prid = if sub2 then fun fmt tn ->
    fprintf fmt "subst_id_%s" (type_name tn dm) else fun fmt _ ->
      fprintf fmt "identity" in
  let print_decl tn c v =
    let tname = type_name tn dm in
    let print_first fmt =
      fprintf fmt "@[<hov 2>%s_%s s" cop tname ;
      List.iter (fprintf fmt "@ %a" prid) v ;
      fprintf fmt "@]" in
    let print_second fmt = fprintf fmt "s" in
    fprintf fmt "@[<hov 2>let lemma identity_neutral_right_%s_%s (s:%a) : unit@\n\
      @[<hov 2>ensures { %t =@ %t }@]@]@\n\
      @[<hov 2>=@ @[<hov 2>assert { extensionalEqual (%t)@ (%t) }@]@]@\n@\n"
      fp2 tname (print_subst_type true dm "b" "c") tn
      print_first print_second print_first print_second in
  make_for_vdefs dm print_decl

let print_substitution_composition_def dm fmt sub =
  let print_args fmt = List.iter (fprintf fmt "@ s1%a" print_tindex) in
  let print_args_typed fmt = List.iter (fun tn ->
    fprintf fmt "@ (s1%a:%a)"
      print_tindex tn (print_subst_type sub dm "c" "d") tn) in
  let print_args_typed2 fmt = List.iter (fun tn ->
    fprintf fmt ",@ s1%a:%a"
      print_tindex tn (print_subst_type sub dm "c" "d") tn) in
  let cop = if sub then "subst_compose" else "rename_subst" in
  let dop = if sub then "subst" else "rename" in
  let print_decl tn c v =
    let tname = type_name tn dm in
    let mytype fmt = print_subst_type true dm "b" "c" fmt tn in
    let print_def fmt = fprintf fmt "@[<hov 2>%s_%s (s0 x)%a@]" dop tname print_args v in
    let print_left_fun fmt =
      fprintf fmt "function %s_%s (s0:%t)%a :@ %a"
        cop tname mytype print_args_typed v (print_subst_type true dm "b" "d") tn in
    fprintf fmt "(* @[<hov 2>Abstraction definition axiom :@ \
      @[<hov 2>%t =@ (\\ x: 'b%a. %t)@]@ *)@]@\n\
      @[<hov 2>%t@]@\n\
      @[<hov 2>axiom %s_%s_definition :@ forall s0:%t%a,@ x:'b%a.@ \
      @[<hov 2>@[<hov 2>%s_%s s0%a@ x@] =@ %t@]@]@\n@\n"
      print_left_fun print_tindex tn print_def
      print_left_fun
      cop tname mytype print_args_typed2 v print_tindex tn
      cop tname print_args v print_def in
  make_for_vdefs dm print_decl

let print_lifting_composition_lemma dm fmt (sub1,sub2) =
  let fp s = if s then "subst" else "rename" in
  let li s = if s then (fun fmt tname -> fprintf fmt "olifts_%s" tname)
    else (fun fmt _ -> fprintf fmt "olift") in
  let fp1,fp2 = fp sub1 , fp sub2 in
  let li1,li2,lic = li sub1,li sub2,li (sub1||sub2) in
  let print_decl tn c v =
    let tname = type_name tn dm in
    fprintf fmt "@[<hov 2>let lemma olift_composition_%s_%s_%s (s0:%a)"
      fp1 fp2 tname (print_subst_type sub1 dm "b" "c") tn ;
    let print_targ tn = fprintf fmt "@ (s1%a:%a)"
      print_tindex tn (print_subst_type sub2 dm "c" "d") tn in
    (if sub1 then List.iter print_targ v else print_targ tn);
    let print_first fmt =
      let side1 fmt = fprintf fmt "s0" in
      let side2 fmt tn = fprintf fmt "s1%a" print_tindex tn in
      fprintf fmt "%a (%a)" lic tname
        (print_composition dm sub1 side1 sub2 side2) tn in
    let blv = TMap.singleton tn 1 in
    let print_second fmt =
      let side1 fmt = fprintf fmt "(%a s0)" li1 tname in
      let side2 fmt tn' = if tn = tn'
        then fprintf fmt "(%a s1%a)" li2 tname print_tindex tn
        else print_lift sub2 dm (fun fmt ->
          fprintf fmt "s1%a" print_tindex tn') blv fmt tn' in
      print_composition dm sub1 side1 sub2 side2 fmt tn in
    fprintf fmt " : unit@\n\
      @[<hov 2>ensures { %t =@ %t }@]@]@\n@[<hov 2>=@ \
      @[<hov 2>assert { forall x:'b%a. eval (%t) (Some x) =@ eval (%t) (Some x) };@]@\n
      @[<hov 2>assert { eval (%t) None =@ eval (%t) None };@]@\n
      @[<hov 2>assert { extensionalEqual (%t)@ (%t) }@]@]@\n@\n"
      print_first print_second print_tindex tn print_first print_second
      print_first print_second print_first print_second
  in
  make_for_vdefs dm print_decl

let print_subst_lifting fmt dm =
  let print_decl tn c v =
    let tname = type_name tn dm in
    let blevels = TMap.singleton tn 1 in
    let print_args fmt =
      List.iter (fun tn' -> if tn = tn'
        then fprintf fmt "@ some"
        else fprintf fmt "@ identity") v in
    let print_lhs1 fmt =
      fprintf fmt "@[<hov 2>rename_%s (s x)%t@]" tname print_args in
    let print_lhs2 fmt =
      fprintf fmt "@[<hov 2>rename_subst_%s s%t@]" tname print_args in
    let mytype = print_subst_type true dm "b" "c" in
    fprintf fmt "@[<hov 2>function osubst_%s (s:%a)@ (x:option 'b%a) :@ @[<hov 2>%a@] =@\n\
      @[<hov 2>match x with@\n| None -> Var_%s None@ | Some x -> %t@]@\nend@]@\n@\n"
      tname mytype tn print_tindex tn (print_type_app dm ~blevels "c") tn
      tname print_lhs1 ;
    fprintf fmt "@[<hov 2>function olifts_%s (s:%a) :@ func (option 'b%a) (%a) =@ \
      ocase (%t) (Var_%s None)@]@\n@\n"
      tname mytype tn
      print_tindex tn (print_type_app dm ~blevels "c") tn
      print_lhs2 tname ;
    fprintf fmt "@[<hov 2>lemma olifts_%s_some_value :@ \
      @[<hov 2>forall s:%a,@ x:'b%a.@ \
      olifts_%s s (Some x) =@ %t@]@]@\n@\n"
      tname mytype tn print_tindex tn tname print_lhs1 ;
    fprintf fmt "@[<hov 2>lemma olifts_%s_none :@ \
      @[<hov 2>forall s:%a.@ \
      olifts_%s s None =@ Var_%s None@]@]@\n@\n"
      tname mytype tn tname tname ;
    (* most provers needs us to write the disjunction ourselves... *)
    fprintf fmt "@[<hov 2>let lemma olifts_%s_other_def@ (s:%a)@ (x:option 'b%a) : unit@\n\
      @[<hov 2>ensures { olifts_%s s x =@ osubst_%s s x }@]@]@\n\
      @[<hov 2>=@ \
      @[<hov 2>match x with@\n| None -> ()@\n| Some _ -> ()@]@\nend@]@\n@\n"
      tname mytype tn print_tindex tn tname tname
  in
  make_for_vdefs dm print_decl

let print_subst_ids fmt dm =
  let print_decl tn c v =
    let tname = type_name tn dm in
    fprintf fmt "(*@[<hov 2> Abstraction-definition axiom :@ \
      @[<hov 2>constant subst_id_%s : %a =@ (\\ x:'b%a. Var_%s x)@]@ *)@]@\n\
      constant subst_id_%s : %a@\n\
      @[<hov 2>axiom subst_id_%s_def :@ forall x:'b%a.@ \
      eval (subst_id_%s : %a) x = Var_%s x@]@\n@\n\
      @[<hov 2>function subst_of_rename_%s (r:%a) : %a =@ \
      rcompose r subst_id_%s@]@\n@\n"
      tname (print_subst_type true dm "b" "b") tn print_tindex tn tname
      tname (print_subst_type true dm "b" "b") tn
      tname print_tindex tn tname (print_subst_type true dm "b" "b") tn tname
      tname (print_subst_type false dm "b" "c") tn
      (print_subst_type true dm "b" "c") tn tname ;
    let print_first fmt =
      fprintf fmt "olifts_%s (subst_id_%s : %a)"
        tname tname (print_subst_type true dm "b" "b") tn in
    let print_second fmt =
      fprintf fmt "subst_id_%s" tname in
    fprintf fmt "@[<hov 2>let lemma olifts_identity_%s (u:unit) : unit@ \
      @[<hov 2>ensures { %t =@ %t }@]@]@\n
      @[<hov 2>=@ \
      @[<hov 2>assert { forall x:'b%a. eval (%t) (Some x) =@ eval (%t) (Some x) };@]@\n\
      @[<hov 2>assert { eval (%t) None =@ eval (%t) None };@]@\n\
      @[<hov 2>assert { extensionalEqual (%t)@ (%t) }@]@]@\n@\n"
      tname print_first print_second print_tindex tn
      print_first print_second print_first print_second print_first print_second in
  make_for_vdefs dm print_decl

let print_renaming_as_subst_lemmae fmt dm =
  let print_decl tn c v =
    let tname = type_name tn dm in
    let print_targs fmt = List.iter (fun tn ->
      fprintf fmt ",@ r%a:%a" print_tindex tn
      (print_subst_type false dm "b" "c") tn) v in
    let print_args1 fmt = List.iter (fun tn ->
      fprintf fmt "@ r%a" print_tindex tn) v in
    let print_args2 fmt = List.iter (fun tn ->
      let tname = type_name tn dm in
      fprintf fmt "@ (subst_of_rename_%s r%a)" tname print_tindex tn) v in
    fprintf fmt "@[<hov 2>lemma renaming_as_subst_%s :@ \
      forall t:%a%t.@ @[<hov 2> @[<hov 2>rename_%s t%t@] =@ \
      @[<hov 2>subst_%s t%t@]@]@]@\n@\n"
      tname (print_type_app dm "b") tn print_targs tname
      print_args1 tname print_args2 ;
    fprintf fmt "@[<hov 2>lemma subst_of_rename_preserve_identity_%s :@ \
      @[<hov 2>(subst_id_%s : %a) =@ \
      subst_of_rename_%s identity@]@]@\n@\n"
      tname tname (print_subst_type true dm "b" "b") tn tname in
  make_for_vdefs dm print_decl

let print_left_compose_renaming_as_subst_lemma dm fmt sub =
  let fp = if sub then "subst" else "rename" in
  let cast = if sub then fun _ _ -> () else fun fmt tname ->
    fprintf fmt "subst_of_rename_%s" tname in
  let print_decl tn c v =
    let tname = type_name tn dm in
    fprintf fmt "@[<hov 2>lemma left_compose_subst_of_rename_%s_%s :@ \
      forall r:%a"
      fp tname (print_subst_type false dm "b" "c") tn ;
    List.iter (fun tn ->
      fprintf fmt ",@ s%a:%a" print_tindex tn
        (print_subst_type sub dm "c" "d") tn) v ;
    let side1_1 fmt = fprintf fmt "r" in
    let side1_2 fmt = fprintf fmt "(subst_of_rename_%s r)" tname in
    let side2 fmt tn = fprintf fmt "s%a" print_tindex tn in
    fprintf fmt ".@ @[<hov 2>%a(%a) =@ %a@]@]@\n@\n" cast tname
      (print_composition dm false side1_1 sub side2) tn
      (print_composition dm true side1_2 sub side2) tn in
  make_for_vdefs dm print_decl

let print_right_compose_renaming_as_subst_lemma dm fmt sub =
  let fp = if sub then "subst" else "rename" in
  let cast = if sub then fun _ _ -> () else fun fmt tname ->
    fprintf fmt "subst_of_rename_%s" tname in
  let print_decl tn c v =
    let tname = type_name tn dm in
    fprintf fmt "@[<hov 2>lemma right_compose_subst_of_rename_%s_%s :@ \
      forall s:%a" fp tname (print_subst_type sub dm "b" "c") tn ;
    let print_targ tn =
      fprintf fmt ",@ r%a:%a" print_tindex tn
        (print_subst_type false dm "c" "d") tn in
    (if sub
     then List.iter print_targ v
     else print_targ tn);
    let side1 fmt = fprintf fmt "s" in
    let side2_1 fmt tn = fprintf fmt "r%a" print_tindex tn in
    let side2_2 fmt tn =
      fprintf fmt "(subst_of_rename_%s r%a : %a)"
      (type_name tn dm) print_tindex tn
      (print_subst_type true dm "c" "d") tn in
    fprintf fmt ".@ @[<hov 2>%a(%a) =@ %a@]@]@\n@\n" cast tname
      (print_composition dm sub side1 false side2_1) tn
      (print_composition dm sub side1 true side2_2) tn in
  make_for_vdefs dm print_decl

let print_free_var_def fmt dm =
  let print_kw = make_first_case_sprinter "predicate" "with" in
  let rec print_in_somes fmt = function
    | 0 -> fprintf fmt "x"
    | n -> fprintf fmt "(Some %a)" print_in_somes (n-1) in
  let print_decl tnv tn c v =
    let tname = type_name tn dm in
    let tnamev = type_name tnv dm in
    let var_case fmt vname = if tn = tnv
      then fprintf fmt "%s = x" vname
      else fprintf fmt "false" in
    let cons_case _ fmt vlist =
      let printed = ref false in
      List.iter (fun (vname,blv,ct) -> match ct with
        | ITVar _ -> ()
        | ITDecl tn -> if List.mem tnv (bvar_list (type_def tn dm))
          then begin
              (if !printed then fprintf fmt "@ \\/@ " else printed := true);
              fprintf fmt "is_%s_free_var_in_%s %a %s"
                tnamev (type_name tn dm) print_in_somes (level tnv blv) vname
            end ) vlist ;
      if not(!printed)
      then fprintf fmt "false" in
    fprintf fmt "@[<hov 2>%t is_%s_free_var_in_%s (x:'b%a) (t:%a) =@\n\
      @[<hov 2>%a@]@]@\n@\n"
      print_kw tnamev tname print_tindex tnv
      (print_type_app dm "b") tn
      (print_pattern_match dm tn c var_case cons_case) "t" in
  make_for_bdefs dm (fun tn c v ->
    List.iter (fun tnv ->
      print_decl tnv tn c v ) v)

let print_free_var_equivalence_def fmt dm =
  let print_decl tnv tn c v =
    let tname = type_name tn dm in
    let tnamev = type_name tnv dm in
    fprintf fmt "@[<hov 2>predicate %s_free_var_%s_equivalence (t:%a) (f g:func 'b%a 'c) =@\n\
      @[<hov 2>forall x:'b%a. is_%s_free_var_in_%s x t ->@ f x = g x@]@]@\n@\n"
      tnamev tname (print_type_app dm "b") tn
      print_tindex tnv print_tindex tnv tnamev tname (*;
    fprintf fmt "@[<hov 2>lemma %s_free_var_%s_equivalence_reflexive :@\n\
      @[<hov 2>forall t:%a,f:func 'b%a 'c. %s_free_var_%s_equivalence t f f@]@]@\n@\n"
      tnamev tname (print_type_app dm "b") tn
      print_tindex tnv tnamev tname*)
  in
  make_for_bdefs dm (fun tn c v ->
    List.iter (fun tnv ->
      print_decl tnv tn c v) v)

let print_free_var_equivalence_lemma dm fmt sub =
  let fp = if sub then "subst" else "rename" in
  let print_kw = make_first_case_sprinter "let rec" "with" in
  let rec print_in_options p fmt = function
    | 0 -> p fmt
    | n -> fprintf fmt "(option %a)" (print_in_options p) (n-1) in
  let print_decl tnv tn c v =
    let tname = type_name tn dm in
    let tnamev = type_name tnv dm in
    let var_case fmt _ = fprintf fmt "()" in
    let prefix id tn fmt = fprintf fmt "s%s%a" id print_tindex tn in
    let cons_case = blemma_cons_case dm (fun blv tn fmt vname ->
      let tname2 = type_name tn dm in
      let v = bvar_list (type_def tn dm) in
      if List.mem tnv v
      then begin
        let p0 = print_in_options (fun fmt -> fprintf fmt "'b%a" print_tindex tnv) in
        let nv0 = level tnv blv in
        let rec print_disjunction somep fmt = function
          | 0 -> fprintf fmt "@[<hov 2>| %a ->@ is_%s_free_var_in_%s y t@]@ "
            somep "y" tnamev tname
          | n -> let somep' fmt a = fprintf fmt "(Some %a)" somep a in
            fprintf fmt "@[<hov 2>| %a ->@ true@]@ %a"
              somep "None" (print_disjunction somep') (n-1) in
        let print_disj fmt =
          print_disjunction (fun fmt -> fprintf fmt "%s") fmt nv0 in
        fprintf fmt "@[<hov 2>assert { forall x:%a. is_%s_free_var_in_%s x %s ->@ \
            @[<hov 2>match x with %t end@] };@]@,"
          p0 nv0 tnamev tname2 vname print_disj ;
        fprintf fmt "%s_%s_free_var_equivalence_lemma_%s %s"
          fp tnamev tname2 vname ;
        let pl id tn fmt = print_lift sub dm (prefix id tn) blv fmt tn in
        List.iter (fun tn ->
          if tn = tnv
          then fprintf fmt "@ %t@ %t" (pl "1" tn) (pl "2" tn)
          else fprintf fmt "@ %t" (pl "0" tn)) v
      end else fprintf fmt "()" ) in
    fprintf fmt "@[<hov 2>%t lemma %s_%s_free_var_equivalence_lemma_%s (t:%a)"
      print_kw fp tnamev tname (print_type_app dm "b") tn ;
    List.iter (fun tn ->
      if tn = tnv
      then fprintf fmt "@ (s1%a:%a)@ (s2%a:%a)" print_tindex tn
          (print_subst_type sub dm "b" "c") tn print_tindex tn
          (print_subst_type sub dm "b" "c") tn
      else fprintf fmt "@ (s0%a:%a)" print_tindex tn
          (print_subst_type sub dm "b" "c") tn
      ) v ;
    let print_call fmt id =
      fprintf fmt "%s_%s t" fp tname ;
      List.iter (fun tn -> if tn = tnv
        then fprintf fmt " s%s%a" id print_tindex tn
        else fprintf fmt " s0%a" print_tindex tn) v in
    fprintf fmt " : unit@\n" ;
    fprintf fmt "@[<hov 2>requires { %s_free_var_%s_equivalence t s1%a s2%a }@]@\n"
      tnamev tname print_tindex tnv print_tindex tnv ;
    fprintf fmt "@[<hov 2>ensures { %a =@ %a }@]@\n\
      @[<hov 2>variant { size_%s t }@]@]@\n\
      @[<hov 2>=@\n@[<hov 2>%a@]@]@\n@\n"
      print_call "1" print_call "2" tname
      (print_pattern_match dm tn c var_case cons_case) "t" in
  make_for_bdefs dm (fun tn c v ->
    List.iter (fun tnv -> print_decl tnv tn c v) v)

(* Awful. *)

let print_free_var_substitution_lemma dm fmt sub =
  let fp = if sub then "subst" else "rename" in
  let print_kw = make_first_case_sprinter "let rec" "with" in
  let rec print_in_somes s fmt = function
    | 0 -> fprintf fmt "%s" s
    | n -> fprintf fmt "(Some %a)" (print_in_somes s) (n-1) in
  let rec print_in_options p fmt = function
    | 0 -> p fmt
    | n -> fprintf fmt "(option %a)" (print_in_options p) (n-1) in
  let print_decl tnv tn c v =
    let tname = type_name tn dm in
    let tnamev = type_name tnv dm in
    let var_case fmt _ = fprintf fmt "()" in
    let tname0 = tname in
    let cons_case = lemma_cons_case (fun blv tn fmt vname ->
        let v2 = bvar_list (type_def tn dm) in
        if List.mem tnv v2
        then begin
          let print_right fmt ty =
            let ynamev = type_name ty dm in
            fprintf fmt"is_%s_free_var_in_%s y t@ /\\@ "
              ynamev tname ;
            if sub
            then fprintf fmt "is_%s_free_var_in_%s x (s%a y)"
                  tnamev ynamev print_tindex ty
            else fprintf fmt "s%a y = x" print_tindex tnv in
          let rec print_disj ty ynamev somep fmt = function
            | 0 -> fprintf fmt "@[<hov 2>| %a ->@ %a@ &&@ exists y:'b%a.%a@]" somep "y"
              print_right ty print_tindex ty print_right ty
            | n -> let somep' fmt s = fprintf fmt "(Some %a)" somep s in
              fprintf fmt "@[<hov 2>| %a ->@ false@]@ %a" somep "None"
                (print_disj ty ynamev somep') (n-1) in
          let print_disj ty ynamev fmt lv =
            fprintf fmt "@[<hov 2>match y with %a@ end@]"
              (print_disj ty ynamev (fun fmt -> fprintf fmt "%s")) lv in
          let lv = level tnv blv in
          let tname = type_name tn dm in
          fprintf fmt "@[<hov 2>%s_%s_free_var_in_%s %a %s"
            fp tnamev tname (print_in_somes "x") lv vname ;
          List.iter (fun tn -> fprintf fmt "@ %a"
            (print_lift sub dm (fun fmt ->
              fprintf fmt "s%a" print_tindex tn ) blv ) tn ) v2 ;
          fprintf fmt ";@]@," ;
          begin if sub
            then List.iter (fun tny ->
              if List.mem tnv (bvar_list (type_def tny dm))
              then begin
                let ynamev = type_name tny dm in
                let lvy = level tny blv in
                let ps fmt tn = print_lift sub dm (fun fmt ->
                      fprintf fmt "s%a" print_tindex tn) blv fmt tn in
                fprintf fmt "@[<hov 2>assert { forall y:'b%a.@ \
                  is_%s_free_var_in_%s %a (eval (%a) %a) ->@ \
                  is_%s_free_var_in_%s x (s%a y) };@]@,"
                  print_tindex tny
                  tnamev ynamev (print_in_somes "x") lv ps tny
                  (print_in_somes "y") lvy
                  tnamev ynamev print_tindex tny ;
                fprintf fmt "@[<hov 2>assert { forall y:%a.@ \
                  is_%s_free_var_in_%s y %s@ /\\@ is_%s_free_var_in_%s %a (eval (%a) y) ->@ \
                  %a@ &&@ exists y:'b%a.%a};@]@,"
                  (print_in_options (fun fmt ->
                    fprintf fmt "'b%a" print_tindex tny)) lvy
                    ynamev tname vname tnamev ynamev
                    (print_in_somes "x") lv ps tny
                    (print_disj tny ynamev) lvy print_tindex tny print_right tny ;
                fprintf fmt "@[<hov 2>assert { (exists y:%a.@ \
                  is_%s_free_var_in_%s y %s@ /\\@ is_%s_free_var_in_%s %a (eval (%a) y)) ->@ \
                  exists y:'b%a.%a};@]@,"
                  (print_in_options (fun fmt ->
                    fprintf fmt "'b%a" print_tindex tny)) lvy
                    ynamev tname vname tnamev ynamev
                    (print_in_somes "x") lv ps tny
                    print_tindex tny print_right tny ;
                fprintf fmt "@[<hov 2>assert { forall y:'b%a.@ \
                  (is_%s_free_var_in_%s %a %s@ /\\@ is_%s_free_var_in_%s x (s%a y)) ->@ \
                  (is_%s_free_var_in_%s %a (eval (%a) %a)@ &&@ \
                  (exists y:%a. is_%s_free_var_in_%s y %s@ /\\@ \
                  is_%s_free_var_in_%s %a (eval (%a) y))@ &&@ \
                  is_%s_free_var_in_%s %a (subst_%s %s"
                  print_tindex tny ynamev tname (print_in_somes "y") lvy vname
                  tnamev ynamev print_tindex tny
                  tnamev ynamev (print_in_somes "x") lv ps tny (print_in_somes "y") lvy
                  (print_in_options (fun fmt -> fprintf fmt "'b%a" print_tindex tny)) lvy
                  ynamev tname vname tnamev ynamev (print_in_somes "x") lv ps tny
                  tnamev tname (print_in_somes "x") lv tname vname ;
                List.iter (fun tns -> fprintf fmt "@ %a" ps tns ) v2 ;
                fprintf fmt ")@ &&@ is_%s_free_var_in_%s x (subst_%s t"
                  tnamev tname0 tname0 ;
                List.iter (fun tns -> fprintf fmt "@ s%a" print_tindex tns) v ;
                fprintf fmt ")) };@]@," ;
              end) v2
            else fprintf fmt "@[<hov 2>assert { forall y:%a.@ \
              is_%s_free_var_in_%s y %s@ /\\@ eval (%a) y = %a ->@ %a };@]@,"
                (print_in_options (fun fmt ->
                  fprintf fmt "'b%a" print_tindex tnv)) lv tnamev tname vname
                  (print_lift sub dm (fun fmt ->
                    fprintf fmt "s%a" print_tindex tnv) blv) tnv
                  (print_in_somes "x") lv
                  (print_disj tnv tnamev) lv
          end ;
          fprintf fmt "()"
        end else fprintf fmt "()" ) in
    fprintf fmt "@[<hov 2>%t lemma %s_%s_free_var_in_%s (x:'c%a)@ (t:%a)"
      print_kw fp tnamev tname print_tindex tnv (print_type_app dm "b") tn ;
    List.iter (fun tn -> fprintf fmt "@ (s%a:%a)" print_tindex tn
      (print_subst_type sub dm "b" "c") tn) v ;
    fprintf fmt " : unit@\n\
      @[<hov 2>ensures { " ;
    begin if sub
     then let print_or = make_first_case_printer ignore
         (fun fmt -> fprintf fmt "@ \\/@ ") in
       List.iter (fun tn' ->
         if List.mem tnv (bvar_list (type_def tn' dm))
         then let tname' = type_name tn' dm in
           fprintf fmt "%t@[<hov 2>(exists y:'b%a.@ is_%s_free_var_in_%s y t@ \
             /\\@ is_%s_free_var_in_%s x (s%a y))@]"
             print_or print_tindex tn' tname' tname
             tnamev tname' print_tindex tn'
       ) v
     else fprintf fmt "(exists y:'b%a.@ is_%s_free_var_in_%s y t /\\ s%a y = x)"
       print_tindex tnv tnamev tname print_tindex tnv
    end;
    fprintf fmt "@] <->@ ";
    fprintf fmt "is_%s_free_var_in_%s x (@[<hov 2>%s_%s t"
      tnamev tname fp tname ;
    List.iter (fun tn -> fprintf fmt "@ s%a" print_tindex tn) v;
    fprintf fmt ") }@]@\nvariant { size_%s t }@]@\n@[<hov 2>=@\n%a@]@\n@\n"
      tname (print_pattern_match dm tn c var_case cons_case) "t" in
  make_for_bdefs dm (fun tn c v ->
    List.iter (fun tnv ->
      print_decl tnv tn c v) v)

let print_free_var_injective_renaming_lemma fmt dm =
  let print_decl tnv tn c v =
    let tname = type_name tn dm in
    let tnamev = type_name tnv dm in
    fprintf fmt "@[<hov 2>lemma inj_rename_%s_free_var_in_%s :@\n\
      @[<hov 2>forall x:'b%a,@ t:%a"
      tnamev tname print_tindex tnv (print_type_app dm "b") tn ;
    List.iter (fun tn -> fprintf fmt ",@ r%a:%a" print_tindex tn
      (print_subst_type false dm "b" "c") tn ) v ;
    fprintf fmt ".@ injective r%a ->@ \
      (is_%s_free_var_in_%s (r%a x) (@[<hov 2>rename_%s t"
      print_tindex tnv tnamev tname print_tindex tnv tname ;
    List.iter (fun tn -> fprintf fmt "@ r%a" print_tindex tn) v ;
    fprintf fmt ")@] <->@ is_%s_free_var_in_%s x t)@]@]@\n@\n"
      tnamev tname in
  make_for_bdefs dm (fun tn c v ->
    List.iter (fun tnv ->
      print_decl tnv tn c v) v)

let print_free_var_lifting_lemma fmt dm =
  let print_decl tnv tn c v =
    let tname = type_name tn dm in
    let tnamev = type_name tnv dm in
    if tn = tnv
    then begin
      fprintf fmt "@[<hov 2>let lemma none_free_var_in_olifts_%s \
        (s:%a)@ (y:option 'b%a) : unit@\n\
        @[<hov 2>ensures { is_%s_free_var_in_%s None (olifts_%s s y) <->@ \
        y = None }@]@]@\n@[<hov 2>=@\n\
        @[<hov 2>match y with@\n| None -> ()@\n| Some y' -> () @]end@]@\n@\n"
        tname (print_subst_type true dm "b" "c") tn
        print_tindex tn tnamev tname tname ;
      fprintf fmt "@[<hov 2>let lemma some_free_var_in_olifts_%s \
        (s:%a)@ (x:'c%a)@ (y:option 'b%a) : unit@\n\
        @[<hov 2>ensures { is_%s_free_var_in_%s (Some x) (olifts_%s s y) <->@ \
        @[<hov 2>exists y':'b%a.@ y = Some y'@ /\\@ is_%s_free_var_in_%s x (s y')\
        @] }@]@]@\n@[<hov 2>=@\n\
        @[<hov 2>match y with@\n| None -> ()@\n| Some y' -> assert { y = Some y' } @]end@]@\n@\n"
        tname (print_subst_type true dm "b" "c") tn
        print_tindex tnv print_tindex tn tnamev tname tname
        print_tindex tn tnamev tname
    end
    else begin
      fprintf fmt "@[<hov 2>let lemma kind_%s_free_var_in_olifts_%s \
        (s:%a)@ (x:'c%a)@ (y:option 'b%a) : unit@\n\
        @[<hov 2>ensures { is_%s_free_var_in_%s x (olifts_%s s y) <->@ \
        @[<hov 2>exists y':'b%a.@ y = Some y'@ /\\@ is_%s_free_var_in_%s x (s y')\
        @] }@]@]@\n@[<hov 2>=@\n\
        @[<hov 2>match y with@\n| None -> ()@\n| Some y' -> assert { y = Some y' } @]end@]@\n@\n"
        tnamev tname (print_subst_type true dm "b" "c") tn
        print_tindex tnv print_tindex tn tnamev tname tname
        print_tindex tn tnamev tname
    end in
  make_for_bdefs dm (fun tn c v ->
    List.iter (fun tnv ->
      print_decl tnv tn c v) v)

let print_open_close fmt dm =
  let print_decl tnv tn c v =
    let tname = type_name tn dm in
    let tnamev = type_name tnv dm in
    let blevels = TMap.singleton tnv 1 in
    let pc = print_type_app ~blevels dm "b" in
    let po = print_type_app dm "b" in
    fprintf fmt "@[<hov 2>function openv_%s_with_%s (t:%a) (x:'b%a) : %a =@\n\
      @[<hov 2>rename_%s t"
      tname tnamev pc tn print_tindex tnv po tn tname ;
    List.iter (fun tn' ->
      if tnv = tn'
      then fprintf fmt "@ (ocase identity x)"
      else fprintf fmt "@ identity") v ;
    fprintf fmt "@]@]@\n@\n@[<hov 2>function close_%s_with_%s (x:'b%a) (t:%a) : %a =@\n\
      @[<hov 2>rename_%s t"
      tname tnamev print_tindex tnv po tn pc tn tname ;
    List.iter (fun tn' -> if tnv = tn'
      then fprintf fmt "@ (update some x None)"
      else fprintf fmt "@ identity") v;
    fprintf fmt "@]@]@\n@\n@[<hov 2>function close_nothing_%s_with_%s (t:%a) : %a =@\n\
      @[<hov 2>rename_%s t"
      tname tnamev po tn pc tn tname ;
    List.iter (fun tn' -> if tnv = tn'
      then fprintf fmt "@ some"
      else fprintf fmt "@ identity") v;
    fprintf fmt "@]@]@\n@\n@[<hov 2>function opent_%s_with_%s (t:%a) (u:%a) : %a =@\n\
      @[<hov 2>subst_%s t"
      tname tnamev pc tn po tnv po tn tname ;
    List.iter (fun tn' -> if tnv = tn'
      then fprintf fmt "@ (ocase subst_id_%s u)" tnamev
      else fprintf fmt "@ subst_id_%s" (type_name tn' dm)) v;
    fprintf fmt "@]@]@\n@\n@[<hov 2>let lemma open_closure_%s_with_%s\
       (t:%a) (x:'b%a) : unit@\nensures { \
       openv_%s_with_%s (close_%s_with_%s x t) x = t }@\n@]@[<hov 2>=@ \
       assert { extensionalEqual (rcompose (update some x None) \
         (ocase identity x)) identity }@]@\n@\n"
       tname tnamev po tn print_tindex tnv tname tnamev tname tnamev ;
    let local fmt = fprintf fmt "(rcompose (ocase identity x) (update some x None))" in
    fprintf fmt "@[<hov 2>let lemma close_fresh_open_%s_with_%s\
      (t:%a) (x:'b%a) : unit@\nrequires { \
      not(is_%s_free_var_in_%s (Some x) t) }@\n\
      ensures { close_%s_with_%s x (openv_%s_with_%s t x) = t }@]@\n@[<hov 2>=@ \
      assert { forall y:option 'b%a. is_%s_free_var_in_%s y t -> match y with \
        | None -> eval %t y = y | Some z -> eval %t y = y end };@\n\
      assert { %s_free_var_%s_equivalence t %t identity };@\n\
      @[<hov 2>assert { %t = %t }@]@\n"
      tname tnamev pc tn print_tindex tnv
      tnamev tname tname tnamev tname tnamev
      print_tindex tnv tnamev tname local local tnamev tname local
      (fun fmt -> fprintf fmt "rename_%s t" tname ;
        List.iter (fun tn -> if tn = tnv
          then fprintf fmt "@ %t" local
          else fprintf fmt "@ identity") v)
      (fun fmt -> fprintf fmt "rename_%s t" tname ;
        List.iter (fun _ -> fprintf fmt "@ identity") v) ;
    fprintf fmt "@]@\n@\n" ;
    let pr_f fmt = fprintf fmt "subst_of_rename_%s (ocase identity x)" tnamev in
    let pr_s fmt = fprintf fmt "ocase (subst_id_%s : %a) (Var_%s x)"
      tnamev (print_subst_type true dm "b" "b") tnv tnamev in
    fprintf fmt "@[<hov 2>let lemma openv_as_opent_%s_with_%s\
      (t:%a) (x:'b%a) : unit@\n\
      ensures { openv_%s_with_%s t x = opent_%s_with_%s t (Var_%s x) }@]@\n\
      @[<hov 2>=@ \
      @[<hov 2>assert { forall x:'b%a. %t (Some x) =@ %t (Some x) };@]@\n\
      @[<hov 2>assert { %t None =@ %t None };@]@\n\
      @[<hov 2>assert { extensionalEqual (%t)@ (%t) }@]@]@\n@\n"
      tname tnamev pc tn print_tindex tnv tname tnamev tname tnamev tnamev
      print_tindex tnv pr_f pr_s pr_f pr_s pr_f pr_s ;
    fprintf fmt "@[<hov 2>let lemma close_nothing_is_close_fresh_%s_with_%s\
      (t:%a) (x:'b%a) : unit@\nrequires { \
      not(is_%s_free_var_in_%s x t) }@\n\
      ensures { close_%s_with_%s x t = close_nothing_%s_with_%s t }@]@\n\
      @[<hov 2>=@ assert { %s_free_var_%s_equivalence t some (update some x None) }@]@\n@\n"
      tname tnamev po tn print_tindex tnv tnamev tname
      tname tnamev tname tnamev tnamev tname ;
    fprintf fmt "@[<hov 2>lemma opent_close_nothing_%s_with_%s : \
      forall t:%a,u:%a. opent_%s_with_%s (close_nothing_%s_with_%s t) u = t@]@\n@\n"
      tname tnamev po tn po tnv tname tnamev tname tnamev ;
    fprintf fmt "@[<hov 2>lemma openv_close_nothing_%s_with_%s : \
      forall t:%a,x:'b%a. openv_%s_with_%s (close_nothing_%s_with_%s t) x = t@]@\n@\n"
      tname tnamev po tn print_tindex tnv tname tnamev tname tnamev ;
    (* Now, free variables. *)
    List.iter (fun tnv2 ->
      let tnamev2 = type_name tnv2 dm in
      fprintf fmt "@[<hov 2>let lemma close_%s_with_%s_free_var_%s \
        (t:%a) (x:'b%a) (y:'b%a) : unit@\n\
        ensures { is_%s_free_var_in_%s "
        tname tnamev tnamev2 po tn print_tindex tnv print_tindex tnv2 tnamev2 tname ;
      (if tnv = tnv2
       then fprintf fmt "(Some y)"
       else fprintf fmt "y");
      fprintf fmt " (close_%s_with_%s x t) <->@ \
        (is_%s_free_var_in_%s y t" tname tnamev tnamev2 tname ;
      (if tnv = tnv2
       then fprintf fmt "@ /\\@ y <> x");
      fprintf fmt ") }@]@\n@[<hov 2>=@ @[<hov 2>assert { " ;
      (if tnv <> tnv2
       then fprintf fmt "identity y = y"
       else fprintf fmt "y <> x -> update some x None y = Some y");
      fprintf fmt "}@]@]@\n@\n" ;
      fprintf fmt "@[<hov 2>let lemma close_nothing_%s_with_%s_free_var_%s \
        (t:%a) (y:'b%a) : unit@\n\
        ensures { is_%s_free_var_in_%s "
        tname tnamev tnamev2 po tn print_tindex tnv2 tnamev2 tname ;
      (if tnv = tnv2
       then fprintf fmt "(Some y)"
       else fprintf fmt "y");
      fprintf fmt " (close_nothing_%s_with_%s t) <->@ \
        is_%s_free_var_in_%s y t }@]@\n@[<hov 2>=@ ()@]@\n@\n"
        tname tnamev tnamev2 tname ;
      fprintf fmt "@[<hov 2>let lemma opent_%s_with_%s_conserve_free_var_%s \
        (t:%a) (u:%a) (y:'b%a) : unit@\n\
        requires { is_%s_free_var_in_%s "
        tname tnamev tnamev2 pc tn po tnv print_tindex tnv2 tnamev2 tname ;
      (if tnv = tnv2
       then fprintf fmt "(Some y)"
       else fprintf fmt "y");
      fprintf fmt " t }@\nensures { is_%s_free_var_in_%s y (opent_%s_with_%s t u) }@]@\n@[<hov 2>=@ \
        assert { is_%s_free_var_in_%s y "
        tnamev2 tname tname tnamev tnamev2 tnamev2 ;
      (if tnv = tnv2
       then fprintf fmt "(ocase subst_id_%s u (Some y))" tnamev
       else fprintf fmt "(eval (subst_id_%s : %a) y)" tnamev2
         (print_subst_type true dm "b" "b") tnv2 );
      fprintf fmt " }@]@\n@\n" ;
      fprintf fmt "@[<hov 2>let lemma openv_%s_with_%s_conserve_free_var_%s \
        (t:%a) (x:'b%a) (y:'b%a) : unit@\n\
        requires { is_%s_free_var_in_%s "
        tname tnamev tnamev2 pc tn print_tindex tnv print_tindex tnv2 tnamev2 tname ;
      (if tnv = tnv2
       then fprintf fmt "(Some y)"
       else fprintf fmt "y");
      fprintf fmt " t }@\nensures { is_%s_free_var_in_%s y (openv_%s_with_%s t x) }\
        @]@\n@[<hov 2>=@ ()@]@\n@\n"
        tnamev2 tname tname tnamev ;
      fprintf fmt "@[<hov 2>let lemma opent_%s_with_%s_free_var_in_%s \
        (t:%a) (u:%a) (y:'b%a) : unit@\n\
        requires { is_%s_free_var_in_%s y (opent_%s_with_%s t u) }@\n\
        ensures { is_%s_free_var_in_%s "
        tname tnamev tnamev2 pc tn po tnv print_tindex tnv2
        tnamev2 tname tname tnamev
        tnamev2 tname ;
      let memv2_v = List.mem tnv2 (bvar_list (type_def tnv dm)) in
      (if tnv = tnv2
       then fprintf fmt "(Some y) t"
       else fprintf fmt "y t");
      (if memv2_v
       then fprintf fmt " \\/ is_%s_free_var_in_%s y u" tnamev2 tnamev );
       fprintf fmt " }@]@\n@[<hov 2>=@ " ;
      (* An assertion should be added...which one ? *)
      List.iter (fun tnv3 ->
        if List.mem tnv2 (bvar_list (type_def tnv3 dm))
        then if tnv3 = tnv
          then if tnv = tnv2
            then fprintf fmt "@[<hov 2>assert { forall z:option 'b%a. \
              (is_%s_free_var_in_%s z t@ /\\@ \
               is_%s_free_var_in_%s y (ocase subst_id_%s u z)) ->@ \
              match z with \
                | Some z -> y = z && is_%s_free_var_in_%s (Some y) t@ \
                | None -> is_%s_free_var_in_%s y u end};@]@,"
              print_tindex tnv tnamev tname tnamev2 tnamev tnamev
              tnamev2 tname tnamev2 tnamev
            else fprintf fmt "@[<hov 2>assert { forall z:option 'b%a. \
              (is_%s_free_var_in_%s z t /\\@ \
               is_%s_free_var_in_%s y (ocase subst_id_%s u z)) ->@ \
               match z with | None -> is_%s_free_var_in_%s y u \
                 | Some _ -> false end };@]@,"
              print_tindex tnv tnamev tname tnamev2 tnamev tnamev
              tnamev2 tnamev
          else begin let tnamev3 = type_name tnv3 dm in
            fprintf fmt "@[<hov 2>assert { forall z:'b%a. \
              (is_%s_free_var_in_%s z t@ /\\@ is_%s_free_var_in_%s y \
              (eval (subst_id_%s : %a) z))\
              ->@ "
              print_tindex tnv3 tnamev3 tname tnamev2 tnamev3 tnamev3
              (print_subst_type true dm "b" "b") tnv3 ;
            if tnv2 = tnv3
            then fprintf fmt "is_%s_free_var_in_%s y t };@]@," tnamev2 tname
            else fprintf fmt "false };@]@,"
          end
      ) v ;
      fprintf fmt "()@]@]@\n@\n"
    ) v ;
  in
  make_for_bdefs dm (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)

(* proofs/defs scheme :
   1) define considered types
   2) define size operators, one into nat and one into integers,
      for variants. Full-mutually-recursive definition.
   3) using nat_to_int of nat_size as variant,
      prove that we can use the other one
      (much more practical for smt solvers !) as a variant since
      it is never negative. Full-mutually-inductive proof.
   4) define renamings of free variables by full mutual recursion.
   5) prove renaming composition lemma for all types by full mutual induction.
   6) prove identity renaming lemma.
   7) define right renaming (point-wise renaming) of substitution
      (left is normal composition).
   8) prove the renaming compositionality ("associativity") of both
      operations,+ commutation between them.
      At the same time, prove that composing with identity(ies) preserve
      the substitution. It is not strictly necessary, but simplify prover task
      as I usually generate a lot of this kind of renaming in substitution definitions.
   9) define substitution lifting.
   10) prove the commutation lemmaes between
       substitution left/right renaming and substitution lifting. Require
       the renaming composition lemma.
   11) Define all substitutions operators by full mutual recursion.
   12) prove both substitution/renaming composition lemmae, using compositionality
       of renaming/substitution composition operations and lifting commutation lemmaes.
   13) Define substitution compositions by point-wise substitutions.
   14) prove associativity lemmae when there is two substitutions. Require both renaming/substitution
       commutation lemmaes.
   15) prove the commutation lemma between substitution lifting and substitution compositions.
       require the renaming/substitution commutation lemmaes.
   16) prove substitution composition lemma. Require commutation lemmaes about
       substitution composition lifting and composition between a substitution and a renamed one.
   17) Prove associativity of substitution composition.
   18) define identity substitutions/cast of renaming to substitution.
   19) prove that identity substitution is preserved under lifting.
   20) prove the commutation lemma between identity substitutions and renamings.
   21) thanks to the two previous one, prove that the identity substitution preserve
       terms.
   22) prove that identity substitution is actually the neutral element for substitution
       composition.
   23) Prove that behaviour of renamings is preserved when casting to substitution.
   24) Define free variables of kind "something" in term type "something".
   25) Prove the caracterisation of free variables in a renamed term.
   26) Caracterise free variables of application of lifted substitution
       (some kind of inversion lemma)
   2X) Prove the caracterisation of free variables in a substituted term.
   
   (* TODO list *)
   ) !!! find which variables are preserved under renaming/subst,etc.
   ) !!! show the free_var_equivalence lemmaes (including reflexivity this time !)
   ) !!! opening binders with var/terms, free variables of opened term.
   ) !!! closing terms, free variables of closed binder.
   ) !!! open/close commutation properties.
   ) !!! renaming (and thus importantly
         opening a binder with a variable/closing a term) preserve size.
   *)

let until_print fmt dcl =
  let dm = convert_decl dcl in
  let dm = compute_binding_vars dm in
  fprintf fmt "%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n\
    %a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n\
    %a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n%a@\n\
    %a@\n%a@\n"
    print_type_defs dm
    print_size_defs dm
    print_size_lemmae dm
    (print_subst_def dm) false
    (print_composition_lemma dm) (false,false)
    (print_identity_lemma dm) false
    (print_substitution_composition_def dm) false
    (print_associativity_lemma dm) (false,true,false)
    (print_associativity_lemma dm) (true,false,false)
    (print_right_identity_lemma dm) false
    print_subst_lifting dm
    (print_lifting_composition_lemma dm) (false,true)
    (print_lifting_composition_lemma dm) (true,false)
    (print_subst_def dm) true
    (print_composition_lemma dm) (true,false)
    (print_composition_lemma dm) (false,true)
    (print_substitution_composition_def dm) true
    (print_associativity_lemma dm) (false,true,true)
    (print_associativity_lemma dm) (true,false,true)
    (print_associativity_lemma dm) (true,true,false)
    (print_lifting_composition_lemma dm) (true,true)
    (print_composition_lemma dm) (true,true)
    (print_associativity_lemma dm) (true,true,true)
    print_subst_ids dm
    (print_left_identity_lemma dm) false
    (print_identity_lemma dm) true
    (print_left_identity_lemma dm) true
    (print_right_identity_lemma dm) true
    print_renaming_as_subst_lemmae dm
    (print_left_compose_renaming_as_subst_lemma dm) false
    (print_left_compose_renaming_as_subst_lemma dm) true
    (print_right_compose_renaming_as_subst_lemma dm) false
    (print_right_compose_renaming_as_subst_lemma dm) true
    print_free_var_def dm
    print_free_var_equivalence_def dm
    (print_free_var_equivalence_lemma dm) false
    (*(print_free_var_substitution_lemma_predicate dm) false*)
    (print_free_var_substitution_lemma dm) false
    (print_free_var_equivalence_lemma dm) true
    print_free_var_injective_renaming_lemma dm
    print_free_var_lifting_lemma dm
    (print_free_var_substitution_lemma dm) true
    print_open_close dm

let lambda_def =
  TypeDefinition ( "lambda" ,
    [ Var ;
      BCons ("App" , [] , [ DeclaredType "lambda" ; DeclaredType "lambda" ] ) ;
      BCons ( "Lam" , [ "lambda" , None ] , [ DeclaredType "lambda" ] ) ;
      BCons ( "Fix" , [ "lambda" , None ; "lambda" , None ] , [ DeclaredType "lambda" ] ) ] ,
    [] )

let first_order_def =
  [ TypeDefinition ( "fo_term" ,
      [ Var ;
        BCons ("FOApp" , [] , [ TypeVar "function_symbol" ; DeclaredType "fo_term_list" ] ) ] ,
      [] ) ;
    TypeDefinition ( "fo_term_list" ,
      [ BCons ("FONil" , [] , [] ) ;
        BCons ("FOCons" , [] , [ DeclaredType "fo_term" ; DeclaredType "fo_term_list" ] ) ] ,
      [] ) ;
    TypeDefinition ( "fo_formula" ,
      [ BCons ( "FOForall" , [ "fo_term" , None ] , [ DeclaredType "fo_formula" ] ) ;
        BCons ( "FOExists" , [ "fo_term" , None ] , [ DeclaredType "fo_formula" ] ) ;
        BCons ( "FOAnd" , [] , [ DeclaredType "fo_formula" ; DeclaredType "fo_formula" ] ) ;
        BCons ( "FOOr" , [] , [ DeclaredType "fo_formula" ; DeclaredType "fo_formula" ] ) ;
        BCons ( "FONot" , [] , [ DeclaredType "fo_formula" ] ) ;
        BCons ( "FOPred" , [] , [ TypeVar "predicate_symbol" ; DeclaredType "fo_term_list" ] ) ] ,
      [] ) ]

let coc_def =
  [ TypeDefinition ( "coc_term" ,
    [ Var ;
      BCons ( "App" , [] , [ DeclaredType "coc_term" ; DeclaredType "coc_term" ] ) ;
      BCons ( "Lam" , [ "coc_term" , Some (DeclaredType "coc_term") ] , [ DeclaredType "coc_term" ] ) ;
      BCons ( "Forall" , [ "coc_term" , Some (DeclaredType "coc_term") ] , [ DeclaredType "coc_term" ] ) ;
      BCons ( "Type" , [] , [ DeclaredType "integer" ] ) ] , [] ) ;
    TypeDefinition ( "integer" ,
    [ BCons ( "O" , [] , [] ) ;
      BCons ( "S" , [] , [ DeclaredType "integer" ] ) ] , [] ) ]

let fsub_def =
  [ TypeDefinition ( "fsub_type" ,
    [ Var ;
      BCons ( "Arrow" , [] , [ DeclaredType "fsub_type" ; DeclaredType "fsub_type" ] ) ;
      BCons ( "Top" , [] , [] ) ;
      BCons ( "Forall" , [ "fsub_type" , Some(DeclaredType "fsub_type") ] , [ DeclaredType "fsub_type" ] ) ] ,
    [] ) ;
    TypeDefinition ( "fsub_term" ,
    [ Var ;
      BCons ( "App" , [] , [ DeclaredType "fsub_term" ; DeclaredType "fsub_term" ] ) ;
      BCons ( "Lam" , [ "fsub_term" , Some(DeclaredType "fsub_type") ] , [ DeclaredType "fsub_term" ] ) ;
      BCons ( "TLam" , [ "fsub_type" , Some(DeclaredType "fsub_type") ] , [ DeclaredType "fsub_term" ] ) ;
      BCons ( "TApp" , [] , [ DeclaredType "fsub_term" ; DeclaredType "fsub_type" ] ) ] ,
    [] ) ]

let _ =
  let fmt = std_formatter in
  fprintf fmt "@[<hov 2>module A@\nuse import option.Option@\n\
    use import int.Int@\nuse import Nat.Nat@\n\
    use import Functions.Func@\nuse import OptionFuncs.Funcs@\n" ;
  let l = ( [ "function_symbol" ; "predicate_symbol" ] , first_order_def ) in
  (*let l = ( [] , coc_def ) in*)
  (*let l = ( [] , [ lambda_def ] ) in*)
  (*let l = ( [] , fsub_def ) in*)
  let l1 , l2 = l in
  let l = { var_parameters = l1 ; binder_types = l2 } in
  until_print fmt l ;
  fprintf fmt "lemma incoherence : false@\n@]@\nend@\n@\n"



