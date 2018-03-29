
open Macrogen_decls

let rec mapt f = function
  | DeclaredType t -> DeclaredType ( f t )
  | TypeVar x -> TypeVar (f x)

let mapc f = function
  | BCons ( c , b , e ) -> BCons ( f c , List.map (fun (x,y) ->
    f x , List.map (mapt f) y) b , List.map (mapt f) e )
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
module ISet = Set.Make(IntO)
module TO = struct type t = TName.t let compare t1 t2 =
  compare (t1:TName.t:>int) (t2:TName.t:>int) end
module CO = struct type t = CName.t let compare c1 c2 =
  compare (c1:CName.t:>int) (c2:CName.t:>int) end

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

let make_itype t = match t with
  | TypeVar v -> ITVar (VName.make v)
  | DeclaredType t -> ITDecl ( TName.make t)

let make_cons_list cons_set cl =
  let cs,cm = List.fold_left ( fun (cs,cm) -> function
    | BCons ( c , b , e ) -> let c' = CName.make c in
      if CSet.mem c' cs
      then assert false (* TODO->send error "duplicate constructor". *)
      else let b' = List.map ( fun ( x , t ) ->
        TName.make x , List.map make_itype t ) b in
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

(* TODO : various "unbound ident" check. *)

(* TODO : constructor "Var_" forbidden check. *)

(* edges of the dependency graph. *)
let dependents_fold f def acc = match def with
  | ITypeDef ( c , _ ) -> let fold_cons acc c =
      let _ , l1 , l2 = c in
      let acc = List.fold_left ( fun acc ( x , t ) ->
        let acc = f x acc in
          List.fold_left (fun acc -> function
            | ITVar _ -> acc
            | ITDecl u -> f u acc) acc t
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
    let td , _ = TMap.find tn dm in
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
    then process tn ) dm ;
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
        let td , _ = TMap.find tn dm in
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
      let _ , r1 = TMap.find t1 dm in
      let _ , r2 = TMap.find t2 dm in
      compare r1 r2 in
    List.sort compare bv in
  let dmr = TMap.mapi (fun tn (td,rank) -> match td with
    | ITypeAssumption v -> ITypeAssumption (reorder v)
    | ITypeDef ( c , _ ) -> let sccn = TMap.find tn get_scc in
      let bv = get_binding_vars sccn in
      ITypeDef ( c , reorder ( TSet.elements bv ) ) ) dm in
  let b = IMap.bindings get_types in
  let b' = List.sort (fun (k1,_) (k2,_) -> compare k2 k1) b in
  let sccgr = List.rev_map snd b' in
  dmr , sccgr

let convert d =
  let d , names = translate_names d in
  let dmap = make_decl_map d.binder_types in
  let dmap , sccg = compute_binding_vars dmap in
  {
    var_params = List.map VName.make d.var_parameters ;
    type_decls = dmap ;
    names ;
    sccg
  }


