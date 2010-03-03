open Ident
open Term
open Theory

let ttrue _ = true
let ffalse _ = false

type env = { fs : (vsymbol list * term) Mls.t;
             ps : (vsymbol list * fmla) Mls.t}

let empty_env = { fs = Mls.empty;
                  ps = Mls.empty}
open Format

let print_env fmt env =
  let print_map iter pterm pfs = Pp.print_iter2 iter Pp.newline Pp.comma pfs
    (Pp.print_pair (Pp.print_list Pp.comma Pretty.print_vsymbol) pterm) in
  fprintf fmt "fs:@[<hov>%a@]@\nps:@[<hov>%a@]@\n"
    (print_map Mls.iter Pretty.print_term Pretty.print_lsymbol) env.fs
    (print_map Mls.iter Pretty.print_fmla Pretty.print_lsymbol) env.ps

let rec replacet env t = 
  let t = substt env t in
  match t.t_node with
    | Tapp (fs,tl) ->
        begin try 
          let (vs,t) = Mls.find fs env.fs in
          let m = List.fold_left2 (fun acc x y -> Mvs.add x y acc)
            Mvs.empty vs tl in
          t_subst m t
        with Not_found -> t end
    | _ -> t

and replacep env f = 
  let f = substp env f in
  match f.f_node with
    | Fapp (ps,tl) ->
        begin try 
          let (vs,t) = Mls.find ps env.ps in
          let m = List.fold_left2 (fun acc x y -> Mvs.add x y acc) 
            Mvs.empty vs tl in
          f_subst m f
        with Not_found -> f end
    | _ -> f

and substt env d = t_map (replacet env) (replacep env) d
and substp env d = f_map (replacet env) (replacep env) d

let fold env d = 
  match d.d_node with
    | Dlogic [l] -> begin
        match l with
          | Lfunction (fs,None) -> env,[d] 
          | Lfunction (fs,Some fmla) -> 
              let _,vs,t = open_fs_defn fmla in
              let t = replacet env t in
              if t_s_any ffalse ((==) fs) t 
              then  env,[create_logic [Lfunction(fs,Some (make_fs_defn fs vs t))]]
              else {env with fs = Mls.add fs (vs,t) env.fs},[]
          | Lpredicate (ps,None) -> env,[d]
          | Lpredicate (ps,Some fmla) -> 
              let _,vs,f = open_ps_defn fmla in
              let f = replacep env f in
              if f_s_any ffalse ((==) ps) f 
              then  env,[create_logic [Lpredicate(ps,Some (make_ps_defn ps vs f))]]
              else {env with ps = Mls.add ps (vs,f) env.ps},[]
          | Linductive (ps,fmlal) -> 
              let fmlal = List.map (fun (id,fmla) -> id,replacep env fmla) fmlal in
              env,[create_logic [Linductive (ps,fmlal)]]
      end
    | Dlogic dl -> env,
        [create_logic 
           (List.map 
              (function
                 | Lfunction (fs,None) as a -> a 
                 | Lfunction (fs,Some fmla) -> 
                     let _,vs,t = open_fs_defn fmla in
                     let t = replacet env t in
                     Lfunction (fs,Some (make_fs_defn fs vs t))
                 | Lpredicate (ps,None) as a -> a
                 | Lpredicate (ps,Some fmla) ->
                     let _,vs,t = open_ps_defn  fmla in
                     let t = replacep env t in
                     Lpredicate (ps,Some (make_ps_defn ps vs t))
                 | Linductive (ps,fmlal) ->
                     let fmlal = List.map 
                       (fun (id,fmla) -> id,replacep env fmla) fmlal in
                     Linductive (ps,fmlal)
              ) dl)]
    | Dtype dl -> env,[d]
    | Dprop (k,i,fmla) -> env,[create_prop k (id_dup i) (replacep env fmla)]
        
let t = Transform.TDecl.fold_map_left fold empty_env
  
let t_use = Transform.TDecl_or_Use.fold_map_left 
  (fun env d -> match d with 
     | Decl d -> let env,l = (fold env d) in
       env,List.map (fun d -> Decl d) l 
     | Use _ as u -> env,[u]) empty_env
  
