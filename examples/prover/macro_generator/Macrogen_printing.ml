
open Format
open Macrogen_decls
open Macrogen_params

module rec X : module type of Macrogen_printing_sig = X
include X

module Helper = functor (P:Parameters) -> struct
  
  open P
  
  let (<|) f x y = f y x
  let (<<) f x = f x
  
  let indent = pp_open_box <| indent
  let string_printer s = fprintf <| "%s" <| s
  
  let params_printer fmt =
    List.iter (fun tn -> fprintf fmt "@ 'a%s" << var_name dm tn) dm.var_params
  
  let level tn blv = try TMap.find tn blv with Not_found -> 0
  let inc_level tn blv = TMap.add tn ( 1 + level tn blv ) blv
  
  let tindex_printer tn = fprintf <| "%d" <| (tn:TName.t:>int)
  let tname_printer tn = fprintf <| "%s" <| type_name dm tn
  
  let rec rpapply_printer op middle times fmt = match times with
    | 0 -> fprintf fmt "%t" middle
    | n -> fprintf fmt "%t(%t@ %t)@]" indent op
      << rpapply_printer op middle (n-1)
  
  let options_printer = rpapply_printer << string_printer "option"
  let somes_printer = rpapply_printer << string_printer "Some"
  let csomes_printer =
    rpapply_printer << string_printer "compose some"
      << string_printer "identity"
  
  let list_printer f l fmt =
    List.iter (fun x -> f x fmt) l
  
  let sep_list_printer f s l fmt =
    let _ = List.fold_left (fun acc x -> (if acc
      then s fmt ) ; f x fmt ; true ) false l in ()
  
  let binding_type_printer ?(blevels=TMap.empty) p tn =
    options_printer (fprintf <| "'%t%t" <| p <| tindex_printer tn)
     (level tn blevels)
  
  let type_app_printer ?(blevels=TMap.empty) p tn fmt =
    fprintf fmt "%t%t%t@ %t@]" indent << tname_printer tn << params_printer
      << sep_list_printer (fun tn -> binding_type_printer ~blevels p tn)
         (fprintf <| "@ ") (binder_vars dm tn)
  
  let type_printer ?(blevels=TMap.empty) p ty fmt = match ty with
    | ITVar x -> fprintf fmt "'a%s" << var_name dm x
    | ITDecl tn -> type_app_printer ~blevels p tn fmt
  
  let make_first_case_printer p1 p2 =
    let a = ref true in
    fun fmt ->
      if !a
      then ( a:=false ; p1 fmt )
      else p2 fmt
  
  let rec_printer s =
    make_first_case_printer ( fprintf <| s ) ( fprintf <| "with" )
  let rec_fun_printer () = rec_printer "function"
  let rec_type_printer () = rec_printer "type"
  let rec_val_printer () = rec_printer "let rec"
  let rec_ind_printer () = rec_printer "inductive"
  
  let match_variables ?(blevels=TMap.empty) ?(vbase=string_printer "v")
    (cn,bl,tl) =
    let process_type blevels (vars,cnt) ty =
      let vprinter fmt = fprintf fmt "%t%d" vbase cnt in
      ((vprinter,blevels,ty)::vars,cnt+1) in
    let process_types blevels = List.fold_left (process_type blevels) in
    let (vars,blevels,cnt) =
      List.fold_left (fun (vars,blevels,cnt) (bo,tys) ->
        let nblevels = inc_level bo blevels in
        let vars,cnt = process_types blevels (vars,cnt) tys in
        (vars,nblevels,cnt) ) ( [] , blevels , 0 ) bl in
    let (vars,_) = process_types blevels (vars,cnt) tl in
    List.rev vars
  
  let cons_case_printer ?(blevels=TMap.empty) ?(vbase=string_printer "v")
    case (cn,bl,tl) fmt =
    let vars = match_variables ~blevels ~vbase (cn,bl,tl) in
    fprintf fmt "%t| %t%s%t@] ->@ %t%t@]@]" indent indent << cons_name dm cn
      << list_printer (fun (vp,_,_) fmt -> fprintf fmt "@ %t" vp) vars
      << indent << case vars
  
  let var_case_printer ?(vbase=string_printer "v") case tn fmt =
    let vname fmt = fprintf fmt "%t0" vbase in
    fprintf fmt "%t| %t%t@ %t0@] ->@ %t%t@]@]" indent indent
      << variable_name tn << vbase << indent << case vname
  
  let match_printer ?(blevels=TMap.empty) ?(vbase=string_printer "v")
    tn vcase ccase mt fmt =
    match type_def dm tn with
      | ITypeAssumption _ -> assert false
      | ITypeDef ( c , _ ) ->
        fprintf fmt "%tmatch %t with" indent mt ;
        (if c.var_present
         then fprintf fmt "@ %t" << var_case_printer ~vbase vcase tn);
        fprintf fmt "%t@]@ end"
          << list_printer (fun cs fmt ->
            fprintf fmt "@ %t%t@]" indent
              << cons_case_printer ~blevels ~vbase ( ccase cs ) cs) c.cons_list
  
  let make_for_defs f =
    TMap.iter (fun tn -> function
      | ITypeAssumption _ -> ()
      | ITypeDef ( c , v ) -> f tn c v) dm.type_decls
  
  let make_for_bdefs f =
    make_for_defs (fun tn c -> function
      | [] -> ()
      | v -> f tn c v)
  
  let make_for_vdefs f =
    make_for_defs (fun tn c v ->
      if c.var_present
      then f tn c v
      else ())
  
  let lemma_cons_case case _ vars fmt =
    fprintf fmt "%t()"
      << list_printer (fun (vname,blevels,ty) fmt ->
          match ty with
            | ITVar _ -> ()
            | ITDecl tn -> fprintf fmt "%t ;@ "
                << case vname blevels tn ) vars
  
  let blemma_cons_case case _ vars fmt =
    fprintf fmt "%t()"
      << list_printer (fun (vname,blevels,ty) fmt ->
          match ty with
            | ITVar _ -> ()
            | ITDecl tn -> match binder_vars dm tn with
              | [] -> ()
              | _ -> fprintf fmt "%t ;@ "
                << case vname blevels tn ) vars
  
  let reconstruct_cons_case case (cn,_,_) vars fmt =
    fprintf fmt "%t%s%t@]" indent << cons_name dm cn
      << list_printer (fun (vname,blevels,ty) fmt ->
          match ty with
            | ITVar _ -> fprintf fmt "@ %t" vname
            | ITDecl tn -> match binder_vars dm tn with
              | [] -> fprintf fmt "@ %t" vname
              | _ -> fprintf fmt "@ %t(%t)@]" indent
                << case vname blevels tn ) vars
  
  let lift_printer sub sp blevels tn fmt =
    let lift = if sub
      then slift_name tn
      else fprintf <| "olift" in
    let middle = rpapply_printer lift sp << level tn blevels in
    if sub
    then fprintf fmt "%t(%t@ %t%t)@]" indent << rename_subst_name tn
      << middle << list_printer (fun tn' fmt ->
         if tn = tn'
         then fprintf fmt "@ identity"
         else fprintf fmt "@ %t"
           (csomes_printer << level tn' blevels))
         (binder_vars dm tn)
    else middle fmt
  
  let subst_type_printer sub ?(blevels=TMap.empty) p1 p2 tn fmt =
    let p' p tn fmt = fprintf fmt "'%t%t" p << tindex_printer tn in
    fprintf fmt "%tfunc@ %t" indent
      (options_printer << p' p1 tn << level tn blevels) ;
    if sub
    then fprintf fmt "@ %t(%t)@]@]" indent << type_app_printer ~blevels p2 tn
    else fprintf fmt "@ %t@]"
      (options_printer << p' p2 tn << level tn blevels)
  
  let print_composition sub1 sub2 tn p1 p2 fmt =
    if sub1
    then begin
      fprintf fmt "%t%t@ %t%t@]"
        indent
        (if sub2 then subst_compose_name tn else rename_subst_name tn) p1
        << list_printer (fun tn fmt ->
            fprintf fmt "@ %t" << p2 tn
          ) (binder_vars dm tn)
    end else fprintf fmt "%trcompose@ %t@ %t@]" indent p1 << p2 tn
  
  let typed_identity_printer sub b tn fmt =
    let name = if sub
      then subst_identity_name tn
      else string_printer "identity" in
    fprintf fmt "(%t%t :@ %t@])" indent name
      << subst_type_printer sub b b tn
  
  let typed_sor_printer p b tn fmt =
    fprintf fmt "(%t%t%t@ %t@] :@ %t@])" indent indent
      << subst_of_rename_name tn << p << type_app_printer b tn
  
end

module MakePP = functor (P0:Parameters) -> struct
  
  module P = P0
  module H = Helper(P)
  
end


