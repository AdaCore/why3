
let (<<) f x = f x

open Macrogen_printing
open Macrogen_decls
open Macrogen_nlparams
open Format

module Printer = functor (P:PrintParameters) ->
  functor (NLP:NLParameters) -> struct

  open P.P
  open P.H
  open NLP

  let nltype_app_printer b tn fmt =
    fprintf fmt "%t%t%t%t@]" indent << nltype_name tn
      << params_printer << list_printer (fun tn fmt ->
          fprintf fmt "@ '%t%t" << b << tindex_printer tn
        ) (binder_vars dm tn)

  let nlrtype_app_printer tn fmt =
    fprintf fmt "%t%t%t%t@]" indent << nltype_name tn
      << params_printer << list_printer (fun tn fmt ->
        fprintf fmt "@ %t" << nlfree_var_type_name tn
      ) (binder_vars dm tn)

  (*let nlcons_case_printer ?(vbase=string_printer "v") case (cn,bl,tl) fmt =
    fprintf fmt "%t| %t%t" indent indent << nlcons_name cn ;
    let process_type blevels (vars,cnt) ty =
      let vprinter fmt = fprintf fmt "%t%d" vbase cnt in
      fprintf fmt "@ %t" vprinter ;
      ((vprinter,blevels,ty)::vars,cnt+1) in
    let process_types blevels = List.fold_left (process_type blevels) in
    let (vars,blevels,cnt) =
      List.fold_left (fun (vars,blevels,cnt) (bo,tys) ->
        let nblevels = inc_level bo blevels in
        let vars,cnt = process_types blevels (vars,cnt) tys in
        (vars,nblevels,cnt) ) ( [] , TMap.empty , 0 ) bl in
    let (vars,_) = process_types blevels (vars,cnt) tl in
    fprintf fmt "@] ->@ %t%t@]@]" << indent << case (List.rev vars)*)

  let nlcons_case_printer ?(vbase=string_printer "v") case (cn,bl,tl) fmt =
    fprintf fmt "%t| %t%t" indent indent << nlcons_name cn ;
    let process_type (vars,cnt) ty =
      let vprinter fmt = fprintf fmt "%t%d" vbase cnt in
      fprintf fmt "@ %t" vprinter ;
      ((vprinter,ty)::vars,cnt+1) in
    let process_types = List.fold_left process_type in
    let (vars,blevels,cnt) =
      List.fold_left (fun (vars,blevels,cnt) (bo,tys) ->
        let nblevels = inc_level bo blevels in
        let vars0,cnt = process_types ([],cnt) tys in
        ((blevels,bo,List.rev vars0)::vars,nblevels,cnt) ) ( [] , TMap.empty , 0 ) bl in
    let (vars0,_) = process_types ([],cnt) tl in
    let v0 = (List.rev vars,(blevels,List.rev vars0)) in
    fprintf fmt "@] ->@ %t%t@]@]" << indent << case v0

  let flatten (v1,(blv,v2)) =
    let add blv l = List.map (fun (x,ty) -> (x,blv,ty)) l in
    let v = List.fold_left (fun acc (blv,_,vars) ->
      List.rev_append (add blv vars) acc) [] v1 in
    List.rev (List.rev_append (add blv v2) v)

  let nlvar_case_printer ?(vbase=string_printer "v") fcase bcase tn fmt =
    let vname fmt = fprintf fmt "%t0" vbase in
    fprintf fmt "%t| %t%t@ %t0@] ->@ %t%t@]@]@ \
      %t| %t%t@ %t0@] ->@ %t%t@]@]" indent indent
      << free_variable_name tn << vbase << indent << fcase vname
      << indent << indent << bound_variable_name tn << vbase
      << indent << bcase vname

  let nlmatch_printer ?(vbase=string_printer "v") tn
    fvcase bvcase ccase mt fmt =
    match type_def dm tn with
      | ITypeAssumption _ -> assert false
      | ITypeDef ( c , _ ) ->
        fprintf fmt "%tmatch %t with" indent mt ;
        (if c.var_present
         then fprintf fmt "@ %t"
           << nlvar_case_printer ~vbase fvcase bvcase tn);
        fprintf fmt "%t@]@ end"
          << list_printer (fun cs fmt ->
            fprintf fmt "@ %t%t@]" indent
              << nlcons_case_printer ~vbase ( ccase cs ) cs) c.cons_list

  let env_type_printer ?(blevels=TMap.empty) inp b tn fmt =
    fprintf fmt "%t %t -> (%t)@]"
      indent inp << type_app_printer ~blevels b tn

  let nlbenv_type_printer ?(blevels=TMap.empty) b tn fmt =
    env_type_printer ~blevels (string_printer "int") b tn fmt

  let benv_lift_printer sp blevels tn fmt =
    let lift = shift_name tn in
    let middle = rpapply_printer lift sp << level tn blevels in
    fprintf fmt "%t(%t@ %t%t)@]" indent << rename_subst_name tn
      << middle << list_printer (fun tn' fmt ->
         if tn = tn'
         then fprintf fmt "@ identity"
         else fprintf fmt "@ %t"
           (csomes_printer << level tn' blevels))
         (binder_vars dm tn)

  let frenv_lift_printer sp blevels tn fmt =
    fprintf fmt "%t(%t@ %t%t)@]" indent << rename_subst_name tn
      << sp
      << list_printer (fun tn fmt ->
        fprintf fmt "@ %t" (csomes_printer << level tn blevels))
        (binder_vars dm tn)

  let full_reconstruct_cons_case case (cn,_,_) vars fmt =
    let vars = flatten vars in
    fprintf fmt "%t%s%t@]" indent << cons_name dm cn
      << list_printer (fun (vname,blevels,ty) fmt ->
          match ty with
            | ITVar _ -> fprintf fmt "@ %t" vname
            | ITDecl tn -> fprintf fmt "@ %t(%t)@]" indent
                << case vname blevels tn ) vars

  let nlrecons_case case (cn,_,_) vars fmt =
    let vars = flatten vars in
    fprintf fmt "%t%t%t@]" indent << nlcons_name cn
      << list_printer (fun (vname,blevels,ty) fmt ->
          match ty with
            | ITVar _ -> fprintf fmt "@ %t" vname
            | ITDecl tn -> match binder_vars dm tn with
              | [] -> fprintf fmt "@ %t" vname
              | _ -> fprintf fmt "@ %t(%t)@]" indent
                << case vname blevels tn ) vars

  let type_defs_printer fmt =
    List.iter (fun scc ->
      let tp = rec_type_printer () in
      List.iter (fun tn ->
        match type_def dm tn with
          | ITypeAssumption _ -> ()
          | ITypeDef (c,v) -> let b = string_printer "b" in
            fprintf fmt "%t%t %t%t@] =@ " indent tp indent
              << nltype_app_printer b tn ;
            (if c.var_present
             then fprintf fmt "| %t %t@\n| %t int@\n" << free_variable_name tn
               << binding_type_printer b tn
               << bound_variable_name tn);
            let internal ty fmt = match ty with
              | ITVar x -> fprintf fmt "@ 'a%s" << var_name dm x
              | ITDecl tn -> fprintf fmt "@ (%t)" << nltype_app_printer b tn in
            fprintf fmt "%t@]@\n@\n" << list_printer (fun (cn,bl,tl) fmt ->
                fprintf fmt "%t| %t%t%t@]@\n" indent << nlcons_name cn
                 << list_printer (fun (_,tys) -> list_printer internal tys) bl
                 << list_printer internal tl) c.cons_list
      ) scc
    ) dm.sccg

  let size_defs_printer fmt =
    let pr = rec_fun_printer () in
    let print_decl is_nat tn _ _ =
      let fn = if is_nat then nat_nlsize_name else nlsize_name in
      let tyn = if is_nat then "nat" else "int" in
      let unity = if is_nat then "one_nat" else "1" in
      let op = if is_nat
        then fun p fmt ->
          fprintf fmt "%tlet s = add_nat@ (%t)@ s in@]@ " indent p
        else fun p fmt -> fprintf fmt "let s = %t@ +@ s in@ " p in
      let vcase _ fmt = fprintf fmt "%s" unity in
      let cons_case _ v fmt =
        let v = flatten v in
        let rec aux v fmt = match v with
          | [] -> fprintf fmt "let s = %s in@ " unity
          | ( vn , _ , ty ) :: q -> match ty with
            | ITVar _ -> aux q fmt
            | ITDecl tn -> fprintf fmt "%t%t" << aux q
              << op (fun fmt -> fprintf fmt "%t%t@ %t@]" indent << fn tn << vn)
        in fprintf fmt "%ts" << aux v in
      fprintf fmt "%t%t %t@ (t:%t) :@ %s@ =@ %t@]@\n@\n" indent pr << fn tn
        << nltype_app_printer (string_printer "b") tn
        << tyn
        << nlmatch_printer tn vcase vcase cons_case (string_printer "t") in
    make_for_defs << print_decl true ;
    make_for_defs << print_decl false

  let size_lemma_printer fmt =
    let pr = rec_val_printer () in
    let print_decl tn _ _ =
      let vcase _ fmt = fprintf fmt "()" in
      let cons_case cs v =
        let v = flatten v in
        lemma_cons_case (fun vp blevels tn fmt ->
          fprintf fmt "%t%t@ %t@]" indent << nlsize_lemma_name tn << vp
        ) cs v in
      fprintf fmt "%t%t lemma %t@ (t:%t) :@ unit@ \
        %tensures {@ %t@ t@ >@ 0@ }@]@ \
        %tvariant {@ nat_to_int %t(%t@ t)@]@ }@]@ =@ %t@]@\n@\n" indent pr
        << nlsize_lemma_name tn
        << nltype_app_printer (string_printer "b") tn
        << indent << nlsize_name tn
        << indent << indent << nat_nlsize_name tn
        << nlmatch_printer tn vcase vcase cons_case (string_printer "t") in
    make_for_defs print_decl

  (* Shifting *)

  let shift_defs_printer fmt =
    let b = string_printer "b" in
    let print_decl tn _ v =
      let blevels = inc_level tn TMap.empty in
      let pl fmt =
        fprintf fmt "function@ %t@ (bnd:%t) :@ %t"
          << shift_name tn << nlbenv_type_printer b tn
          << nlbenv_type_printer ~blevels b tn in
      let pr fmt =
        fprintf fmt "%tif i = 0@ \
          %tthen@ %t%t@ None@]@]@ \
          %telse@ %t%t@ (bnd (i-1))%t@]@]@]"
          indent indent indent << variable_name tn
          << indent << indent << rename_name tn
          << list_printer (fun tn' fmt ->
              if tn = tn'
              then fprintf fmt "@ some"
              else fprintf fmt "@ identity"
            ) v in
      fprintf fmt "(*%t@ Abstraction@ definition@ axiom :@ \
        %t%t@ =@ (%t\\ i:int.@ %t@])@]@]*)@\n\
        %t%t@]@\n%taxiom@ %t_definition :@ \
        %tforall@ bnd:%t,@ i:int.@ %t%teval@ (%t bnd)@ i@]@ =@ %t@]@]@]@\n@\n"
        indent indent pl indent pr
        indent pl indent << shift_name tn << indent
        << nlbenv_type_printer b tn << indent
        << indent << shift_name tn << pr
    in
    make_for_vdefs print_decl

  (* shift composition. *)

  let shift_lemma_printer fmt =
    let b,c = string_printer "b",string_printer "c" in
    let print_decl tn _ v =
      let blevels = inc_level tn TMap.empty in
      let lifting tn' fmt =
        if tn = tn'
        then fprintf fmt "(%t%t@ s%t@])" indent
              << slift_name tn << tindex_printer tn
        else lift_printer true (fun fmt ->
          fprintf fmt "s%t" << tindex_printer tn') blevels tn' fmt in
      let p1 fmt =
        fprintf fmt "%t%t@ (%t%t@ bnd@])%t@]"
          indent << subst_compose_name tn << indent
          << shift_name tn << list_printer (fun tn fmt ->
            fprintf fmt "@ %t" << lifting tn) v in
      let p2 fmt =
        fprintf fmt "%t%t (%t%t@ bnd%t@])@]"
          indent << shift_name tn << indent
            << subst_compose_name tn << list_printer (fun tn fmt ->
            fprintf fmt "@ s%t" << tindex_printer tn) v in
      fprintf fmt "%tlet@ lemma@ %t@ (bnd:%t)%t :@ unit@ \
        %tensures {@ %t@ =@ %t@ }@]@ =@ \
        %tassert {@ %tforall i:int.@ (i = 0 \\/ i <> 0) ->@ \
          %t%t@ (%t%t@ bnd@ i@])%t@]@ =@ %teval (%t) i@]@]@ }@] ;@ \
        %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@]@]@\n@\n"
        indent << shift_lemma_name tn << nlbenv_type_printer b tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ (s%t:%t)" << tindex_printer tn
            << subst_type_printer true b c tn) v
        << indent << p1 << p2 << indent << indent << indent
        << subst_name tn << indent << shift_name tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ %t" << lifting tn) v
        << indent << p2 << indent << indent << p1 << p2
    in
    make_for_vdefs print_decl

  (* model. *)

  let model_defs_printer fmt =
    let b,c = string_printer "b",string_printer "c" in
    let pr = rec_fun_printer () in
    let print_decl tn _ v =
      let fvcase vname fmt =
        fprintf fmt "fr%t %t" << tindex_printer tn << vname in
      let bvcase vname fmt =
        fprintf fmt "bnd%t %t" << tindex_printer tn << vname in
      let ccase = full_reconstruct_cons_case (fun vname blv tn fmt ->
          fprintf fmt "%t@ %t%t"
            << model_name tn << vname << list_printer (fun tn fmt ->
              fprintf fmt "@ (%t)@ (%t)" << frenv_lift_printer (fun fmt ->
                fprintf fmt "fr%t" << tindex_printer tn) blv tn
                << benv_lift_printer (fun fmt ->
                  fprintf fmt "bnd%t" << tindex_printer tn) blv tn
            ) (binder_vars dm tn)) in
      fprintf fmt "%t%t@ %t@ (t:%t)%t :@ %t@ =@ %t@]@\n@\n"
        indent pr << model_name tn << nltype_app_printer b tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ (fr%t:%t)@ (bnd%t:%t)" << tindex_printer tn
            << subst_type_printer true b c tn
            << tindex_printer tn
            << nlbenv_type_printer c tn) v
        << type_app_printer c tn
        << nlmatch_printer tn fvcase bvcase ccase (string_printer "t")
    in
    make_for_defs print_decl

  let model_commutation_prelude sub pr tn v fmt =
    let b,c,d = string_printer "b",string_printer "c",string_printer "d" in
    let variant = if sub
      then fun fmt ->
        fprintf fmt "%tvariant {@ %t t@ }@]@ " indent << nlsize_name tn
      else ignore in
    fprintf fmt "%t%t@ lemma@ %t@ (t:%t)%t :@ unit@ \
      %tensures {@ %t%t@ t%t@]@ =@ %t%t@ (%t%t@ t%t@])%t@]@ }@]@ \
      %t=@ "
      indent pr << (if sub
        then model_subst_commutation_lemma_name tn
        else model_rename_commutation_lemma_name tn)
      << nltype_app_printer b tn
      << list_printer (fun tn fmt ->
        fprintf fmt "@ (fr%t:%t)@ (bnd%t:%t)@ (s%t:%t)" << tindex_printer tn
          << subst_type_printer true b c tn << tindex_printer tn
          << nlbenv_type_printer c tn << tindex_printer tn
          << subst_type_printer sub c d tn) v
      << indent << indent << model_name tn << list_printer (fun tn fmt ->
        let side2 tn fmt = fprintf fmt "s%t" << tindex_printer tn in
        fprintf fmt "@ (%t)@ (%t)"
          << print_composition true sub tn (fun fmt ->
            fprintf fmt "fr%t" << tindex_printer tn) side2
          << print_composition true sub tn (fun fmt ->
            fprintf fmt "bnd%t" << tindex_printer tn) side2) v
      << indent << (if sub then subst_name tn else rename_name tn)
      << indent << model_name tn
      << list_printer (fun tn fmt ->
        fprintf fmt "@ fr%t@ bnd%t" << tindex_printer tn
          << tindex_printer tn) v
      << list_printer (fun tn fmt ->
        fprintf fmt "@ s%t" << tindex_printer tn) v
      << variant

  let model_subst_commutation_lemma_printer fmt =
    let pr = rec_val_printer () in
    let print_decl tn _ v =
      let vcase _ fmt = fprintf fmt "()" in
      let ccase cs v =
        let v = flatten v in
        blemma_cons_case (fun vname blv tn fmt ->
        let p1 tn fmt = fprintf fmt "fr%t" << tindex_printer tn in
        let p2 tn fmt = fprintf fmt "bnd%t" << tindex_printer tn in
        let p3 tn fmt = fprintf fmt "s%t" << tindex_printer tn in
        let pa tn = list_printer (fun tn fmt ->
          fprintf fmt "@ %t" << p3 tn) (binder_vars dm tn) in
        let p10 tn = frenv_lift_printer (p1 tn) blv tn in
        let p20 tn = benv_lift_printer (p2 tn) blv tn in
        let p30 tn = lift_printer true (p3 tn) blv tn in
        let pa0 tn = list_printer (fun tn fmt ->
          fprintf fmt "@ (%t)" << p30 tn) (binder_vars dm tn) in
        let v0 = binder_vars dm tn in
        fprintf fmt "%t@ %t%t%t"
          << model_subst_commutation_lemma_name tn
          << vname << list_printer (fun tn fmt ->
            fprintf fmt "@ (%t)@ (%t)@ (%t)" << p10 tn << p20 tn << p30 tn) v0
          << list_printer (fun tn fmt -> let sn = subst_compose_name tn in
            fprintf fmt " ;@ %tassert {@ %t%t@ %t%t@]@ =@ %t@ }@] ;@ \
              %tassert {@ %t%t@ %t@ %t@]@ =@ %t@ }@]"
              indent indent << sn << p10 tn << pa0 tn
              << frenv_lift_printer (fun fmt ->
                fprintf fmt "(%t%t@ %t%t@])" indent sn
                  << p1 tn << pa tn) blv tn
              << indent << indent << sn << p20 tn << pa0 tn
              << benv_lift_printer (fun fmt ->
                fprintf fmt "(%t%t@ %t@ %t@])" indent sn
                  << p2 tn << pa tn) blv tn) v0
          ) cs v in
      fprintf fmt "%t%t@]@\n@\n"
        << model_commutation_prelude true pr tn v
        << nlmatch_printer tn vcase vcase ccase (string_printer "t")
    in
    make_for_bdefs print_decl

  (* Derive immediately from subst commutation. *)

  let model_rename_commutation_lemma_printer fmt =
    let pr fmt = fprintf fmt "let" in
    let print_decl tn _ v =
      fprintf fmt "%t%t%t@ t%t@]@]@\n@\n"
        << model_commutation_prelude false pr tn v
        << indent
        << model_subst_commutation_lemma_name tn
        << list_printer (fun tn fmt ->
          let ti = tindex_printer tn in
          fprintf fmt "@ fr%t@ bnd%t@ (%t%t@ s%t@])"
            ti ti indent << subst_of_rename_name tn << ti) v in
    make_for_bdefs print_decl

  let correct_indexes_printer fmt =
    let pr = make_first_case_printer << string_printer "predicate"
      << string_printer "with" in
    let print_decl tn _ _ =
      let fvcase _ fmt = fprintf fmt "true" in
      let bvcase vname fmt = fprintf fmt "%t >= 0" vname in
      let ccase _ v =
        let v = flatten v in
        let printed = ref false in
        let rec aux v fmt = match v with
          | [] -> if not(!printed)
            then fprintf fmt "true"
          | (vn,_,ty) :: q -> match ty with
            | ITVar _ -> aux q fmt
            | ITDecl tn -> match binder_vars dm tn with
              | [] -> aux q fmt
              | _ -> (if !printed
                then fprintf fmt "@ /\\@ "
                else printed := true);
                fprintf fmt "%t%t@ %t@]%t" indent
                  << correct_indexes_name tn
                  << vn
                  << aux q in
        aux v in
      fprintf fmt "%t%t@ %t@ (t:%t)@ =@ %t@]@\n@\n" indent pr
        << correct_indexes_name tn
        << nltype_app_printer (string_printer "b") tn
        << nlmatch_printer tn fvcase bvcase ccase (string_printer "t") in
    make_for_bdefs print_decl

  let bound_depth_printer fmt =
    let pr = rec_fun_printer () in
    let print_decl tnv tn _ _ =
      let fvcase _ fmt = fprintf fmt "0" in
      let bvcase = if tn = tnv
        then fun vname fmt -> fprintf fmt "1@ +@ %t" vname
        else fun _ fmt -> fprintf fmt "0" in
      let ccase _ v =
        let v = flatten v in
        let printed = ref false in
        let rec aux v fmt = match v with
          | [] -> if !printed
            then fprintf fmt "a"
            else fprintf fmt "0"
          | (vn,blv,ty) :: q -> match ty with
            | ITDecl tn when List.mem tnv (binder_vars dm tn) ->
              fprintf fmt "%tlet b =@ %t%t@ %t@]@]@ in@ "
                indent indent << bound_depth_name tnv tn << vn ;
              let lv = level tnv blv in
              (if lv <> 0
               then fprintf fmt "%tlet b =@ %tif b < %d@ \
                 then 0@ else@ b - %d@]@]@ in@ " indent indent lv lv);
              (if !printed
               then fprintf fmt "%tlet a =@ %tif a > b@ \
                   then a@ else b@]@]@ in@ " indent indent
               else (printed := true; fprintf fmt "let a = b in@ "));
              aux q fmt
            | _ -> aux q fmt in
        aux v in
      fprintf fmt "%t%t@ %t@ (t:%t) :@ int@ =@ %t@]@\n@\n" indent pr
        << bound_depth_name tnv tn
        << nltype_app_printer (string_printer "b") tn
        << nlmatch_printer tn fvcase bvcase ccase (string_printer "t") in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)

  let bound_depth_lemma_printer fmt =
    let pr = rec_val_printer () in
    let print_decl tnv tn _ v =
      let vcase _ fmt = fprintf fmt "()" in
      let ccase cs v =
        let v = flatten v in
        blemma_cons_case (fun vname blv tn fmt ->
        if List.mem tnv (binder_vars dm tn)
        then fprintf fmt "%t@ %t"
          << bound_depth_lemma_name tnv tn << vname
        else fprintf fmt "()"
      ) cs v in
      fprintf fmt "%t%t@ lemma@ %t@ (t:%t) :@ unit@ \
        %trequires {@ %t%t@ t@]@ }@]@ \
        %tensures {@ %t%t@ t@] >= 0@ }@]@ \
        %tvariant {@ %t%t@ t@]@ }@]@ =@ %t@]@\n@\n"
        indent pr << bound_depth_lemma_name tnv tn
        << nltype_app_printer (string_printer "b") tn
        << indent << indent << correct_indexes_name tn
        << indent << indent << bound_depth_name tnv tn
        << indent << indent << nlsize_name tn
        << nlmatch_printer tn vcase vcase ccase (string_printer "t") in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)

  let model_equal_lemma_printer fmt =
    let pr = rec_val_printer () in
    let b,c = string_printer "b",string_printer "c" in
    let print_decl tn _ v =
      let vcase _ fmt = fprintf fmt "()" in
      let ccase cs v =
        let v = flatten v in
        blemma_cons_case (fun vname blv tn fmt ->
        let v0 = binder_vars dm tn in
        fprintf fmt "%t%t@ %t%t@]"
          indent << model_equal_lemma_name tn
          << vname << list_printer (fun tnv fmt ->
            fprintf fmt "@ (%t)@ (%t)@ (%t)@ (%t)" << frenv_lift_printer (fun fmt ->
                  fprintf fmt "fr1%t" << tindex_printer tnv) blv tnv
              << frenv_lift_printer (fun fmt ->
                fprintf fmt "fr2%t" << tindex_printer tnv) blv tnv
              << benv_lift_printer (fun fmt ->
                fprintf fmt "bnd1%t" << tindex_printer tnv) blv tnv
              << benv_lift_printer (fun fmt ->
                fprintf fmt "bnd2%t" << tindex_printer tnv) blv tnv) v0) cs v in
      let p id = list_printer (fun tnv fmt ->
          fprintf fmt "@ fr%s%t@ bnd%s%t" << id << tindex_printer tnv
            << id << tindex_printer tnv) v in
      fprintf fmt "%t%t@ lemma@ %t@ (t:%t)%t :@ unit@ %t\
        %trequires {@ %t%t@ t@]@ }@]@ \
        %tensures {@ %t%t@ t%t@]@ =@ %t%t@ t%t@]@ }@]@ \
        %tvariant {@ %t%t@ t@]@ }@]@ \
        =@ %t@]@\n@\n"
        indent pr << model_equal_lemma_name tn
        << nltype_app_printer b tn
        << list_printer (fun tnv fmt ->
            fprintf fmt "@ (fr1%t:%t)@ (fr2%t:%t)@ (bnd1%t:%t)@ (bnd2%t:%t)"
              << tindex_printer tnv
              << env_type_printer (fun fmt ->
                fprintf fmt "'b%t" << tindex_printer tnv) c tnv
              << tindex_printer tnv
              << env_type_printer (fun fmt ->
                fprintf fmt "'b%t" << tindex_printer tnv) c tnv
              << tindex_printer tnv << nlbenv_type_printer c tnv
              << tindex_printer tnv << nlbenv_type_printer c tnv) v
        << list_printer (fun tnv fmt ->
            fprintf fmt "%trequires {@ %tforall i:int.@ \
              0@ <=@ i@ <@ %t%t@ t@]@ ->@ \
              @ bnd1%t i@ =@ bnd2%t i@]@ }@]@ \
              %trequires {@ fr1%t@ =@ fr2%t@ }@]@ "
              << indent << indent << indent << bound_depth_name tnv tn
              << tindex_printer tnv << tindex_printer tnv
              << indent << tindex_printer tnv << tindex_printer tnv) v
        << indent << indent << correct_indexes_name tn
        << indent << indent << model_name tn << p "1"
        << indent << model_name tn << p "2"
        << indent << indent << nlsize_name tn
        << nlmatch_printer tn vcase vcase ccase (string_printer "t") in
    make_for_bdefs print_decl

  let bind_var_printer fmt =
    let pr = rec_val_printer () in
    let b = string_printer "b" in
    let print_decl tnv tn _ v =
      let fvcase = if tnv = tn
        then fun vname fmt ->
          fprintf fmt "%tif %t = x@ \
            then %t i@ \
            else %t %t@]" indent vname
            << bound_variable_name tn
            << free_variable_name tn << vname
        else fun vname fmt ->
          fprintf fmt "%t %t" << free_variable_name tn << vname in
      let bvcase vname fmt =
        fprintf fmt "%t %t" << bound_variable_name tn << vname in
      let ccase = nlrecons_case (fun vname blv tn fmt ->
        let v = binder_vars dm tn in
        if List.mem tnv v
        then fprintf fmt "%t%t@ %t@ x@ (i+%d)%t@]"
          indent << bind_var_name tnv tn
          << vname
          << level tnv blv
          << list_printer (fun tn fmt ->
            fprintf fmt "@ (%t)@ (%t)"
              << frenv_lift_printer (fun fmt ->
                fprintf fmt "fr%t" << tindex_printer tn) blv tn
              << benv_lift_printer (fun fmt ->
                fprintf fmt "bnd%t" << tindex_printer tn) blv tn) v
        else vname fmt) in
      let ccase cs v0 fmt =
        let v = flatten v0 in
        List.iter (fun (vn,blv,ty) -> match ty with
          | ITDecl tn' when List.mem tnv (binder_vars dm tn') ->
            let lv = level tnv blv in
            let p1 = frenv_lift_printer (fun fmt ->
              fprintf fmt "(%tupdate@ fr%t@ x@ (%tbnd%t@ i@])@])"
                << indent << tindex_printer tnv << indent << tindex_printer tnv)
              blv tnv in
            let p2 fmt = fprintf fmt "(%t%t@ (%tbnd%t@ i@])%t@])"
              << indent << rename_name tnv << indent << tindex_printer tnv
              << list_printer (fun tn fmt ->
                  fprintf fmt "@ %t" << csomes_printer (level tn blv)
                ) (binder_vars dm tnv) in
            let p3 p fmt = fprintf fmt "(%tupdate@ (%t)@ x@ %t@])"
              << indent << frenv_lift_printer (fun fmt ->
                fprintf fmt "fr%t" << tindex_printer tnv) blv tnv << p in
            let p4 fmt = fprintf fmt "(%teval@ (%t)@ (i+%d)@])"
              << indent << benv_lift_printer (fun fmt ->
                fprintf fmt "bnd%t" << tindex_printer tnv) blv tnv
              << lv in
            fprintf fmt "%tassert {@ %t@ =@ %t@ };@]@ \
              %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ };@]@ \
              %tassert {@ %t@ =@ %t@ };@]@ "
              << indent << p2 << p4
              << indent << indent << p1 << p3 p2
              << indent << p1 << p3 p4
          | _ -> ()
        ) v ;
        ccase cs v0 fmt in
      fprintf fmt "%t%t@ %t@ (t:%t)@ (x:%t)@ (i:int)%t :@ %t@ \
        %trequires {@ %t%t@ t@]@ }@]@ \
        %trequires {@ %t%t@ t@]@ <=@ i@ }@]@ \
        %tensures {@ %t%t@ result@]@ <= i + 1@ }@]@ \
        %tensures {@ %t%t@ result@]@ }@]@ %t\
        %tensures {@ %t%t@ result%t@]@ =@ %t%t@ t%t@]@ }@]@ \
        =@ %t@]@\n@\n"
        indent pr << bind_var_name tnv tn
          << nlrtype_app_printer tn
          << nlfree_var_type_name tn
          << list_printer (fun tn fmt ->
            fprintf fmt "@ (ghost fr%t:%t)@ (ghost bnd%t:%t)"
              << tindex_printer tn
              << env_type_printer (nlfree_var_type_name tn) b tn
              << tindex_printer tn << nlbenv_type_printer b tn) v
          << nlrtype_app_printer tn
          << indent << indent << correct_indexes_name tn
          << indent << indent << bound_depth_name tnv tn
          << indent << indent << bound_depth_name tnv tn
          << indent << indent << correct_indexes_name tn
          << list_printer (fun tnv2 fmt ->
              if tnv <> tnv2
              then fprintf fmt "%tensures {@ %t%t@ t@]@ =@ \
                %t%t@ result@]@ }@]@ "
                indent indent << bound_depth_name tnv2 tn
                << indent << bound_depth_name tnv2 tn) v
          << indent << indent << model_name tn << list_printer (fun tn fmt ->
              fprintf fmt "@ fr%t@ bnd%t" << tindex_printer tn
                << tindex_printer tn) v
          << indent << model_name tn << list_printer (fun tn fmt ->
            if tn = tnv
            then fprintf fmt "@ (%tupdate@ fr%t@ x@ (%tbnd%t@ i@])@])@ bnd%t"
              << indent << tindex_printer tn << indent << tindex_printer tn
              << tindex_printer tn
            else fprintf fmt "@ fr%t@ bnd%t" << tindex_printer tn
              << tindex_printer tn
            ) v
          << nlmatch_printer tn fvcase bvcase ccase (string_printer "t") in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)

  let unbind_var_printer fmt =
    let pr = rec_val_printer () in
    let b = string_printer "b" in
    let print_decl tnv tn _ v =
      let vv = binder_vars dm tnv in
      let fvcase vname fmt =
        fprintf fmt "%t%t@ %t@]" indent
          << free_variable_name tn << vname in
      let bvcase = if tn = tnv
        then fun vname fmt ->
          fprintf fmt "%tif %t = i@ \
            %tthen (%t%t@ x%t@] ;@ x)@]@ else %t %t@]" indent
              vname << indent << indent << model_equal_lemma_name tn
              << list_printer (fun tnv2 fmt ->
                let ti2 = tindex_printer tnv2 in
                fprintf fmt "@ fr%t@ fr%t@ bnd1%t@ bnd2%t" ti2 ti2 ti2 ti2) v
              << bound_variable_name tn << vname
        else fun vname fmt ->
          fprintf fmt "%t%t@ %t@]" indent
            << bound_variable_name tn << vname in
      let ccase = nlrecons_case (fun vname blv tn fmt ->
        let v = binder_vars dm tn in
        if List.mem tnv v
        then fprintf fmt "%t%t@ %t@ (i+%d)@ x%t%t@]" indent
          << unbind_var_name tnv tn << vname << level tnv blv
          << list_printer (fun tn fmt ->
              fprintf fmt "@ (%t)@ (%t)"
                << frenv_lift_printer (fun fmt ->
                  fprintf fmt "fr%t" << tindex_printer tn) blv tn
                << benv_lift_printer (fun fmt ->
                  fprintf fmt "bnd1%t" << tindex_printer tn) blv tn) v
          << list_printer (fun tn fmt ->
            fprintf fmt "@ (%t)"
              << frenv_lift_printer (fun fmt ->
                fprintf fmt "bnd2%t" << tindex_printer tn) blv tn) vv
        else vname fmt) in
      let ccase cs v0 fmt =
        let v = flatten v0 in
        List.iter (fun (vname,blv,ty) -> match ty with
          | ITVar _ -> ()
          | ITDecl tn -> let pm0 fmt =
              fprintf fmt "%t%t@ x%t@]" << indent << model_name tnv
              << list_printer (fun tn fmt ->
                  let ti = tindex_printer tn in
                  fprintf fmt "@ fr%t@ bnd2%t" ti ti) vv in
            let pm1 fmt =
              fprintf fmt "%t%t@ (%t)%t@]" indent << rename_name tnv << pm0
                << list_printer (fun tn fmt ->
                  fprintf fmt "@ %t" << csomes_printer (level tn blv)) vv in
            let pm2 fmt = fprintf fmt "%t%t@ x%t@]" indent << model_name tnv
              << list_printer (fun tn fmt ->
                let ti = tindex_printer tn in
                fprintf fmt "@ (%t)@ (%t)"
                  << frenv_lift_printer (fun fmt ->
                    fprintf fmt "fr%t" ti) blv tn
                  << frenv_lift_printer (fun fmt ->
                    fprintf fmt "bnd2%t" ti) blv tn) vv in
            let p1 = benv_lift_printer (fun fmt ->
                fprintf fmt "(%tupdate@ bnd1%t@ i@ (%t)@])"
                  indent << tindex_printer tnv << pm0
              ) blv tnv in
            let p2 pm fmt = fprintf fmt "%tupdate@ (%t)@ (i+%d)@ (%t)@]"
              indent << benv_lift_printer (fun fmt ->
                fprintf fmt "bnd1%t" << tindex_printer tnv) blv tnv
              << level tnv blv << pm in
            fprintf fmt "%tassert {@ %t@ =@ %t@ }@] ;@ \
              %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@] ;@ \
              %tassert {@ %t@ =@ %t@ }@] ;@ "
              indent pm1 pm2 indent indent p1 << p2 pm1
              << indent << p1 << p2 pm2
        ) v ;
        ccase cs v0 fmt in
      fprintf fmt "%t%t@ %t@ (t:%t)@ (i:int)@ (x:%t)%t%t :@ %t@ \
        %trequires {@ i@ >=@ 0@ }@]@ \
        %trequires {@ %t%t@ t@]@ }@]@ \
        %trequires {@ %t%t@ t@]@ <=@ i + 1@ }@]@ \
        %trequires {@ %t%t@ x@]@ }@]@ %t\
        %tensures {@ %t%t@ result@]@ }@]@ \
        %tensures {@ %t%t@ result@]@ <=@ i@ }@]@ %t\
        %tensures {@ %t%t@ result%t@]@ =@ %t%t@ t%t@]@ }@]@ \
        =@ %t@]@\n@\n"
        indent pr << unbind_var_name tnv tn << nlrtype_app_printer tn
        << nlrtype_app_printer tnv
        << list_printer (fun tn fmt ->
            fprintf fmt "@ (ghost fr%t:%t)@ (ghost bnd1%t:%t)"
              << tindex_printer tn
              << env_type_printer (nlfree_var_type_name tn) b tn
              << tindex_printer tn << nlbenv_type_printer b tn) v
        << list_printer (fun tn fmt ->
            fprintf fmt "@ (ghost bnd2%t:%t)"
              << tindex_printer tn << nlbenv_type_printer b tn) vv
        << nlrtype_app_printer tn
        << indent << indent << indent << correct_indexes_name tn
        << indent << indent << bound_depth_name tnv tn
        << indent << indent << correct_indexes_name tnv
        << list_printer (fun tnv2 fmt ->
          fprintf fmt "%trequires {@ %t%t@ x@]@ =@ 0@ }@]@ "
            indent indent << bound_depth_name tnv2 tnv) vv
        << indent << indent << correct_indexes_name tn
        << indent << indent << bound_depth_name tnv tn
        << list_printer (fun tnv2 fmt ->
          if tnv <> tnv2
          then fprintf fmt "%tensures {@ %t%t@ result@]@ =@ %t%t@ t@]@ }@]@ "
            indent indent << bound_depth_name tnv2 tn
            << indent << bound_depth_name tnv2 tn) v
        << indent << indent << model_name tn << list_printer (fun tn fmt ->
          fprintf fmt "@ fr%t@ bnd1%t"
            << tindex_printer tn << tindex_printer tn) v
        << indent << model_name tn << list_printer (fun tn fmt ->
          if tn = tnv
          then fprintf fmt "@ fr%t@ (%tupdate@ bnd1%t@ i@ (%t%t@ x%t@])@])"
            << tindex_printer tn << indent << tindex_printer tn
            << indent << model_name tnv << list_printer (fun tn fmt ->
              fprintf fmt "@ fr%t@ bnd2%t"
                << tindex_printer tn << tindex_printer tn) vv
          else fprintf fmt "@ fr%t@ bnd1%t"
            << tindex_printer tn << tindex_printer tn) v
        << nlmatch_printer tn fvcase bvcase ccase (string_printer "t") in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)


  let subst_base_printer fmt =
    let pr = rec_val_printer () in
    let b = string_printer "b" in
    let print_decl tnv tn _ v =
      let vv = binder_vars dm tnv in
      let fvcase =
        if tn = tnv
        then fun vname fmt ->
          fprintf fmt "%tif %t = x@ \
            %tthen (%t%t@ u%t@] ;@ u)@]@ else %t %t@]" indent
              vname indent indent << model_equal_lemma_name tn
              << list_printer (fun tnv2 fmt ->
                let ti2 = tindex_printer tnv2 in
                fprintf fmt "@ fr%t@ fr%t@ bnd1%t@ bnd2%t" ti2 ti2 ti2 ti2) v
              << free_variable_name tn << vname
        else fun vname fmt ->
          fprintf fmt "%t%t@ %t@]" indent
            << free_variable_name tn << vname in
      let bvcase vname fmt =
        fprintf fmt "%t%t@ %t@]" indent
          << bound_variable_name tn << vname in
      let ccase = nlrecons_case (fun vname blv tn fmt ->
        let v = binder_vars dm tn in
        if List.mem tnv v
        then fprintf fmt "%t%t@ %t@ x@ u%t%t@]" indent
          << subst_base_name tnv tn << vname
          << list_printer (fun tn fmt ->
              fprintf fmt "@ (%t)@ (%t)"
                << frenv_lift_printer (fun fmt ->
                  fprintf fmt "fr%t" << tindex_printer tn) blv tn
                << benv_lift_printer (fun fmt ->
                  fprintf fmt "bnd1%t" << tindex_printer tn) blv tn) v
          << list_printer (fun tn fmt ->
            fprintf fmt "@ (%t)"
              << frenv_lift_printer (fun fmt ->
                fprintf fmt "bnd2%t" << tindex_printer tn) blv tn) vv
        else vname fmt) in
      let ccase cs v0 fmt =
        let v = flatten v0 in
        List.iter (fun (vname,blv,ty) -> match ty with
          | ITVar _ -> ()
          | ITDecl tn -> let pm0 fmt =
              fprintf fmt "%t%t@ u%t@]" << indent << model_name tnv
              << list_printer (fun tn fmt ->
                  let ti = tindex_printer tn in
                  fprintf fmt "@ fr%t@ bnd2%t" ti ti) vv in
            let pm1 fmt =
              fprintf fmt "%t%t@ (%t)%t@]" indent << rename_name tnv << pm0
                << list_printer (fun tn fmt ->
                  fprintf fmt "@ %t" << csomes_printer (level tn blv)) vv in
            let pm2 fmt = fprintf fmt "%t%t@ u%t@]" indent << model_name tnv
              << list_printer (fun tn fmt ->
                let ti = tindex_printer tn in
                fprintf fmt "@ (%t)@ (%t)"
                  << frenv_lift_printer (fun fmt ->
                    fprintf fmt "fr%t" ti) blv tn
                  << frenv_lift_printer (fun fmt ->
                    fprintf fmt "bnd2%t" ti) blv tn) vv in
            let p1 = frenv_lift_printer (fun fmt ->
                fprintf fmt "(%tupdate@ fr%t@ x@ (%t)@])"
                  indent << tindex_printer tnv << pm0
              ) blv tnv in
            let p2 pm fmt = fprintf fmt "%tupdate@ (%t)@ x@ (%t)@]"
              indent << frenv_lift_printer (fun fmt ->
                fprintf fmt "fr%t" << tindex_printer tnv) blv tnv
              << pm in
            fprintf fmt "%tassert {@ %t@ =@ %t@ }@] ;@ \
              %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@] ;@ \
              %tassert {@ %t@ =@ %t@ }@] ;@ "
              indent pm1 pm2 indent indent p1 << p2 pm1
              << indent << p1 << p2 pm2
        ) v ;
        ccase cs v0 fmt in
      fprintf fmt "%t%t@ %t@ (t:%t)@ (x:int)@ (u:%t)%t%t :@ %t@ \
        %trequires {@ %t%t@ t@]@ }@]@ \
        %trequires {@ %t%t@ u@]@ }@]@ %t\
        %tensures {@ %t%t@ result@]@ }@]@  %t\
        %tensures {@ %t%t@ result%t@]@ =@ %t%t@ t%t@]@ }@]@ \
        =@ %t@]@\n@\n"
        indent pr << subst_base_name tnv tn << nlrtype_app_printer tn
        << nlrtype_app_printer tnv
        << list_printer (fun tn fmt ->
            fprintf fmt "@ (ghost fr%t:%t)@ (ghost bnd1%t:%t)"
              << tindex_printer tn
              << env_type_printer (nlfree_var_type_name tn) b tn
              << tindex_printer tn << nlbenv_type_printer b tn) v
        << list_printer (fun tn fmt ->
            fprintf fmt "@ (ghost bnd2%t:%t)"
              << tindex_printer tn << nlbenv_type_printer b tn) vv
        << nlrtype_app_printer tn
        << indent << indent << correct_indexes_name tn
        << indent << indent << correct_indexes_name tnv
        << list_printer (fun tnv2 fmt ->
          fprintf fmt "%trequires {@ %t%t@ u@]@ =@ 0@ }@]@ "
            indent indent << bound_depth_name tnv2 tnv) vv
        << indent << indent << correct_indexes_name tn
        << list_printer (fun tnv2 fmt ->
          fprintf fmt "%tensures {@ %t%t@ result@]@ =@ %t%t@ t@]@ }@]@ "
            indent indent << bound_depth_name tnv2 tn
            << indent << bound_depth_name tnv2 tn) v
        << indent << indent << model_name tn << list_printer (fun tn fmt ->
          fprintf fmt "@ fr%t@ bnd1%t"
            << tindex_printer tn << tindex_printer tn) v
        << indent << model_name tn << list_printer (fun tn fmt ->
          if tn = tnv
          then fprintf fmt "@ (%tupdate@ fr%t@ x@ (%t%t@ u%t@])@])@ bnd1%t"
            << indent << tindex_printer tn << indent << model_name tnv
            << list_printer (fun tn fmt ->
              fprintf fmt "@ fr%t@ bnd2%t"
                << tindex_printer tn << tindex_printer tn) vv
            << tindex_printer tn
          else fprintf fmt "@ fr%t@ bnd1%t"
            << tindex_printer tn << tindex_printer tn) v
        << nlmatch_printer tn fvcase bvcase ccase (string_printer "t") in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)




  let implementation_type_printer fmt =
    let print_decl tn _ v =
      fprintf fmt "%ttype@ %t%t@ =@ %t{@ \
        %t%t :@ %t ;@]%t@ \
        %tghost@ %t :@ %t%s%t%t@] ;@]@]@ }@]@\n@\n"
        indent << impl_type_name tn << params_printer
        << indent << indent << data_field_name tn
        << nlrtype_app_printer tn << list_printer (fun tnv fmt ->
          fprintf fmt "@ %t%t :@ %t ;@]"
            indent << varset_field_name tnv tn << varset_type_name tnv) v
        << indent << model_field_name tn << indent
        << type_name dm tn << params_printer
        << list_printer (fun tn fmt ->
          fprintf fmt "@ %t" << nlfree_var_type_name tn) v
    in
    make_for_defs print_decl

  let invariant_printer fmt =
    let print_decl tn _ v =
      let correct_indexes fmt = match v with
        | [] -> ()
        | _ -> fprintf fmt "@ /\\@ %t%t@ t.%t@]"
          << indent << correct_indexes_name tn << data_field_name tn in
      fprintf fmt "%tpredicate@ %t@ (t:%t%t%t@])@ =@ \
        %t%t%t@ t.%t%t@]@ =@ t.%t@]\
        %t%t%t@]@\n@\n"
        indent << invariant_name tn << indent << impl_type_name tn
        << params_printer << indent << indent << model_name tn
        << data_field_name tn << list_printer (fun tn fmt ->
          fprintf fmt "@ %t@ (%tconst@ (%t%t@ (%t)@])@])"
            << subst_identity_name tn << indent
            << indent << variable_name tn << default_variable_value tn) v
        << model_field_name tn
        << correct_indexes
        << list_printer (fun tnv fmt ->
          fprintf fmt "@ /\\@ %t%t%t@ t.%t@]@ =@ 0@]"
            indent indent << bound_depth_name tnv tn
            << data_field_name tn) v
        << list_printer (fun tnv fmt ->
          fprintf fmt "@ /\\@ (%tforall@ x:%t.@ %t%t@ x@ t.%t@]@ ->@ %t@])"
            << indent << nlfree_var_type_name tn << indent
            << free_var_predicate_name tnv tn << model_field_name tn
            << free_var_in_set_predicate tnv (string_printer "x") (fun fmt ->
              fprintf fmt "t.%t" << varset_field_name tnv tn)) v
    in
    make_for_defs print_decl

  (* Time to go for explicit construction/destruction ! *)

  let constructor_type_printer fmt =
    let print_decl tn c v =
      fprintf fmt "%ttype@ %t%t@ =" indent << constructor_type_name tn
        << params_printer ;
      (if c.var_present
       then fprintf fmt "@ %t| %t@ %t@]" indent << constructor_variable_name tn
         << nlfree_var_type_name tn) ;
      let pf = list_printer (fun ty fmt -> match ty with
        | ITVar vname -> fprintf fmt "@ 'a%s" << var_name dm vname
        | ITDecl tn -> fprintf fmt "@ (%t%t%t@])"
          indent << impl_type_name tn << params_printer) in
      fprintf fmt "%t@]@\n@\n" << list_printer (fun (cn,bl,tl) fmt ->
        fprintf fmt "@ %t| %t%t%t@]" indent << constructor_cons_name cn
          << list_printer (fun (tn,tl) fmt ->
            fprintf fmt "@ (%t)%t" << nlfree_var_type_name tn
              << pf tl) bl << pf tl
      ) c.cons_list in
    make_for_defs print_decl

  let env_list tn elv = try TMap.find tn elv with Not_found -> []

  let add_to_env tn vp elv =
    TMap.add tn (vp::env_list tn elv) elv

  let cons_match_variables ?(vbase=string_printer "v") (cn,bl,tl) =
    let process_type blevels elv (vars,cnt) ty =
      let vprinter fmt = fprintf fmt "%t%d" vbase cnt in
      ((vprinter,blevels,elv,ty)::vars,cnt+1) in
    let process_types blevels elv = List.fold_left (process_type blevels elv) in
    let (vars,blevels,elv,cnt) =
      List.fold_left (fun (vars,blevels,elv,cnt) (bo,tys) ->
        let nblevels = inc_level bo blevels in
        let vprinter fmt = fprintf fmt "%t%d" vbase cnt in
        let nelv = add_to_env bo vprinter elv in
        let ivars,cnt = process_types blevels elv ([],cnt+1) tys in
        ((vprinter,blevels,bo,elv,List.rev ivars)::vars,nblevels,nelv,cnt)
      ) ( [] , TMap.empty , TMap.empty , 0 ) bl in
    let (ivars,_) = process_types blevels elv ([],cnt) tl in
    List.rev vars,List.rev ivars

  let cons_match_printer tn vcase ccase v fmt =
    let c = match type_def dm tn with
      | ITypeDef (c,_) -> c
      | _ -> assert false in
    fprintf fmt "%tmatch %t with" indent v ;
    (if c.var_present
     then fprintf fmt "@ %t| %t@ v0@ ->@ %t@]"
       indent << constructor_variable_name tn
       << vcase (string_printer "v0"));
    fprintf fmt "%t@]@ end"
      << list_printer (fun ((cn,_,_) as cs) fmt ->
        let bl,tl = cons_match_variables cs in
        let p (vp,_,_,_) fmt = fprintf fmt "@ %t" vp in
        let p = list_printer p in
        fprintf fmt "@ %t| %t%t%t%t@]@ ->@ %t@]"
          indent indent << constructor_cons_name cn
          << list_printer (fun (vp,_,_,_,tl) fmt ->
            fprintf fmt "@ %t%t" vp << p tl) bl
          << p tl << ccase cs bl tl) c.cons_list

  let constructor_invariant_printer fmt =
    let print_decl tn _ v =
      let vcase _ fmt = fprintf fmt "true" in
      let ccase _ bl tl fmt =
        let printed = ref false in
        let p (vp,_,_,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn -> (if !printed
            then fprintf fmt "@ /\\@ "
            else printed := true);
            fprintf fmt "%t%t@ %t@]" indent << invariant_name tn
              << vp in
        let p = list_printer p in
        fprintf fmt "%t%t" << list_printer (fun (_,_,_,_,tl) -> p tl) bl
          << p tl ;
        if not(!printed)
        then fprintf fmt "true" in
      fprintf fmt "%tpredicate@ %t@ (c:%t%t%t@])@ =@ %t@]@\n@\n"
        indent << constructor_invariant_name tn
        << indent << constructor_type_name tn << params_printer
        << cons_match_printer tn vcase ccase (string_printer "c") in
    make_for_defs print_decl

  let closure_renaming tn blv elv fmt =
    let l = env_list tn elv in
    (*let lv = level tn blv in*)
    let rec aux n l fmt = match l with
      | [] -> csomes_printer n fmt
      | vp :: l -> fprintf fmt "(%tupdate@ %t@ %t@ %t@])"
        indent << aux (n+1) l << vp
        << somes_printer (string_printer "None") n in
    aux 0 l fmt

  let open_renaming tn elv fmt =
    let l = env_list tn elv in
    let rec aux l fmt = match l with
      | [] -> fprintf fmt "identity"
      | vp :: l -> fprintf fmt "(%tocase@ %t@ %t@])"
        indent << aux l << vp in
    aux l fmt

  let constructor_relation_printer fmt =
    let print_decl tn _ v =
      let vcase vname fmt = fprintf fmt "t.%t@ =@ %t%t@ %t@]"
        << model_field_name tn << indent << variable_name tn
        << vname in
      let ccase (cn,_,_) bl tl fmt =
        let p (vp,blv,elv,ty) fmt = match ty with
          | ITVar _ -> fprintf fmt "@ %t" vp
          | ITDecl tn -> let v = binder_vars dm tn in
            match v with
              | [] -> fprintf fmt "@ %t.%t" vp << model_field_name tn
              | _ -> fprintf fmt "@ (%t%t@ %t.%t%t@])"
                << indent << rename_name tn << vp << model_field_name tn
                << list_printer (fun tnv fmt ->
                    fprintf fmt "@ %t" << closure_renaming tnv blv elv
                  ) v in
        let p = list_printer p in
        fprintf fmt "t.%t@ =@ %t%s%t%t@]"
          << model_field_name tn << indent << cons_name dm cn
          << list_printer (fun (_,_,_,_,tl) -> p tl) bl
          << p tl
      in
      fprintf fmt "%tpredicate@ %t@ (c:%t%t%t@])@ (t:%t%t%t@])@ =@ %t@]@\n@\n"
        indent << constructor_relation_name tn << indent
        << constructor_type_name tn << params_printer << indent
        << impl_type_name tn << params_printer
        << cons_match_printer tn vcase ccase (string_printer "c") in
    make_for_defs print_decl

  let constructor_open_relation_printer fmt =
    let print_decl tn _ v =
      let vcase vname fmt = fprintf fmt "t.%t@ =@ %t%t@ %t@]"
        << model_field_name tn << indent << variable_name tn
        << vname in
      let ccase (cn,_,_) bl tl (cn2,_,_) vars fmt =
        if cn = cn2
        then let printed = ref false in
          let conj fmt = if !printed
            then fprintf fmt "@ /\\@ "
            else printed := true in
          let rec zip acc tl vars = match tl,vars with
            | [] , vars -> List.rev acc , vars
            | _ , [] -> assert false
            | (vp,blv,elv,ty) :: tl, (mvp,_,_) :: vars ->
              zip ((vp,mvp,blv,elv,ty) :: acc) tl vars in
          let rec zipb acc bl vars = match bl with
            | [] -> List.rev acc , let tl , _ = zip [] tl vars in tl
            | (vp,blv,bo,elv,tl) :: bl ->
              let tl,vars = zip [] tl vars in
              zipb ((vp,blv,bo,elv,tl)::acc) bl vars in
          let bl,tl = zipb [] bl vars in
          let p (vp,mvp,blv,elv,ty) fmt = match ty with
            | ITVar _ -> fprintf fmt "%t%t%t@ =@ %t@]" conj indent vp mvp
            | ITDecl tn -> let v = binder_vars dm tn in match v with
              | [] -> fprintf fmt "%t%t%t.%t@ =@ %t@]"
                conj indent vp << model_field_name tn << mvp
              | _ -> fprintf fmt "%t%t%t.%t@ =@ (%t%t@ %t%t@])@]"
                conj indent vp << model_field_name tn << indent
                << rename_name tn << mvp << list_printer (fun tnv fmt ->
                    fprintf fmt "@ %t" << open_renaming tnv elv
                  ) v in
          let p = list_printer p in
          List.iter (fun (_,_,_,_,tl) -> p tl fmt) bl ;
          p tl fmt ;
          (if not(!printed)
          then fprintf fmt "true")
        else fprintf fmt "false" in
      let ccase cs bl tl =
        let vbase = string_printer "w" in
        match_printer ~vbase tn (fun _ fmt ->
          fprintf fmt "false") (ccase cs bl tl) (fun fmt ->
          fprintf fmt "t.%t" << model_field_name tn) in
      fprintf fmt "%tpredicate@ %t@ (c:%t%t%t@])@ (t:%t%t%t@])@ =@ %t@]@\n@\n"
        indent << constructor_open_relation_name tn << indent
        << constructor_type_name tn << params_printer << indent
        << impl_type_name tn << params_printer
        << cons_match_printer tn vcase ccase (string_printer "c") in
    make_for_defs print_decl

  let construction_operator_printer fmt =
    let print_decl tn _ v =
      let vcase vname fmt =
        fprintf fmt "%t{@ \
          %t%t@ =@ %t%t@ %t@] ;@]%t@ \
          %t%t@ =@ ghost@ (%t%t@ %t@]) ;@]@]@ }"
          indent indent << data_field_name tn << indent
          << free_variable_name tn << vname << list_printer (fun tnv fmt ->
            fprintf fmt "@ %t%t@ =@ %t ;@]"
              indent << varset_field_name tnv tn
              << (if tn = tnv
                then varset_singleton tnv vname
                else varset_empty tnv)) v
          << indent << model_field_name tn << indent
          << variable_name tn << vname in
      let ccase (cn,_,_) bl tl fmt =
        let nextup up tnvp bvp n tn fmt =
          if tnvp = tn
          then fprintf fmt "(%tupdate@ %t@ %t@ (%t%t@ %t@])@])"
            indent << up tn << bvp << indent << variable_name tn
            << somes_printer (string_printer "None") n
          else up tn fmt in
        let bbase blv tn fmt =
          benv_lift_printer (fun fmt ->
            fprintf fmt "(%tconst@ (%t%t@ %t@])@])"
              indent indent << variable_name tn << default_variable_value tn)
          blv tn fmt in
        let upd blv tn fmt =
          fprintf fmt "(%t%t@ (%t:(%t)->(%t%s%t%t@]))%t@])" indent
            << rename_subst_name tn
            << subst_identity_name tn << nlfree_var_type_name tn
            << indent << type_name dm tn
            << params_printer << list_printer (fun tnv fmt ->
              fprintf fmt "@ (%t)" << nlfree_var_type_name tnv
            ) (binder_vars dm tn)
            << list_printer (fun tnv fmt ->
              fprintf fmt "@ %t" << csomes_printer (level tnv blv)
            ) (binder_vars dm tn)
        in
        let print_nl_element (vp,blv,elv,ty) fmt = match ty with
          | ITVar _ -> fprintf fmt "@ %t" vp
          | ITDecl tn ->
            fprintf fmt "@ (%t%tlet@ %t@ =@ %t.%t@]@ in@ " indent indent vp vp
              << data_field_name tn ;
              let update_list = TMap.fold (fun tnv l acc ->
                let l,_ = List.fold_left (fun (acc,n) bvp ->
                  (bvp,tnv,n)::acc,n+1) ([],0) l in
                List.append l acc) elv [] in
              let update_list,_ = List.fold_left (fun (acc,up) (bvp,tnv,n) ->
                  let nup = nextup up tnv bvp n in
                  (bvp,tnv,n,up)::acc,nup) ([],upd blv) update_list in
              List.iter (fun (bvp,tnv,n,up) ->
                fprintf fmt "%tlet@ %t@ =@ %t%t@ %t@ %t@ %d%t@]@]@ in@ "
                  indent vp indent << bind_var_name tnv tn << vp << bvp << n
                  << list_printer (fun tnv2 fmt ->
                      fprintf fmt "@ (%tghost@ %t@])@ \
                        (%tghost@ %t@])"
                        << indent << up tnv2 << indent << bbase blv tnv2
                  ) (binder_vars dm tn) ;
              ) update_list ;
              fprintf fmt "%t@])" vp in
        let print_nl_elements tl fmt = list_printer print_nl_element tl fmt in
        let print_nl_elements fmt =
          fprintf fmt "%t%t"
            << list_printer (fun (_,_,_,_,tl) fmt ->
              print_nl_elements tl fmt) bl
            << print_nl_elements tl in

        let print_renaming vp blv elv tn fmt =
          fprintf fmt "(%t%t@ %t.%t%t@])" indent
            << rename_name tn << vp << model_field_name tn
            << list_printer (fun tn fmt ->
                fprintf fmt "@ %t" << closure_renaming tn blv elv
              ) (binder_vars dm tn) in
        let print_l_element (vp,blv,elv,ty) fmt = match ty with
          | ITVar _ -> fprintf fmt "@ %t" vp
          | ITDecl tn -> let v = binder_vars dm tn in
            match v with
              | [] -> fprintf fmt "@ %t" vp
              | _ -> fprintf fmt "@ %t" << print_renaming vp blv elv tn in
        let print_l_elements tl fmt =
          list_printer print_l_element tl fmt in
        let print_l_elements fmt =
          fprintf fmt "%t%t"
            << list_printer (fun (_,_,_,_,tl) fmt -> print_l_elements tl fmt) bl
            << print_l_elements tl in

        let rec print_join tnv a l = match l with
          | [] -> a
          | (vp,_,_,ty) :: l -> match ty with
            | ITVar _ -> print_join tnv a l
            | ITDecl tn2 -> if List.mem tnv (binder_vars dm tn2)
              then let p fmt = fprintf fmt "%t.%t" vp
                << varset_field_name tnv tn2 in
                match a with None -> print_join tnv (Some p) l
                  | Some a -> print_join tnv (Some (varset_join tnv a p)) l
              else print_join tnv a l in
        let print_join tnv fmt =
          let a = List.fold_left (fun acc (_,_,_,_,tl) ->
            print_join tnv acc tl) None bl in
          match print_join tnv a tl with
            | None -> varset_empty tnv fmt
            | Some a -> a fmt in

        let print_fv_assertion vp blv elv tnv tn2 fmt =
          fprintf fmt "%tassert {@ %tforall@ x:%t.@ \
            %t%t@ %t@ %t@]@ ->@ (%tforall@ y:%t.@ \
            (%t%t@ y@ %t.%t@]@ /\\@ %teval@ (%t)@ y@ =@ %t@])@ ->@ \
            %t%t%t@ =@ %teval@ (%t)@ y@]@]@ &&@ %tx@ =@ y@]@ &&@ \
            %t%t@ x@ %t.%t@]@])@ &&@ %t%t@ x@ %t.%t@]@ \
            &&@ %t@ &&@ %t@]@ }@] ;@ "
            indent indent << nlfree_var_type_name tnv
            << indent << free_var_predicate_name tnv tn2
            << somes_printer (string_printer "x") (level tnv blv)
            << print_renaming vp blv elv tn2
            << indent << nlfree_var_type_name tnv
            << indent << free_var_predicate_name tnv tn2 << vp
            << model_field_name tn2 << indent << closure_renaming tnv blv elv
            << somes_printer (string_printer "x") (level tnv blv)
            << list_printer (fun vp2 fmt ->
                fprintf fmt "%ty@ <>@ %t@]@ &&@ " indent vp2
              ) (env_list tnv elv)
            << indent << somes_printer (string_printer "x") (level tnv blv)
            << indent << csomes_printer (level tnv blv)
            << indent << indent << free_var_predicate_name tnv tn2 << vp
            << model_field_name tn2
            << indent << free_var_predicate_name tnv tn2 << vp
            << model_field_name tn2
            << free_var_in_set_predicate tnv (string_printer "x") (fun fmt ->
              fprintf fmt "%t.%t" vp << varset_field_name tnv tn2)
            << free_var_in_set_predicate tnv (string_printer "x") (fun fmt ->
              fprintf fmt "res.%t" << varset_field_name tnv tn) in
        let print_fv_assertion (vp,blv,elv,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn -> list_printer (fun tnv fmt ->
            print_fv_assertion vp blv elv tnv tn fmt) (binder_vars dm tn) fmt in
        let print_fv_assertion tl fmt =
          list_printer print_fv_assertion tl fmt in
        let print_fv_assertion fmt =
          fprintf fmt "%t%t%t"
            << list_printer (fun (_,_,_,_,tl) fmt ->
              print_fv_assertion tl fmt) bl
            << print_fv_assertion tl
            << list_printer (fun tnv fmt ->
              let disj = ref false in
              let pdisj fmt = if !disj
                then fprintf fmt "@ \\/@ "
                else disj := true in
              let pvar (vp,blv,elv,ty) fmt = match ty with
                | ITDecl tn2 when List.mem tnv (binder_vars dm tn2) ->
                  fprintf fmt "%t%t%t@ %t@ %t@]"
                    pdisj indent << free_var_predicate_name tnv tn2
                    << somes_printer (string_printer "x") (level tnv blv)
                    << print_renaming vp blv elv tn2
                | _ -> () in
              let pvar tl fmt = list_printer pvar tl fmt in
              fprintf fmt "%tassert {@ %tforall@ x:%t.@ \
                %t%t@ x@ res.%t@]@ ->@ \
                (%t%t%t%t@])@ &&@ %t@]@ }@] ;@ "
                indent indent << nlfree_var_type_name tnv << indent
                << free_var_predicate_name tnv tn << model_field_name tn
                << indent << list_printer (fun (_,_,_,_,tl) fmt ->
                  pvar tl fmt) bl
                << pvar tl << (fun fmt -> if not(!disj)
                  then fprintf fmt "false")
                << free_var_in_set_predicate tnv (string_printer "x")
                  (fun fmt -> fprintf fmt "res.%t" << varset_field_name tnv tn)
            ) v
        in

        let print_model_assertion vp blv elv tn2 fmt =
          let update_list = TMap.fold (fun tnv l acc ->
              let l,_ = List.fold_left (fun (acc,n) bvp ->
                (bvp,tnv,n)::acc,n+1) ([],0) l in
              List.append l acc) elv [] in
          let updt = List.fold_left (fun up (bvp,tnv,n) ->
            nextup up tnv bvp n) (upd blv) update_list in
          let p1 tnv fmt =
            fprintf fmt "%t%t@ %t%t@]"
              indent << rename_subst_name tnv << subst_identity_name tnv
              << list_printer (fun tnv2 fmt ->
                fprintf fmt "@ %t" << closure_renaming tnv2 blv elv
              ) (binder_vars dm tnv) in
          let p2 tnv fmt =
            fprintf fmt "%trcompose@ (%t)@ (%t)@]" indent
              << closure_renaming tnv blv elv
              << open_renaming tnv elv in
          let p3 tnv fmt = fprintf fmt "(%tidentity :@ %t(%t)@ -> (%t)@]@])"
            indent indent << nlfree_var_type_name tnv
            << nlfree_var_type_name tnv in
          List.iter (fun tnv ->
            fprintf fmt "%tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@] ;@ \
              %tassert {@ %t@ =@ %t@ }@] ;@ "
              indent indent << p1 tnv << updt tnv
              << indent << p1 tnv << updt tnv
            ) (binder_vars dm tn2) ;
          fprintf fmt "%t%t@ %t.%t%t@] ;@ %t"
            indent << model_equal_lemma_name tn2 << vp << data_field_name tn2
            << list_printer (fun tnv fmt ->
              fprintf fmt "@ (%t)@ (%t)@ (%t)@ \
                (%t%t@ (%tconst@ (%t%t@ %t@])@])%t@])"
                << p1 tnv << p1 tnv << bbase blv tnv
                << indent << rename_subst_name tnv
                << indent << indent << variable_name tnv
                << default_variable_value tnv << list_printer (fun tnv2 fmt ->
                  fprintf fmt "@ %t" << closure_renaming tnv2 blv elv
                ) (binder_vars dm tnv)
            ) (binder_vars dm tn2)
            << list_printer (fun tnv fmt ->
              fprintf fmt "(*%tassert {@ %textensionalEqual@ \
                (%t)@ (%t)@]@ }@] ;@ \
                %tassert {@ %t@ =@ %t@ }@] ;*)@ "
                << indent << indent << p2 tnv << p3 tnv
                << indent << p2 tnv << p3 tnv
            ) (binder_vars dm tn2) in
        let print_model_assertion (vp,blv,elv,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn2 -> print_model_assertion vp blv elv tn2 fmt in
        let print_model_assertion tl fmt =
          list_printer print_model_assertion tl fmt in
        let print_model_assertion fmt =
          fprintf fmt "%t%t"
            << list_printer (fun (_,_,_,_,tl) fmt ->
              print_model_assertion tl fmt) bl
            << print_model_assertion tl in

        let print_ok_assertion (vp,blv,elv,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn ->
            fprintf fmt "%tassert {@ %t%t@ %t@]@ }@] ;@ "
              indent indent << invariant_name tn << vp in
        let print_ok_assertion tl fmt =
          list_printer print_ok_assertion tl fmt in
        let print_ok_assertion fmt =
          fprintf fmt "%t%t"
            << list_printer (fun (_,_,_,_,tl) fmt ->
              print_ok_assertion tl fmt) bl
            << print_ok_assertion tl in

        fprintf fmt "%t%tlet@ res@ =@ %t{@ \
          %t%t@ =@ (%t%t%t@]) ;@]%t@ \
          %t%t@ =@ ghost@ (%t%s%t@]) ;@]@]@ }@]@ in@ %t%tres"
          << print_ok_assertion
          << indent << indent << indent << data_field_name tn
          << indent << nlcons_name cn << print_nl_elements
          << list_printer (fun tnv fmt ->
            fprintf fmt "@ %t%t@ =@ %t ;@]"
              indent << varset_field_name tnv tn
              << print_join tnv
            ) v
          << indent << model_field_name tn << indent
          << cons_name dm cn
          << print_l_elements
          << print_fv_assertion
          << print_model_assertion in

      fprintf fmt "%tlet@ %t@ (c:%t%t%t@]) :@ %t%t%t@]@ \
        %trequires {@ %t%t@ c@]@ }@]@ \
        %tensures {@ %t%t@ result@]@ }@]@ \
        %tensures {@ %t%t@ c@ result@]@ }@]@ \
        (*%tensures {@ %t%t@ c@ result@]@ }@]*)@ \
        =@ %t@]@\n@\n"
        indent << construction_operator_name tn << indent
        << constructor_type_name tn << params_printer
        << indent << impl_type_name tn << params_printer
        << indent << indent << constructor_invariant_name tn
        << indent << indent << invariant_name tn
        << indent << indent << constructor_relation_name tn
        << indent << indent << constructor_open_relation_name tn
        << cons_match_printer tn vcase ccase (string_printer "c") in
    make_for_defs print_decl

  let destruction_operator_printer fmt =
    let print_decl tn _ v =
      let bvcase _ fmt = fprintf fmt "absurd" in
      let fvcase vname fmt =
        fprintf fmt "%t@ %t" << constructor_variable_name tn << vname in
      let ccase (cn,_,_) (bvars,(blvf,vf)) fmt =
        (* Update utility. *)
        let upd tn fmt =
          fprintf fmt "(%tconst@ (%t%t@ %t@]) :@ %tint@ -> (%t%s%t%t@])@]@])"
            indent indent << variable_name tn << default_variable_value tn
            << indent << indent << type_name dm tn << params_printer
            << list_printer (fun tnv fmt ->
                fprintf fmt "@ %t" << nlfree_var_type_name tnv
              ) (binder_vars dm tn) in
        let nextup up tnvp bvp n tn fmt =
          if tn = tnvp
          then fprintf fmt "(%tupdate@ %t@ %d@ (%t%t@ %t@])@])"
            indent << up tn << n << indent << variable_name tn << bvp
          else up tn fmt in
        (* generate fresh variables. *)
        let bvars,elvf,_ = List.fold_left (fun (vars,elv,cnt) (blv,bo,vrs) ->
          let wp fmt = fprintf fmt "w%d" cnt in
          fprintf fmt "%tlet@ %t@ =@ %t@]@ in@ \
            %tlet@ fv%t@ =@ %t@]@ in@ " indent wp << varset_fresh bo (fun fmt ->
              fprintf fmt "fv%t" << tindex_printer bo)
            << indent << tindex_printer bo << varset_add bo wp (fun fmt ->
              fprintf fmt "fv%t" << tindex_printer bo) ;
          ((blv,elv,wp,bo,vrs)::vars,add_to_env bo wp elv,cnt+1)
        ) ([],TMap.empty,0) bvars in
        let bvars = List.rev bvars in
        (* Done generation. Inverse the model. *)
        let comma = ref false in
        let pcomma fmt = if !comma
          then fprintf fmt " ,@ "
          else comma := true in
        let pv (vp,_) fmt = fprintf fmt "%tm%t" pcomma vp in
        let pv l fmt = list_printer pv l fmt in
        let mvcase _ fmt = fprintf fmt "absurd" in
        let mccase (cn2,_,_) v fmt = if cn = cn2
          then let _ = comma := false in
            fprintf fmt "(%t%t@])" indent
              << list_printer (fun (vp,_,_) fmt ->
                fprintf fmt "%t%t" pcomma vp) v
          else fprintf fmt "absurd" in
        let vbase = string_printer "x" in
        let pva blv (vp,ty) fmt = match ty with
          | ITVar _ -> fprintf fmt "@ %t" vp
          | ITDecl tn -> fprintf fmt "@ (%t%t@ %t%t@])"
            indent << model_name tn << vp << list_printer (fun tnv fmt ->
              fprintf fmt "@ %t@ %t"
                << frenv_lift_printer (subst_identity_name tnv) blv tnv
                << benv_lift_printer (upd tnv) blv tnv
            ) (binder_vars dm tn)
        in
        let pva blv l fmt = list_printer (pva blv) l fmt in
        fprintf fmt "%tassert {@ t.%t@ =@ %t%s%t%t@]@ }@] ;@ "
          indent << model_field_name tn << indent << cons_name dm cn
          << list_printer (fun (blv,_,_,_,vrs) fmt -> pva blv vrs fmt) bvars
          << pva blvf vf ;
        fprintf fmt "%tlet@ (%t%t%t@])@ =@ %t@]@ in@ "
          indent indent
          << list_printer (fun (_,_,_,_,vrs) fmt -> pv vrs fmt) bvars
          << pv vf
          << match_printer ~vbase tn mvcase mccase (fun fmt ->
            fprintf fmt "t.%t" << model_field_name tn) ;
        (* Relation between inversed model/inversed data (strange,
           but become difficult to prove very quickly with other assertions
           stacking before). Basically, this is a problem coming with the
           fact that they are invariant of the inversed data. *)
        let pv blv elv (vp,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn2 ->
            fprintf fmt "%tassert {@ m%t@ =@ %t%t@ %t%t@]@ }@] ;@ "
              indent vp indent << model_name tn2 << vp
              << list_printer (fun tnv fmt ->
                fprintf fmt "@ (%t)@ (%t)"
                  << frenv_lift_printer (subst_identity_name tnv) blv tnv
                  << benv_lift_printer (upd tnv) blv tnv
              ) (binder_vars dm tn2) in
        let pv blv elv l fmt = list_printer (pv blv elv) l fmt in
        fprintf fmt "%t%t" << list_printer (fun (blv,elv,_,_,vrs) fmt ->
          pv blv elv vrs fmt) bvars << pv blvf elvf vf ;
        (* Idem for depth bound majorations and free variables
           set abstraction. *)
        let pv blv (vp,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn2 -> list_printer (fun tnv fmt ->
              let lv = level tnv blv in
              let rec aux n fmt = match n with
                | 0 -> fprintf fmt "%t%t@ x@ t.%t@]@ &&@ %t"
                  indent << free_var_predicate_name tnv tn
                  << model_field_name tn
                  << free_var_in_set_predicate tnv (string_printer "x")
                  (fun fmt -> fprintf fmt "t.%t" << varset_field_name tnv tn)
                | _ -> fprintf fmt "%tmatch x with@ %t| None@ ->@ true@]@ \
                  %t| Some x@ ->@ %t@]@]@ end"
                  << indent << indent << indent << aux (n-1) in
              fprintf fmt "%tassert {@ %t%t@ %t@]@ <=@ %d@ }@] ;@ \
                %tassert {@ %tforall x:%t.@ \
                  %t%t@ x@ m%t@]@ ->@ %t@]@ }@] ;@ "
                indent indent << bound_depth_name tnv tn2 << vp
                << lv << indent << indent
                << options_printer (nlfree_var_type_name tnv) lv
                << indent << free_var_predicate_name tnv tn2 << vp
                << aux lv
            ) (binder_vars dm tn2) fmt in
        let pv blv l fmt = list_printer (pv blv) l fmt in
        fprintf fmt "%t%t" << list_printer (fun (blv,_,_,_,vrs) fmt ->
          pv blv vrs fmt) bvars << pv blvf vf ;
        (* relation between fully inversed model/updated data model. *)
        let pv blv elv (vp,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn2 ->
            let updt = TMap.fold (fun tnv l up ->
              let _,up = List.fold_left (fun (n,up) bvp ->
                n+1,nextup up tnv bvp n) (0,up) l in up) elv upd in
            let bnd2 tnv fmt =
              fprintf fmt "%t%t@ (%t)%t@]"
                indent << rename_subst_name tnv
                << benv_lift_printer (upd tnv) blv tnv
                << list_printer (fun tnv2 fmt ->
                  fprintf fmt "@ (%t)" << open_renaming tnv2 elv
                ) (binder_vars dm tnv) in
            fprintf fmt "%t%t%t@ %t%t@] ;@ "
              << list_printer (fun tnv fmt ->
                let n0 = level tnv blv in
                for i = 0 to n0 - 1 do
                  fprintf fmt "%tassert {@ %teval@ (%t)@ %d@]@ =@ \
                    (%t%t@ (%t%t@ %t@])%t@])@ =@ %teval@ (%t)@ %d@]@ }@] ;@ "
                    indent indent << updt tnv << i << indent
                    << rename_name tnv
                    << indent << variable_name tnv
                    << somes_printer (string_printer "None") i
                    << list_printer (fun tnv2 fmt ->
                      fprintf fmt "@ (%t)" << open_renaming tnv2 elv
                    ) (binder_vars dm tnv)
                    << indent << bnd2 tnv << i
                done
              ) (binder_vars dm tn2)
              << indent << model_equal_lemma_name tn2 << vp
              << list_printer (fun tnv fmt ->
                fprintf fmt "@ %t@ (%t%t@ (%t)%t@]) (%t)@ (%t)"
                  << subst_identity_name tnv
                  << indent << rename_subst_name tnv
                  << frenv_lift_printer (subst_identity_name tnv) blv tnv
                  << list_printer (fun tnv2 fmt ->
                    fprintf fmt "@ (%t)" << open_renaming tnv2 elv
                  ) (binder_vars dm tnv)
                  << updt tnv << bnd2 tnv
              ) (binder_vars dm tn2) in
        let pv blv elv l fmt = list_printer (pv blv elv) l fmt in
        fprintf fmt "%t%t" << list_printer (fun (blv,elv,_,_,vrs) fmt ->
          pv blv elv vrs fmt) bvars << pv blvf elvf vf ;
        (* Finish inversion by renaming. *)
        let pv elv (vp,ty) fmt = match ty with
          | ITVar _ -> fprintf fmt "%tlet@ mr%t@ =@ m%t@]@ in@ " indent vp vp
          | ITDecl tn -> let v = binder_vars dm tn in
            match v with
              | [] -> fprintf fmt "%tlet@ mr%t@ =@ m%t@]@ in@ " indent vp vp
              | _ -> fprintf fmt "%tlet@ mr%t@ =@ %t%t@ m%t%t@]@]@ in@ "
                indent vp indent << rename_name tn << vp
                << list_printer (fun tnv fmt ->
                  fprintf fmt "@ %t" << open_renaming tnv elv) v in
        let pv elv l fmt = list_printer (pv elv) l fmt in
        fprintf fmt "%t%t"
          << list_printer (fun (_,elv,_,_,vrs) fmt -> pv elv vrs fmt) bvars
          << pv elvf vf ;
        (* Unbind the variables (here). *)
        let pv update_list (vp,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn2 -> list_printer (fun (bvp,n,tnv,up) fmt ->
              fprintf fmt "%tlet@ %t@ =@ \
                %t%t@ %t@ %d@ (%t%t@ %t@])%t%t@]@]@ in@ "
                indent vp indent << unbind_var_name tnv tn2 << vp
                << n << indent << free_variable_name tnv << bvp
                << list_printer (fun tnv2 fmt ->
                  fprintf fmt "@ (%tghost@ %t@])@ \
                    (%tghost@ %t@])"
                    << indent << subst_identity_name tnv2
                    << indent << up tnv2
                ) (binder_vars dm tn2)
                << list_printer (fun tnv2 fmt ->
                  fprintf fmt "@ (%tghost@ %t@])" indent << upd tnv2
                ) (binder_vars dm tnv)
            ) update_list fmt in
        let upl elv =
          let update_list,_ = TMap.fold (fun tnv l (acc,up) ->
            let acc,_,up = List.fold_left (fun (acc,n,up) bvp ->
              let nup = nextup up tnv bvp n in
              (bvp,n,tnv,up)::acc,n+1,nup) (acc,0,up) l in
            acc,up) elv ([],upd) in
          update_list in
        let pv elv l fmt = list_printer (pv (upl elv)) l fmt in
        fprintf fmt "%t%t"
          << list_printer (fun (_,elv,_,_,vrs) fmt -> pv elv vrs fmt) bvars
          << pv elvf vf ;
        (* Model inversed, build the resulting elements. *)
        let pv (vp,ty) fmt = match ty with
          | ITVar _ -> fprintf fmt "%tlet@ res%t@ =@ %t@]@ in@ " indent vp vp
          | ITDecl tn2 -> fprintf fmt "%tlet@ res%t@ =@ %t{@ \
            %t%t@ =@ %t ;@]@ %t\
            %t%t@ =@ ghost@ mr%t ;@]@ \
            @]@ }@]@ in@ "
            indent vp indent indent << data_field_name tn2 << vp
            << list_printer (fun tnv fmt ->
              fprintf fmt "%t%t@ =@ fv%t ;@]@ "
                indent << varset_field_name tnv tn2 << tindex_printer tnv
            ) (binder_vars dm tn2)
            << indent << model_field_name tn2 << vp
        in
        let pv l fmt = list_printer pv l fmt in
        fprintf fmt "%t%t"
          << list_printer (fun (_,_,_,_,vrs) fmt -> pv vrs fmt) bvars
          << pv vf ;
        (* Build the result *)
        let pv (vp,ty) fmt = fprintf fmt "@ res%t" << vp in
        let pv l fmt = list_printer pv l fmt in
        fprintf fmt "%tlet@ res@ =@ %t%t%t%t@]@]@ in@ "
          << indent << indent << constructor_cons_name cn
          << list_printer (fun (_,_,wp,_,vrs) fmt ->
            fprintf fmt "@ %t%t" wp << pv vrs) bvars
          << pv vf ;
        (* Assertions : open|close = identity over the free variables,
           so free-var equivalence lemma. *)
        let pv blv elv (vp,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn2 -> let p1 fmt = fprintf fmt "identity" in
              let p2 tnv fmt = fprintf fmt "%trcompose@ (%t)@ (%t)@]"
                << indent
                << open_renaming tnv elv
                << closure_renaming tnv blv elv in
              let pint tnv fmt = closure_renaming tnv blv elv fmt in
            list_printer (fun tnv fmt ->
              let e0 = env_list tnv elv in
              let rec aux nb n l fmt = match l with
                | [] -> let v = somes_printer (string_printer "x") nb in
                  fprintf fmt "%t%teval@ (%t)@ (%t)@]@ =@ \
                    %teval@ (%t)@ x@]@ =@ \
                    %teval@ (%t)@ (%t)@]" << list_printer (fun bvp fmt ->
                      fprintf fmt "%tx@ <>@ %t@]@ &&@ " indent bvp
                    ) e0
                    << indent << p1 << v << indent << pint tnv
                    << indent << p2 tnv << v
                | ovp :: l ->
                  let v = somes_printer (string_printer "None") nb in
                  fprintf fmt "%tmatch x with@ \
                    %t| None@ ->@ %teval@ (%t)@ (%t)@]@ =@ \
                    %teval@ (%t)@ %t@]@ =@ \
                    %teval@ (%t)@ (%t)@]@]@ \
                    %t| Some x@ ->@ %t@]@]@ end"
                    indent indent indent p1 v
                    indent << pint tnv << ovp << indent << p2 tnv << v
                    << indent << aux (nb+1) (n-1) l in
              let n0 = level tnv blv in
              (* n0 = 0 degenerates to identity || identity = identity. *)
              if n0 <> 0
              then fprintf fmt "%tassert {@ %tforall@ x:%t.@ \
                %t%t@ x@ m%t@]@ ->@ %t@]@ }@] ;@ "
                indent indent << options_printer (nlfree_var_type_name tnv) n0
                << indent << free_var_predicate_name tnv tn2 << vp
                << aux 0 n0 e0 ) (binder_vars dm tn2) fmt ;
            fprintf fmt "%t%t@ m%t%t@] ;@ "
              indent << free_var_equivalence_lemma_name false false tn2
              << vp << list_printer (fun tnv fmt ->
                fprintf fmt "@ (%t)@ (%t)" p1 << p2 tnv
              ) (binder_vars dm tn2) in
        let pv blv elv l fmt = list_printer (pv blv elv) l fmt in
        fprintf fmt "%t%t" << list_printer (fun (blv,elv,_,_,vrs) fmt ->
          pv blv elv vrs fmt) bvars << pv blvf elvf vf ;
        (* Assertions : free variables of opened terms are indeed in the set
           abstractions. *)
        let pv blv elv (vp,ty) fmt = match ty with
          | ITVar _ -> ()
          | ITDecl tn2 -> list_printer (fun tnv fmt ->
            let e0 = env_list tnv elv in
            let p = free_var_in_set_predicate tnv (string_printer "x")
              (fun fmt -> fprintf fmt "fv%t" << tindex_printer tnv) in
            let rec aux n l fmt = match l with
              | [] -> fprintf fmt "x@ =@ y@ &&@ %t%t@ x@ t.%t@]@ &&@ %t"
                indent << free_var_predicate_name tnv tn
                << model_field_name tn << p
              | ovp :: l -> fprintf fmt "%tmatch y with@ \
                  %t| None@ ->@ x@ =@ %t@ &&@ %t@]@ \
                  %t| Some y@ ->@ %t@]@]@ end@ "
                  indent indent << ovp << p << indent << aux (n-1) l in
            let lv = level tnv blv in
            fprintf fmt "%tassert {@ %tforall@ x:%t.@ \
              %t%t@ x@ mr%t@]@ ->@ (%tforall@ y:%t.@ \
              (%t%t%t@ y@ m%t@]@ /\\@ %teval@ (%t)@ y@]@ =@ x@])@ ->@ \
              %t@])@ &&@ %t@]@ }@] ;@ "
              indent indent << nlfree_var_type_name tnv
              << indent << free_var_predicate_name tnv tn2 << vp
              << indent << options_printer (nlfree_var_type_name tnv) lv
              << indent << indent << free_var_predicate_name tnv tn2 << vp
              << indent << open_renaming tnv elv << aux lv e0 << p
            ) (binder_vars dm tn2) fmt in
        let pv blv elv l fmt = list_printer (pv blv elv) l fmt in
        fprintf fmt "%t%t" << list_printer (fun (blv,elv,_,_,vrs) fmt ->
          pv blv elv vrs fmt) bvars << pv blvf elvf vf ;
        fprintf fmt "res" in

      fprintf fmt "%tlet@ %t@ (t:%t%t%t@]) :@ %t%t%t@]@ \
        %trequires {@ %t%t@ t@]@ }@]@ \
        %tensures {@ %t%t@ result@]@ }@]@ \
        %tensures {@ %t%t@ result@ t@]@ }@]@ \
        %tensures {@ %t%t@ result@ t@]@ }@]@ \
        =@ %t%t@]@\n@\n"
        indent << destruction_operator_name tn << indent
        << impl_type_name tn << params_printer
        << indent << constructor_type_name tn << params_printer
        << indent << indent << invariant_name tn
        << indent << indent << constructor_invariant_name tn
        << indent << indent << constructor_relation_name tn
        << indent << indent << constructor_open_relation_name tn
        << list_printer (fun tnv fmt ->
            fprintf fmt "%tlet@ fv%t@ =@ t.%t@]@ in@ " indent
              << tindex_printer tnv << varset_field_name tnv tn) v
        << nlmatch_printer tn fvcase bvcase ccase (fun fmt ->
          fprintf fmt "t.%t" << data_field_name tn) in
    make_for_defs print_decl

  let subst_operator_printer fmt =
    let print_decl tnv tn c v =
      let vv = binder_vars dm tnv in
      let sid tn fmt =
        fprintf fmt "(%t%t:@ %t(%t)@ -> (%t%s%t%t@])@]@])"
          indent << subst_identity_name tn
          << indent << nlfree_var_type_name tn
          << indent << type_name dm tn << params_printer
          << list_printer (fun tnv fmt ->
            fprintf fmt "@ (%t)" << nlfree_var_type_name tnv
          ) (binder_vars dm tn)
      in
      let b0 tn fmt = fprintf fmt "(%tconst@ (%t%t@ (-1)@])@])"
        indent indent << variable_name tn in
      let s fmt = fprintf fmt "(%tupdate@ %t@ x@ u.%t@])"
        indent << sid tnv << model_field_name tnv in
      let s' tnv2 fmt = if tnv2 = tnv
        then s fmt
        else sid tnv2 fmt in
      fprintf fmt "%tlet@ %t@ (t:%t%t%t@])@ (x:%t)@ (u:%t%t%t@]) :@ %t%t%t@]@ \
        %trequires {@ %t%t@ t@]@ }@]@ \
        %trequires {@ %t%t@ u@]@ }@]@ \
        %tensures {@ %t%t@ result@]@ }@]@ \
        %tensures {@ result.%t@ =@ %t%t@ t.%t%t@]@ }@]@ \
        =@ %t%t@ t.%t%t@];@ \
        %tlet@ res@ =@ %t{@ \
          %t%t@ =@ %t%t@ t.%t@ x@ u.%t%t%t@]@] ;@ \
          %t%t%t@ =@ ghost@ %t%t@ t.%t%t@]@] ;@]@ \
        }@]@ in@ %tres@]@\n@\n"
        indent << subst_operator_name tnv tn << indent << impl_type_name tn
        << params_printer << nlfree_var_type_name tnv
        << indent << impl_type_name tnv << params_printer
        << indent << impl_type_name tn << params_printer
        << indent << indent << invariant_name tn
        << indent << indent << invariant_name tnv
        << indent << indent << invariant_name tn
        << indent << model_field_name tn << indent << subst_name tn
        << model_field_name tn << list_printer (fun tnv2 fmt ->
          fprintf fmt "@ %t" << s' tnv2) v
        << indent << model_equal_lemma_name tn << data_field_name tn
        << list_printer (fun tnv2 fmt ->
          fprintf fmt "@ (%t%t@ %t%t@])@ (%t)@ (%t%t@ %t%t@])@ (%t)"
            indent << subst_compose_name tnv2 << subst_identity_name tnv2
            << list_printer (fun tnv3 fmt ->
              fprintf fmt "@ (%t)" << s' tnv3
            ) (binder_vars dm tnv2)
            << s' tnv2
            << indent << subst_compose_name tnv2 << b0 tnv2
            << list_printer (fun tnv3 fmt ->
              fprintf fmt "@ (%t)" << s' tnv3
            ) (binder_vars dm tnv2)
            << b0 tnv2
        ) v
        << indent << indent << indent << data_field_name tn
        << indent << subst_base_name tnv tn
        << data_field_name tn
        << data_field_name tnv
        << list_printer (fun tnv2 fmt ->
          fprintf fmt "@ (%t)@ (%t)" << subst_identity_name tnv2 << b0 tnv2
        ) v
        << list_printer (fun tnv2 fmt ->
          fprintf fmt "@ (%t)" << b0 tnv2
        ) vv
        << list_printer (fun tnv2 fmt ->
          fprintf fmt "%t%t@ =@ %t@] ;@ "
            indent << varset_field_name tnv2 tn << (if List.mem tnv2 vv
              then varset_join tnv2 (fun fmt ->
                fprintf fmt "t.%t" << varset_field_name tnv2 tn) (fun fmt ->
                fprintf fmt "u.%t" << varset_field_name tnv2 tnv)
              else fun fmt -> fprintf fmt "t.%t" << varset_field_name tnv2 tn)
        ) v
        << indent << model_field_name tn << indent << subst_name tn
        << model_field_name tn << list_printer (fun tnv2 fmt ->
          fprintf fmt "@ %t" << s' tnv2) v
        << list_printer (fun tnv2 fmt ->
          let p = free_var_in_set_predicate tnv2 << string_printer "x2"
            << fun fmt -> fprintf fmt "res.%t" << varset_field_name tnv2 tn in
          fprintf fmt "%tassert {@ %tforall@ x2:%t.@ \
            %t%t@ x2@ res.%t@]@ ->@ (%ttrue%t@])@ &&@ %t@]@ }@] ;@ "
            indent indent << nlfree_var_type_name tnv2
            << indent << free_var_predicate_name tnv2 tn
            << model_field_name tn << indent
            << list_printer (fun tnv3 fmt ->
              if List.mem tnv2 (binder_vars dm tnv3)
              then begin
                fprintf fmt "@ /\\@ (%tforall@ y:%t.@ \
                  (%t%t%t@ y@ t.%t@]@ /\\@ \
                  %t%t@ x2@ (%teval@ (%t)@ y@])@]@])@ ->@ "
                  indent << nlfree_var_type_name tnv3
                  << indent << indent << free_var_predicate_name tnv3 tn
                  << model_field_name tn << indent
                  << free_var_predicate_name tnv2 tnv3 << indent
                  << s' tnv3 ;
                if tnv3 = tnv
                then fprintf fmt "(%t(%t%tx@ =@ y@]@ ->@ %t@])@ \
                  /\\@ (%t%tx@ <>@ y@]@ ->@ %t)@])@ &&@ %t@])@]"
                  indent indent indent p indent indent
                  (fun fmt -> if tnv2 = tnv3
                    then fprintf fmt "%tx2@ =@ y@]@ &&@ %t" indent p
                    else fprintf fmt "false") p
                else if tnv2 = tnv3
                  then fprintf fmt "%tx2@ =@ y@]@ &&@ %t@])" indent p
                  else fprintf fmt "false@])"
              end
            ) (binder_vars dm tn)
            << p
        ) v
    in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)

  let types_defs_printer fmt =
    type_defs_printer fmt ;
    implementation_type_printer fmt ;
    constructor_type_printer fmt

  let logics_defs_printer fmt =
    size_defs_printer fmt ;
    size_lemma_printer fmt ;
    shift_defs_printer fmt ;
    shift_lemma_printer fmt ;
    model_defs_printer fmt ;
    model_subst_commutation_lemma_printer fmt ;
    model_rename_commutation_lemma_printer fmt ;
    correct_indexes_printer fmt ;
    bound_depth_printer fmt ;
    bound_depth_lemma_printer fmt ;
    model_equal_lemma_printer fmt ;
    invariant_printer fmt ;
    constructor_invariant_printer fmt ;
    constructor_relation_printer fmt ;
    constructor_open_relation_printer fmt

  let impls_defs_printer fmt =
    bind_var_printer fmt ;
    unbind_var_printer fmt ;
    subst_base_printer fmt ;
    construction_operator_printer fmt ;
    destruction_operator_printer fmt ;
    subst_operator_printer fmt

end
