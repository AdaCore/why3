
let (<<) f x = f x
let (<|) f x y = f y x

open Macrogen_printing
open Macrogen_decls
open Format

module Printer = functor (P:PrintParameters) -> struct
  
  open P.P
  open P.H
  
  let type_defs_printer fmt =
    List.iter (fun scc ->
      let tp = rec_type_printer () in
      List.iter (fun tn ->
        match type_def dm tn with
          | ITypeAssumption _ -> ()
          | ITypeDef (c,v) -> let b = string_printer "b" in
            fprintf fmt "%t%t %t%t@] =@ " indent tp indent
              << type_app_printer b tn ;
            (if c.var_present
             then fprintf fmt "| %t %t@\n" << variable_name tn
               << binding_type_printer b tn);
            let pl blevels l fmt =
              List.iter (fun ty ->
                fprintf fmt "@ (%t)" << type_printer ~blevels b ty ) l in
            List.iter (fun (cn,bl,tl) ->
              fprintf fmt "%t| %s" indent << cons_name dm cn ;
              let blevels = List.fold_left (fun blevels (tnv,tl) ->
                pl blevels tl fmt ; inc_level tnv blevels ) TMap.empty bl in
              fprintf fmt "%t@]@\n" << pl blevels tl ) c.cons_list ;
            fprintf fmt "@]@\n@\n"
      ) scc
    ) dm.sccg
  
  let size_defs_printer fmt =
    let pr = rec_fun_printer () in
    let print_decl is_nat tn _ _ =
      let fn = if is_nat then nat_size_name else size_name in
      let tyn = if is_nat then "nat" else "int" in
      let unity = if is_nat then "one_nat" else "1" in
      let op = if is_nat
        then fun p fmt ->
          fprintf fmt "%tlet s = add_nat@ (%t)@ s in@]@ " indent p
        else fun p fmt -> fprintf fmt "let s = %t@ +@ s in@ " p in
      let vcase _ fmt = fprintf fmt "%s" unity in
      let cons_case _ v fmt =
        let rec aux v fmt = match v with
          | [] -> fprintf fmt "let s = %s in@ " unity
          | ( vn , _ , ty ) :: q -> match ty with
            | ITVar _ -> aux q fmt
            | ITDecl tn -> fprintf fmt "%t%t" << aux q
              << op (fprintf <| "%t%t@ %t@]" <| indent <| fn tn <| vn)
        in fprintf fmt "%ts" << aux v in
      fprintf fmt "%t%t %t@ (t:%t) :@ %s@ =@ %t@]@\n@\n" indent pr << fn tn
        << type_app_printer (string_printer "b") tn
        << tyn << match_printer tn vcase cons_case (string_printer "t") in
    make_for_defs << print_decl true ;
    make_for_defs << print_decl false
  
  let size_lemma_printer fmt =
    let pr = rec_val_printer () in
    let print_decl tn _ _ =
      let vcase _ fmt = fprintf fmt "()" in
      let cons_case = lemma_cons_case (fun vp blevels tn fmt ->
          fprintf fmt "%t%t@ %t@]" indent << size_lemma_name tn << vp
        ) in
      fprintf fmt "%t%t lemma %t@ (t:%t) :@ unit@ \
        %tensures {@ %t@ t@ >@ 0@ }@]@ \
        %tvariant {@ nat_to_int %t(%t@ t)@]@ }@]@ =@ %t@]@\n@\n" indent pr
        << size_lemma_name tn
        << type_app_printer (string_printer "b") tn
        << indent << size_name tn
        << indent << indent << nat_size_name tn
        << match_printer tn vcase cons_case (string_printer "t") in
    make_for_defs print_decl
  
  let subst_defs_printer sub fmt =
    let pr = rec_fun_printer () in
    let fn = if sub then subst_name else rename_name in
    let b = string_printer "b" in
    let c = string_printer "c" in
    let sp tn fmt = fprintf fmt "s%t" << tindex_printer tn in
    let print_decl tn _ v =
      let vcase = if sub
        then fun v fmt ->
          fprintf fmt "s%t@ %t" << tindex_printer tn << v
        else fun v fmt ->
          fprintf fmt "%t %t(s%t@ %t)@]" << variable_name tn
            << indent << tindex_printer tn << v in
      let ccase = reconstruct_cons_case (fun v blevels tn fmt ->
          fprintf fmt "%t@ %t%t" << fn tn << v
            << list_printer (fun tn fmt ->
                fprintf fmt "@ %t" << lift_printer sub (sp tn) blevels tn
              ) (binder_vars dm tn)
        ) in
      fprintf fmt "%t%t %t@ (t:%t)%t :@ %t@ =@ %t@]@\n@\n"
        indent pr << fn tn << type_app_printer b tn
        << list_printer (fun tn fmt ->
            fprintf fmt "@ (s%t:%t)" << tindex_printer tn
            << subst_type_printer sub b c tn
          ) v
        << type_app_printer c tn
        << match_printer tn vcase ccase (string_printer "t") in
    make_for_bdefs print_decl
  
  let composition_lemma_printer sub1 sub2 fmt =
    let fn = match sub1,sub2 with
      | false,false -> renaming_composition_lemma_name
      | false,true -> rename_then_subst_composition_lemma_name
      | true,false -> subst_then_rename_composition_lemma_name
      | true,true -> subst_composition_lemma_name in
    let fn0 s = if s then subst_name else rename_name in
    let fn1,fn2,fna = fn0 sub1,fn0 sub2,fn0 (sub1||sub2) in
    let pr = rec_val_printer () in
    let b = string_printer "b" in
    let c = string_printer "c" in
    let d = string_printer "d" in
    let sp id tn fmt = fprintf fmt "s%s%t" id << tindex_printer tn in
    let print_cargs blevels sub id tn fmt =
      let v = binder_vars dm tn in
      list_printer (fun tn fmt ->
        fprintf fmt "@ %t" << lift_printer sub (sp id tn) blevels tn
      ) v fmt in
    let print_nargs sub id tn fmt =
      let v = binder_vars dm tn in
      list_printer (fun tn fmt ->
        fprintf fmt "@ %t" << sp id tn) v fmt in
    let vcase _ fmt = fprintf fmt "()" in
    let ccase = blemma_cons_case (fun vp blevels tn fmt ->
        fprintf fmt "%t@ %t%t%t"
        << fn tn << vp << print_cargs blevels sub1 "1" tn
        << print_cargs blevels sub2 "2" tn ) in
    let print_decl tn _ v =
      let print_dargs sub a b id fmt =
        list_printer (fun tn fmt ->
          fprintf fmt "@ (s%s%t:%t)" id << tindex_printer tn
            << subst_type_printer sub a b tn
        ) v fmt in
      fprintf fmt "%t%t lemma %t@ (t:%t)%t%t :@ unit@ \
        %tensures {@ %t%t@ %t(%t@ t%t)%t@]@]@ =@ %t%t@ t%t@]@ }@]@ \
        %tvariant {@ %t@ t@ }@]@ =@ %t@]@\n@\n" indent pr << fn tn
        << type_app_printer b tn
        << print_dargs sub1 b c "1" << print_dargs sub2 c d "2"
        << indent << indent << fn2 tn << indent << fn1 tn
        << print_nargs sub1 "1" tn << print_nargs sub2 "2" tn
        << indent << fna tn << list_printer (fun tn fmt ->
          fprintf fmt "@ (%t)"
          << print_composition sub1 sub2 tn (sp "1" tn) (sp "2")
        ) v
        << indent << size_name tn
        << match_printer tn vcase ccase (string_printer "t") in
    make_for_bdefs print_decl
  
  let identity_lemma_printer sub fmt =
    let pr = rec_val_printer () in
    let fp = if sub then subst_name else rename_name in
    let fn = if sub then subst_identity_lemma_name
      else renaming_identity_lemma_name in
    let identity = if sub then fun tn -> subst_identity_name tn
      else fun _ fmt -> fprintf fmt "identity" in
    let b = string_printer "b" in
    let vcase _ fmt = fprintf fmt "()" in
    let ccase = blemma_cons_case (fun vp _ tn fmt ->
      fprintf fmt "%t@ %t" << fn tn << vp) in
    let print_decl tn _ v =
      fprintf fmt "%t%t lemma %t@ (t:%t) :@ unit@ \
        %tensures {@ %t%t@ t%t@]@ =@ t@ }@]@ \
        %tvariant {@ %t@ t@ }@]@ =@ %t@]@\n@\n" indent pr << fn tn
        << type_app_printer b tn
        << indent << indent << fp tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ %t" << identity tn) v
        << indent << size_name tn
        << match_printer tn vcase ccase (string_printer "t") in
    make_for_bdefs print_decl
  
  let subst_composition_def_printer sub fmt =
    let fn = if sub then subst_compose_name else rename_subst_name in
    let fp = if sub then subst_name else rename_name in
    let b,c,d = string_printer "b",string_printer "c",string_printer "d" in
    let print_decl tn _ v =
      let print_args = list_printer (fun tn fmt ->
        fprintf fmt "@ s1%t" << tindex_printer tn) v in
      let print_right fmt =
        fprintf fmt "%t%t@ (s0 x)%t@]"
          indent << fp tn << print_args in
      let print_left fmt =
        fprintf fmt "%tfunction %t@ (s0:%t)%t :@ %t@]"
          << indent << fn tn << subst_type_printer true b c tn
          << list_printer (fun tn fmt ->
            fprintf fmt "@ (s1%t:%t)" << tindex_printer tn
              << subst_type_printer sub c d tn) v
          << subst_type_printer true b d tn in
      fprintf fmt "(*%t@ Abstraction@ definition@ axiom :@ \
        %t%t@ =@ %t(\\ x:'b%t.%t)@]@]@ @]*)@\n%t@\n\
        %taxiom %t_definition :@ %tforall s0:%t%t,@ x:'b%t@].@ \
          %t%t@ s0%t@ x@]@ =@ %t@]@\n@\n"
        << indent << indent << print_left << indent << tindex_printer tn
        << print_right << print_left << indent << fn tn << indent
        << subst_type_printer true b c tn
        << list_printer (fun tn fmt ->
          fprintf fmt ",@ s1%t:%t" << tindex_printer tn
            << subst_type_printer sub c d tn) v
        << tindex_printer tn << indent << fn tn << print_args
        << print_right in
    make_for_vdefs print_decl
  
  let associativity_lemma_printer (sub1,sub2,sub3) fmt =
    let fn = associativity_lemma_name (sub1,sub2,sub3) in
    let print_decl tn _ v =
      let b,c,d,e = string_printer "b",string_printer "c",
        string_printer "d",string_printer "e" in
      let print_targs b c d id = list_printer (fun tn fmt ->
        fprintf fmt "@ (s%s%t:%t)" id << tindex_printer tn
          << subst_type_printer b c d tn) v in
      let s1 fmt = fprintf fmt "s1" in
      let s2 id tn fmt = fprintf fmt "s%s%t" id << tindex_printer tn in
      let p1 =
        let p0 tn fmt =
          fprintf fmt "(%t)"
            (print_composition sub2 sub3 tn << s2 "2" tn << s2 "3") in
        print_composition sub1 (sub2||sub3) tn s1 p0 in
      let p2 =
        let p0 fmt =
          fprintf fmt "(%t)"
            << print_composition sub1 sub2 tn s1 (s2 "2") in
        print_composition (sub1||sub2) sub3 tn p0 << s2 "3" in
      fprintf fmt "%tlet lemma %t@ (s1:%t)%t%t :@ unit@ \
        %tensures {@ %t@ =@ %t@ }@]@ =@ \
        %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@]@]@\n@\n"
        indent << fn tn << subst_type_printer sub1 b c tn
        << print_targs sub2 c d "2" << print_targs sub3 d e "3"
        << indent << p1 << p2 << indent << indent << p1 << p2 in
    make_for_vdefs print_decl
  
  let right_identity_lemma_printer sub fmt =
    let fn = if sub then right_subst_by_identity_lemma_name
      else right_rename_by_identity_lemma_name in
    let id = if sub then subst_identity_name
      else fun _ fmt -> fprintf fmt "identity" in
    let b,c = string_printer "b",string_printer "c" in
    let print_decl tn _ v =
      let p2 = string_printer "s0" in
      let p1 = print_composition true sub tn p2 id in
      fprintf fmt "%tlet lemma@ %t@ (s0:%t) :@ unit@ \
        %tensures {@ %t@ =@ %t@ }@]@ =@ \
        %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@]@]@\n@\n"
        indent << fn tn << subst_type_printer true b c tn
        << indent << p1 << p2 << indent << indent << p1 << p2
    in make_for_vdefs print_decl
  
  let left_identity_lemma_printer sub fmt =
    let fn = if sub then left_subst_identity_lemma_name
      else left_rename_identity_lemma_name in
    let b,c = string_printer "b",string_printer "c" in
    let print_decl tn _ v =
      let p2 tn fmt = fprintf fmt "s%t" << tindex_printer tn in
      let p1 = print_composition true sub tn
        << typed_identity_printer true  b tn << p2 in
      let p2 = if sub then p2 tn
        else fun fmt -> fprintf fmt "%t%t@ s%t@]" indent
          << subst_of_rename_name tn << tindex_printer tn in
      fprintf fmt "%tlet lemma@ %t%t :@ unit@ \
        %tensures {@ %t@ =@ %t@ }@]@ =@ \
        %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@]@]@\n@\n"
        indent << fn tn << list_printer (fun tn fmt ->
          fprintf fmt "@ (s%t:%t)" << tindex_printer tn
             << subst_type_printer sub b c tn) v
        << indent << p1 << p2 << indent << indent << p1 << p2 in
    make_for_vdefs print_decl
  
  let subst_identity_printer fmt =
    let b = string_printer "b" in
    let c = string_printer "c" in
    let print_decl tn _ _ =
      let print_right fmt =
        fprintf fmt "%t%t@ x@]" indent << variable_name tn in
      let print_left fmt =
        fprintf fmt "constant@ %t :@ %t" << subst_identity_name tn
          << subst_type_printer true b b tn in
      fprintf fmt "(*%t@ Abstraction@ definition@ axiom :@ \
        %t%t@ =@ (%t\\ x:'b%t.@ %t@])@]@]*)@\n\
        %t%t@]@\n%taxiom@ %t_definition :@ \
        %tforall x:'b%t.@ %t%teval %t@ x@]@ =@ %t@]@]@]@\n@\n"
        indent indent print_left indent << tindex_printer tn
        << print_right << indent << print_left << indent
        << subst_identity_name tn << indent << tindex_printer tn
        << indent << indent << typed_identity_printer true b tn
        << print_right ;
      fprintf fmt "%tfunction@ %t@ (r:%t) :@ %t@ =@ \
        %trcompose@ r@ %t@]@]@\n@\n"
        indent << subst_of_rename_name tn << subst_type_printer false b c tn
        << subst_type_printer true b c tn << indent << subst_identity_name tn ;
      let p1 fmt =
        fprintf fmt "(%t%t@ %t@])" indent << slift_name tn
          << typed_identity_printer true b tn in
      let p2 = subst_identity_name tn in
      fprintf fmt "%tlet lemma@ %t@ (u:unit) :@ unit@ \
        %tensures {@ %t@ =@ %t@ }@]@ =@ \
        %tassert {@ %tforall x:option 'b%t.@ \
          %tmatch x with@ \
            %t| None ->@ %teval@ (%t)@ x@]@ =@ %teval@ (%t)@ x@]@]@ \
            %t| Some y ->@ %teval@ (%t)@ x@]@ =@ %teval@ (%t)@ x@]@]@]@ \
          end@]@ }@] ;@ \
        %tassert {@ extensionalEqual@ (%t)@ (%t)@ }@]@]@\n@\n"
        indent << slift_identity_lemma_name tn << indent << p1 << p2
        << indent << indent << tindex_printer tn
        << indent << indent << indent << p1 << indent << p2
        << indent << indent << p1 << indent << p2
        << indent << p1 << p2
      in
    make_for_vdefs print_decl
  
  let subst_lifting_printer fmt =
    let b,c = string_printer "b",string_printer "c" in
    let print_decl tn _ v =
      let blevels = inc_level tn TMap.empty in
      fprintf fmt "%tfunction@ %t@ (s:%t) :@ %t@ =@ \
        %tocase@ (%t%t@ s%t@])@ (%t%t@ None@])@]@]@\n@\n"
        indent << slift_name tn
        << subst_type_printer true b c tn
        << subst_type_printer true ~blevels b c tn
        << indent << indent << rename_subst_name tn
        << list_printer (fun tn' fmt ->
          if tn = tn' then fprintf fmt "@ some" else fprintf fmt "@ identity") v
        << indent << variable_name tn
    in
    make_for_vdefs print_decl
  
  let lifting_composition_lemma_printer (sub1,sub2) fmt =
    let b,c,d = string_printer "b",string_printer "c",string_printer "d" in
    let li s = if s then slift_name else fun _ fmt -> fprintf fmt "olift" in
    let li1,li2,lic = li sub1,li sub2,li (sub1||sub2) in
    let print_decl tn _ v =
      let blevels = inc_level tn TMap.empty in
      let print_targ tn fmt = fprintf fmt "@ (s2%t:%t)" << tindex_printer tn
        << subst_type_printer sub2 c d tn in
      let pa = if sub1
        then list_printer print_targ v
        else print_targ tn in
      let p0 tn fmt = fprintf fmt "s2%t" << tindex_printer tn in
      let p1 fmt =
        fprintf fmt "(%t%t@ (%t)@])" indent << lic tn
          << (print_composition sub1 sub2 tn << string_printer "s1"
            << fun tn fmt -> fprintf fmt "s2%t" << tindex_printer tn) in
      let p2 =
        let side1 fmt = fprintf fmt "(%t%t@ s1@])" indent << li1 tn in
        let side2 tn' fmt = if tn = tn'
          then fprintf fmt "(%t%t@ s2%t@])" indent
            << li2 tn << tindex_printer tn
          else lift_printer sub2 (p0 tn') blevels tn' fmt in
        print_composition sub1 sub2 tn side1 side2 in
      let cname = if sub2 then subst_name else rename_name in
      let pint fmt = if sub1
        then fprintf fmt "%t%t@ (%t%t@ (s1 y)%t@])%t@]"
          indent << cname tn << indent << rename_name tn
            << list_printer (fun tn' fmt -> if tn = tn'
              then fprintf fmt "@ some" else fprintf fmt "@ identity") v
            << list_printer (fun tn fmt ->
              fprintf fmt "@ %t" << lift_printer sub2 (p0 tn) blevels tn) v
        else fprintf fmt "%teval (%t) (%trcompose@ s1@ some@ y@])@]" indent
          << lift_printer sub2 (p0 tn) blevels tn
          << indent in
      let pint2 =
        let side1 fmt = fprintf fmt "s1" in
        let side2 = if sub2 then fun tn' fmt ->
            fprintf fmt "(%t%t@ s2%t%t@])"
              indent << rename_subst_name tn' << tindex_printer tn'
              << list_printer (fun tn'' fmt ->
                  if tn = tn'' then fprintf fmt "@ some"
                  else fprintf fmt "@ identity" ) (binder_vars dm tn')
          else fun tn' fmt -> if tn = tn'
            then fprintf fmt "(%trcompose@ s2%t@ some)@]" indent
              << tindex_printer tn
            else fprintf fmt "s2%t" << tindex_printer tn' in
        print_composition sub1 sub2 tn side1 side2 in
      fprintf fmt "%tlet lemma@ %t@ (s1:%t)%t :@ unit@ \
        %tensures {@ %t@ =@ %t }@]@ =@ \
        %tassert {@ %tforall x:option 'b%t.@ \
          %tmatch x with@ | None ->@ \
            %t%teval@ (%t)@ x@]@ =@ %teval@ (%t)@ x@]@]@ \
            | Some y ->@ %t%teval@ (%t)@ x@]@ =@ %teval@ (%t)@ y@]@ \
              =@ %t =@ %teval@ (%t)@ x@]@]@]@ end@]@ \
          }@] ;@ %tassert {@ %textensionalEqual@ (%t)@ (%t)@]@ }@]@]@\n@\n"
        indent << slift_composition_lemma_name (sub1,sub2) tn
        << subst_type_printer sub1 b c tn << pa << indent << p1 << p2
        << indent << indent << tindex_printer tn << indent
        << indent << indent << p1 << indent << p2
        << indent << indent << p1 << indent << pint2 << pint << indent << p2
        << indent << indent << p1 << p2 in
    make_for_vdefs print_decl
  
  let free_var_def_printer fmt =
    let pr = make_first_case_printer
      << string_printer "predicate"
      << string_printer "with" in
    let b = string_printer "b" in
    let print_decl tnv tn _ v =
      let vcase vname fmt =
        if tn = tnv
        then fprintf fmt "%t@ =@ x" vname
        else fprintf fmt "false" in
      let ccase _ vlist fmt =
        let printed = ref false in
        List.iter (fun (vname,blv,ct) -> match ct with
          | ITVar _ -> ()
          | ITDecl tn -> if List.mem tnv (binder_vars dm tn)
            then begin
                 (if !printed then fprintf fmt "@ \\/@ " else printed := true);
                fprintf fmt "%t%t@ %t@ %t@]" indent
                  << free_var_predicate_name tnv tn
                  << somes_printer (string_printer "x") (level tnv blv)
                  << vname
              end) vlist ;
        if not(!printed)
        then fprintf fmt "false" in
      fprintf fmt "%t%t@ %t@ (x:'b%t)@ (t:%t)@ =@ %t@]@\n@\n"
        indent pr << free_var_predicate_name tnv tn << tindex_printer tnv
        << type_app_printer b tn
        << match_printer tn vcase ccase (string_printer "t") in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv -> print_decl tnv tn c v) v)
  
  let subst_free_var_inversion_printer sub fmt =
    let pr = rec_val_printer () in
    let b,c,x = string_printer "b",string_printer "c",string_printer "x" in
    let sum_type p v fmt =
      let rec aux tn1 l fmt = match l with
        | [] -> p tn1 fmt
        | tn2 :: q -> fprintf fmt "%tsum@ (%t%t@])@ (%t%t@])@]"
          indent indent << p tn1 << indent << aux tn2 q in
      match v with
        | [] -> assert false
        | tn :: q -> aux tn q fmt in
    let sum_matching p v fmt =
      let rec aux tn1 l fmt = match l with
        | [] -> p tn1 fmt
        | tn2 :: q -> fprintf fmt "%tmatch@ sumx@ with@ \
          %t| Left@ sumx@] ->@ %t%t@]@ \
          %t| Right@ sumx@] ->@ %t%t@]@]@ end"
          indent indent indent << p tn1 << indent << indent << aux tn2 q in
      match v with
        | [] -> assert false
        | tn :: q -> aux tn q fmt in
    let rec rule_nones_out p n fmt = match n with
      | 0 -> p fmt
      | _ -> fprintf fmt "%tmatch@ sumx@ with@ \
          %t| None ->@ absurd@]@ \
          %t| Some sumx ->@ %t@]@] end" indent indent
          indent << rule_nones_out p (n-1) in
    
    let print_decl tnv tn _ v =
      let v0 = List.filter (fun tn2 ->
        List.mem tnv (binder_vars dm tn2)) v in
      let vcase = if sub
        then fun vname ->
          let rec aux l fmt = match l with
            | [] -> assert false
            | tnvr :: [] -> vname fmt
            | tnvr :: _ when tn = tnvr -> fprintf fmt "Left %t" vname
            | tnvr :: q -> fprintf fmt "%tRight@ (%t)@]" indent << aux q in
          aux v0
        else if tnv = tn
        then fun vname -> vname
        else fun _ -> string_printer "absurd" in
      let ccase _ vlist fmt =
        let rec aux l fmt = match l with
          | [] -> fprintf fmt "absurd"
          | (vname,blv,ITDecl tn2) :: q
            when List.mem tnv (binder_vars dm tn2) ->
              let lv = level tnv blv in
              let v2 = binder_vars dm tn2 in
              let args fmt =
                fprintf fmt "%t%t" vname
                  << list_printer (fun tn fmt ->
                    fprintf fmt "@ %t"
                      << lift_printer sub (fun fmt ->
                      fprintf fmt "s%t" << tindex_printer tn) blv tn
                    ) v2 in
              fprintf fmt "%tif %t%t@ %t@ (%t%t@ %t@])@]@ \
                %tthen@ %tlet sumx =@ %t%t@ %t@ %t@]@]@ in@ %t@ @]@ \
                %telse@ %t@]@]"
                indent indent << free_var_predicate_name tnv tn2
                << somes_printer x lv << indent
                << (if sub then subst_name tn2 else rename_name tn2)
                << args << indent << indent << indent
                << subst_free_var_inversion_helper_name sub tnv tn2
                << somes_printer x lv
                << args
                << (if sub
                  then sum_matching (fun tnvr ->
                      rule_nones_out (let rec aux l fmt = match l with
                          | [] -> assert false
                          | tnvr2 :: q when tnvr = tnvr2 ->
                            let base = match q with [] -> "sumx"
                              | _ -> "Left sumx" in
                            fprintf fmt "%tlet y =@ \
                              %t%t@ %t@ (%teval@ s%t@ sumx@])%t@] @]@ in@ \
                              %tassert {@ y@ =@ x@ }@] ;@ %s"
                              << indent << indent
                              << subst_free_var_inversion_helper_name
                                   false tnv tnvr
                              << somes_printer x (level tnv blv)
                              << indent << tindex_printer tnvr
                              << list_printer (fun tn fmt ->
                                fprintf fmt "@ %t"
                                  (csomes_printer << level tn blv))
                                  (binder_vars dm tnvr)
                              << indent << base
                          | tnvr2 :: q -> fprintf fmt "%tRight@ (%t)@]"
                            indent << aux q
                        in aux v0) (level tnvr blv)
                    ) (List.filter (fun tnx ->
                      List.mem tnv (binder_vars dm tnx)) (binder_vars dm tn2))
                  else rule_nones_out (string_printer "sumx") lv
                  )
                << indent << aux q
          | _ :: q -> aux q fmt in
        aux vlist fmt in
      let prefix gh name fmt =
        fprintf fmt "%t%t@ %s@ %t@ (x:'c%t)@ (t:%t)%t :@ %t@ \
          %trequires {@ %t%t@ x@ (%t%t@ t%t@])@]@ }@]@ "
          indent pr << (if gh then "ghost" else "lemma") << name
          << tindex_printer tnv
          << type_app_printer b tn << list_printer (fun tn fmt ->
            fprintf fmt "@ (s%t:%t)" << tindex_printer tn
              << subst_type_printer sub b c tn) v
          << (if gh
            then if sub
              then sum_type (fun tn fmt ->
                  fprintf fmt "'b%t" << tindex_printer tn
                ) v0
              else fun fmt -> fprintf fmt "'b%t" << tindex_printer tnv
            else string_printer "unit" )
          << indent << indent << free_var_predicate_name tnv tn << indent
          << (if sub then subst_name tn else rename_name tn)
          << list_printer (fun tn fmt ->
            fprintf fmt "@ s%t" << tindex_printer tn) v in
      
      fprintf fmt "%t%tensures {@ %t@ }@]@ \
        %tvariant {@ %t%t@ t@]@ }@]@ =@ \
        %t@]@\n@\n"
        << prefix true (subst_free_var_inversion_helper_name sub tnv tn)
        << indent << (if sub
          then fun fmt -> fprintf fmt "%tlet sumx =@ result@]@ in@ %t"
            indent << sum_matching (fun tn' fmt ->
              fprintf fmt "%t%t@ sumx@ t@]@ /\\@ %t%t@ x@ (%ts%t@ sumx@])@]"
                indent << free_var_predicate_name tn' tn << indent
                << free_var_predicate_name tnv tn' << indent
                << tindex_printer tn' ) v0
          else fun fmt ->
            fprintf fmt "%t%t@ result@ t@]@ /\\@ s%t result@ =@ x" indent
              << free_var_predicate_name tnv tn
              << tindex_printer tnv)
        << indent << indent << size_name tn
        << match_printer tn vcase ccase (string_printer "t") ;
      fprintf fmt "%t%tensures {@ %t@ }@]@ \
        %tvariant { 1 + %t%t@ t@] }@]@ =@ \
        %tlet sumx =@ %t%t@ x@ t%t@]@]@ in@ \
        %t@]@\n@\n"
        << prefix false (subst_free_var_inversion_lemma_name sub tnv tn)
        << indent << (if sub
          then sep_list_printer (fun tnvr fmt ->
              fprintf fmt "(%texists y:'b%t.@ \
                %t%t@ y@ t@]@ /\\@ %t%t@ x@ (s%t y)@]@])"
                indent << tindex_printer tnvr << indent
                << free_var_predicate_name tnvr tn
                << indent << free_var_predicate_name tnv tnvr
                << tindex_printer tnvr
            )
            (fun fmt -> fprintf fmt "@ \\/@ ")
            v0
          else fun fmt ->
            fprintf fmt "%texists y:'b%t.@ \
              %t%t@ y@ t@]@ /\\@ %ts%t y@ =@ x@]@]"
              indent << tindex_printer tnv
              << indent << free_var_predicate_name tnv tn
              << indent << tindex_printer tnv
            )
        << indent << indent << size_name tn
        << indent << indent << subst_free_var_inversion_helper_name sub tnv tn
        << list_printer (fun tn fmt ->
            fprintf fmt "@ s%t" << tindex_printer tn) v
        << if sub
          then sum_matching (fun _ fmt ->
                fprintf fmt "()") v0
          else fun fmt -> fprintf fmt "()"
    in
    
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)
  
  let rename_free_var_propagation_lemma_printer fmt =
    let pr = rec_val_printer () in
    let b,c = string_printer "b",string_printer "c" in
    let print_decl tnv tn _ v =
      let vcase _ fmt = fprintf fmt "()" in
      let ccase = blemma_cons_case (fun vname blv tn fmt ->
        if List.mem tnv (binder_vars dm tn)
        then fprintf fmt "%t@ %t@ %t%t"
          << rename_free_var_propagation_lemma_name tnv tn
          << somes_printer (string_printer "x") (level tnv blv)
          << vname << list_printer (fun tn fmt ->
            fprintf fmt "@ (%t)" << lift_printer false (fun fmt ->
              fprintf fmt "s%t" << tindex_printer tn
            ) blv tn
          ) (binder_vars dm tn)
        else fprintf fmt "()"
      ) in
      fprintf fmt "%t%t@ lemma@ %t@ (x:'b%t)@ (t:%t)%t :@ unit@ \
        %tensures {@ %t%t@ x t@] ->@ %t%t@ (s%t x)@ (%t%t@ t%t@])@]@ }@]@ \
        %tvariant {@ %t@ t@ }@]@ =@ %t@]@\n@\n"
        indent pr << rename_free_var_propagation_lemma_name tnv tn
        << tindex_printer tnv << type_app_printer b tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ (s%t:%t)" << tindex_printer tn
            << subst_type_printer false b c tn) v
        << indent << indent << free_var_predicate_name tnv tn
        << indent << free_var_predicate_name tnv tn
        << tindex_printer tnv << indent << rename_name tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ s%t" << tindex_printer tn) v
        << indent << size_name tn
        << match_printer tn vcase ccase (string_printer "t")
    in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)
  
  let subst_free_var_propagation_lemma_printer fmt =
    let pr = rec_val_printer () in
    let b,c = string_printer "b",string_printer "c" in
    let print_decl tni tnv tn _ v =
      let vcase _ fmt = fprintf fmt "()" in
      let ccase = blemma_cons_case (fun vname blv tn fmt ->
        if List.mem tni (binder_vars dm tn)
        then let sx = somes_printer (string_printer "x") (level tni blv) in
          let sy = somes_printer (string_printer "y") (level tnv blv) in
          let li tn = lift_printer true (fun fmt ->
          fprintf fmt "s%t" << tindex_printer tn) blv tn in
          fprintf fmt "%t%t@ %t@ %t@ %t%t@] ;@ \
            %t%t@ y@ (eval s%t x)%t@] ;@ \
            %tassert {@ %t%t@ y@ (s%t x)@] ->@ \
            %t%t@ %t@ (%teval@ (%t)@ %t@])@]@ }@]"
            indent << subst_free_var_propagation_lemma_name tni tnv tn
            << sx << sy
            << vname << list_printer (fun tn fmt ->
              fprintf fmt "@ (%t)" << li tn) (binder_vars dm tn)
            << indent << rename_free_var_propagation_lemma_name tnv tni
            << tindex_printer tni << list_printer (fun tn fmt ->
              fprintf fmt "@ %t" << csomes_printer (level tn blv))
              (binder_vars dm tni)
            << indent << indent << free_var_predicate_name tnv tni
            << tindex_printer tni
            << indent << free_var_predicate_name tnv tni
            << sy << indent << li tni << sx
        else fprintf fmt "()") in
      fprintf fmt "%t%t@ lemma@ %t@ (x:'b%t)@ (y:'c%t)@ (t:%t)%t: @ unit@ \
        %tensures {@ %t%t%t@ x t@]@ /\\@ %t%t@ y@ (s%t x)@]@] ->@ \
          %t%t@ y@ (%t%t@ t%t@])@]@ }@]@ \
        %tvariant {@ %t@ t@ }@]@ =@ %t@]@\n@\n"
        indent pr << subst_free_var_propagation_lemma_name tni tnv tn
        << tindex_printer tni << tindex_printer tnv
        << type_app_printer b tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ (s%t:%t)" << tindex_printer tn
            << subst_type_printer true b c tn) v
        << indent << indent << indent << free_var_predicate_name tni tn
        << indent << free_var_predicate_name tnv tni << tindex_printer tni
        << indent << free_var_predicate_name tnv tn
        << indent << subst_name tn
        << list_printer (fun tn fmt ->
          fprintf fmt "@ s%t" << tindex_printer tn) v
        << indent << size_name tn
        << match_printer tn vcase ccase (string_printer "t")
    in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tni ->
        List.iter (fun tnv ->
          print_decl tni tnv tn c v
        ) (binder_vars dm tni)
      ) v)
  
  let free_var_equivalence_lemma_prelude sub inv pr tn c v fmt =
    let b,c = string_printer "b",string_printer "c" in
    let sn = if sub then subst_name tn else rename_name tn in
    let ens,req = if inv then "requires","ensures" else
      "ensures","requires" in
    let args id = list_printer (fun tn fmt ->
      fprintf fmt "@ s%s%t" id << tindex_printer tn) v in
    let variant = if sub
      then fun fmt -> fprintf fmt "%tvariant {@ %t%t@ t@]@ }@]@ "
        indent indent << size_name tn
      else ignore in
    fprintf fmt "%t%t@ lemma@ %t@ (t:%t)%t :@ unit@ %t\
      %t%s {@ %t%t@ t%t@]@ =@ %t%t@ t%t@]@ }@]@ %t=@ "
      indent pr << free_var_equivalence_lemma_name sub inv tn
      << type_app_printer b tn << list_printer (fun tn fmt ->
          fprintf fmt "@ (s1%t:%t)@ (s2%t:%t)" << tindex_printer tn
            << subst_type_printer sub b c tn << tindex_printer tn
            << subst_type_printer sub b c tn) v
      << list_printer (fun tnv fmt ->
        fprintf fmt "%t%s {@ %tforall x:'b%t.@ \
          %t%t@ x@ t@] ->@ %ts1%t x@ =@ s2%t@ x@]@]@ }@]@ "
          indent req indent << tindex_printer tnv << indent
          << free_var_predicate_name tnv tn << indent
          << tindex_printer tnv << tindex_printer tnv
        ) v
      << indent << ens << indent << sn << args "1"
      << indent << sn << args "2" << variant
  
  let free_var_equivalence_lemma_printer sub fmt =
    if sub
    then let pr = rec_val_printer () in
      let print_decl tn c v =
        let vcase _ fmt = fprintf fmt "()" in
        let ccase = blemma_cons_case (fun vname blv tn2 fmt ->
          fprintf fmt "%t%t%t@ %t%t@]"
            << list_printer (fun tnv fmt ->
                let n0 = level tnv blv in
                let rec print_disj n fmt = match n with
                  | 0 -> fprintf fmt "%t%t@ x@ t@]" indent
                    << free_var_predicate_name tnv tn
                  | _ -> fprintf fmt "%tmatch x with@ \
                    %t| None ->@ true@]@ \
                    %t| Some x ->@ %t@]@]@ end"
                    indent indent indent << print_disj (n-1) in
                fprintf fmt "%tassert {@ %tforall x:%t.@ \
                  %t%t@ x@ %t@] ->@ %t@]@ }@] ;@ "
                  indent indent << options_printer (fun fmt ->
                    fprintf fmt "'b%t" << tindex_printer tnv) n0
                  << indent << free_var_predicate_name tnv tn2 << vname
                  << print_disj n0
              ) (binder_vars dm tn2)
            << indent << free_var_equivalence_lemma_name true false tn2
            << vname << list_printer (fun tnv fmt ->
              fprintf fmt "@ (%t)@ (%t)"
                << lift_printer true (fun fmt ->
                  fprintf fmt "s1%t" << tindex_printer tnv
                ) blv tnv
                << lift_printer true (fun fmt ->
                  fprintf fmt "s2%t" << tindex_printer tnv
                ) blv tnv) (binder_vars dm tn2)) in
        fprintf fmt "%t%t@]@\n@\n"
          << free_var_equivalence_lemma_prelude sub false pr tn c v
          << match_printer tn vcase ccase (string_printer "t") in
      make_for_bdefs print_decl
    else let pr fmt = fprintf fmt "let" in
      let print_decl tn c v =
        fprintf fmt "%t%t%t@ t%t@]@]@\n@\n"
          << free_var_equivalence_lemma_prelude sub false pr tn c v
          << indent << free_var_equivalence_lemma_name true false tn
          << list_printer (fun tn fmt ->
              let sor = subst_of_rename_name tn in
              fprintf fmt "@ (%t%t@ s1%t@])@ (%t%t@ s2%t@])"
                indent sor << tindex_printer tn
                << indent << sor << tindex_printer tn) v in
      make_for_bdefs print_decl
  
  let free_var_derive_equivalence_lemma_printer sub fmt =
    if sub
    then let pr = rec_val_printer () in
      let print_decl tn c v =
        let vcase _ fmt = fprintf fmt "()" in
        let ccase = blemma_cons_case (fun vname blv tn2 fmt ->
          fprintf fmt "%t%t@ %t%t@]%t"
            << indent << free_var_equivalence_lemma_name true true tn2
            << vname << list_printer (fun tnv fmt ->
              fprintf fmt "@ (%t)@ (%t)"
                << lift_printer true (fun fmt ->
                  fprintf fmt "s1%t" << tindex_printer tnv
                ) blv tnv
                << lift_printer true (fun fmt ->
                  fprintf fmt "s2%t" << tindex_printer tnv
                ) blv tnv) (binder_vars dm tn2)
            << list_printer (fun tnv fmt ->
              let ox = somes_printer (string_printer "x") (level tnv blv) in
              let pl1 = list_printer (fun tnv2 fmt ->
                fprintf fmt "@ %t" << csomes_printer (level tnv2 blv))
                (binder_vars dm tnv) in
              let pl2 = list_printer (fun tnv2 fmt ->
                let rec aux n fmt = if n = 0
                  then fprintf fmt "identity"
                  else fprintf fmt "(%tocase@ %t@ %t@])"
                    indent << aux (n-1)
                    << (somes_printer (fun fmt ->
                      fprintf fmt "y%t" << tindex_printer tnv2) (n-1)) in
                fprintf fmt "@ %t" << aux (level tnv2 blv))
                (binder_vars dm tnv) in
              fprintf fmt ";@ %tassert {@ (%tforall x:'b%t%t.@ \
                %t%t@ %t@ %t@]@ ->@ %t%t@ (s1%t x)%t@]@ =@ %teval (%t) %t@]@ \
                  =@ %teval (%t) %t@]@ =@ %t%t@ (s2%t x)%t@]@ &&@ \
                  s1%t x@ =@ %t%t@ (%t%t@ (s1%t x)%t@])%t@]@ =@ \
                  %t%t@ (%t%t@ (s2%t x)%t@])%t@]@ =@ s2%t x@ &&@ \
                  s1%t x@ =@ s2%t x@])@ &&@ %tforall x:'b%t.@ \
                %t%t@ %t@ %t@]@ ->@ s1%t x@ =@ s2%t x@]@ }@]"
                indent indent << tindex_printer tnv
                << list_printer (fun tnv2 fmt ->
                    fprintf fmt ",@ y%t:'c%t" << tindex_printer tnv2
                      << tindex_printer tnv2
                  ) (binder_vars dm tnv)
                << indent << free_var_predicate_name tnv tn2
                << ox << vname << indent << rename_name tnv
                << tindex_printer tnv << pl1
                << indent << lift_printer true (fun fmt ->
                  fprintf fmt "s1%t" << tindex_printer tnv) blv tnv
                << ox << indent << lift_printer true (fun fmt ->
                  fprintf fmt "s2%t" << tindex_printer tnv) blv tnv
                << ox << indent << rename_name tnv << tindex_printer tnv << pl1
                << tindex_printer tnv << indent << rename_name tnv << indent
                << rename_name tnv << tindex_printer tnv << pl1 << pl2
                << indent << rename_name tnv << indent << rename_name tnv
                << tindex_printer tnv << pl1 << pl2 << tindex_printer tnv
                << tindex_printer tnv << tindex_printer tnv
                << indent << tindex_printer tnv
                << indent << free_var_predicate_name tnv tn2
                << ox << vname << tindex_printer tnv << tindex_printer tnv
            ) (binder_vars dm tn2)) in
        fprintf fmt "%t%t@]@\n@\n"
          << free_var_equivalence_lemma_prelude sub true pr tn c v
          << match_printer tn vcase ccase (string_printer "t") in
      make_for_bdefs print_decl
    else let pr fmt = fprintf fmt "let" in
      let print_decl tn _ v =
        let c = string_printer "c" in
        fprintf fmt "%t%t%t@ t%t@]%t@]@\n@\n"
          << free_var_equivalence_lemma_prelude sub true pr tn c v
          << indent << free_var_equivalence_lemma_name true true tn
          << list_printer (fun tn fmt ->
              let sor = subst_of_rename_name tn in
              fprintf fmt "@ (%t%t@ s1%t@])@ (%t%t@ s2%t@])"
                indent sor << tindex_printer tn
                << indent << sor << tindex_printer tn) v
          << list_printer (fun tn fmt ->
            let sor = subst_of_rename_name tn in
            fprintf fmt ";@ %tassert {@ %tforall x:'b%t.@ \
              (%t%t@ s1%t@ x:%t@])@ =@ (%t%t@ s2%t@ x:%t@])@ ->@ \
              (%t%t@ (s1%t x):%t@])@ =@ (%t%t@ (s2%t x):%t@])@ &&@ \
              s1%t x@ =@ s2%t x@]@ }@]"
              indent indent << tindex_printer tn
              << indent << sor << tindex_printer tn << type_app_printer c tn
              << indent << sor << tindex_printer tn << type_app_printer c tn
              << indent << variable_name tn << tindex_printer tn
              << type_app_printer c tn
              << indent << variable_name tn << tindex_printer tn
              << type_app_printer c tn
              << tindex_printer tn << tindex_printer tn) v in
      make_for_bdefs print_decl
  
  (* TODO : remove ? do not seem that useful in fact. *)
  
  let open_close_defs_printer fmt =
    let b = string_printer "b" in
    let print_decl tnv tn c v =
      let blevels = inc_level tnv TMap.empty in
      fprintf fmt "%tfunction@ %t@ (t:%t)@ (x:'b%t) :@ %t@ =@ \
        %t%t@ t%t@]@]@\n@\n\
        %tfunction@ %t@ (t:%t)@ (x:'b%t) :@ %t@ =@ \
        %t%t@ t%t@]@]@\n@\n\
        %tfunction@ %t@ (t:%t)@ (u:%t) :@ %t@ =@ \
        %t%t@ t%t@]@]@\n@\n"
        indent << close_name tnv tn << type_app_printer b tn
        << tindex_printer tnv << type_app_printer ~blevels b tn
        << indent << rename_name tn << list_printer (fun tnv2 fmt ->
          if tnv = tnv2
          then fprintf fmt "@ (%tupdate@ some@ x@ None@])" indent
          else fprintf fmt "@ identity") v
        << indent << openv_name tnv tn << type_app_printer ~blevels b tn
        << tindex_printer tnv << type_app_printer b tn << indent
        << rename_name tn << list_printer (fun tnv2 fmt ->
          if tnv = tnv2
          then fprintf fmt "@ (%tocase@ identity@ x@])" indent
          else fprintf fmt "@ identity") v
        << indent << opent_name tnv tn << type_app_printer ~blevels b tn
        << type_app_printer b tnv << type_app_printer b tn
        << indent << subst_name tn << list_printer (fun tnv2 fmt ->
          if tnv = tnv2
          then fprintf fmt "@ (%tocase@ %t@ u@])" indent
            << subst_identity_name tnv
          else fprintf fmt "@ %t" << subst_identity_name tnv2) v
    in
    make_for_bdefs (fun tn c v ->
      List.iter (fun tnv ->
        print_decl tnv tn c v) v)
  
  let size_preservation_lemma_printer fmt =
    let b,c = string_printer "b",string_printer "c" in
    let pr = rec_val_printer () in
    let print_decl tn _ v =
      let vcase _ fmt = fprintf fmt "()" in
      let ccase = blemma_cons_case (fun vname blv tn fmt ->
          fprintf fmt "%t%t@ %t%t@]" indent
            << size_preservation_lemma_name tn
            << vname << list_printer (fun tn fmt ->
              fprintf fmt "@ (%t)" << lift_printer false (fun fmt ->
                  fprintf fmt "s%t" << tindex_printer tn
                ) blv tn) (binder_vars dm tn)) in
      fprintf fmt "%t%t@ lemma@ %t@ (t:%t)%t :@ unit@ \
        %tensures {@ %t%t@ (%t%t@ t%t@])@]@ =@ %t%t@ t@]@ }@]@ \
        %tvariant {@ %t%t@ t@]@ }@]@ =@ %t@]@\n@\n"
        indent pr << size_preservation_lemma_name tn
        << type_app_printer b tn << list_printer (fun tn fmt ->
          fprintf fmt "@ (s%t:%t)" << tindex_printer tn
            << subst_type_printer false b c tn) v
        << indent << indent << size_name tn << indent << rename_name tn
        << list_printer (fun tn fmt ->
          fprintf fmt " s%t" << tindex_printer tn) v
        << indent << size_name tn
        << indent << indent << size_name tn
        << match_printer tn vcase ccase (string_printer "t") in
    make_for_bdefs print_decl
  
  let required_imports fmt =
    fprintf fmt "use import option.Option@\n\
      use import int.Int@\nuse import Nat.Nat@\n\
      use import Functions.Func@\nuse import OptionFuncs.Funcs@\n\
      use import Sum.Sum@\n"
  
  let base_defs_printer fmt =
    type_defs_printer fmt ;
    size_defs_printer fmt ;
    size_lemma_printer fmt
  
  let subst_lemmae_defs_printer fmt =
    subst_defs_printer false fmt ;
    composition_lemma_printer false false fmt ;
    identity_lemma_printer false fmt ;
    subst_composition_def_printer false fmt ;
    associativity_lemma_printer (true,false,false) fmt ;
    associativity_lemma_printer (false,true,false) fmt ;
    right_identity_lemma_printer false fmt ;
    subst_lifting_printer fmt ;
    lifting_composition_lemma_printer (false,true) fmt ;
    lifting_composition_lemma_printer (true,false) fmt ;
    subst_defs_printer true fmt ;
    composition_lemma_printer false true fmt ;
    composition_lemma_printer true false fmt ;
    subst_composition_def_printer true fmt ;
    associativity_lemma_printer (false,true,true) fmt ;
    associativity_lemma_printer (true,false,true) fmt ;
    associativity_lemma_printer (true,true,false) fmt ;
    lifting_composition_lemma_printer (true,true) fmt ;
    composition_lemma_printer true true fmt ;
    associativity_lemma_printer (true,true,true) fmt ;
    subst_identity_printer fmt ;
    left_identity_lemma_printer false fmt ;
    identity_lemma_printer true fmt ;
    left_identity_lemma_printer true fmt ;
    right_identity_lemma_printer true fmt ;
    size_preservation_lemma_printer fmt
  
  let free_var_lemmae_defs_printer fmt =
    free_var_def_printer fmt ;
    subst_free_var_inversion_printer false fmt ;
    rename_free_var_propagation_lemma_printer fmt ;
    subst_free_var_inversion_printer true fmt ;
    subst_free_var_propagation_lemma_printer fmt ;
    free_var_equivalence_lemma_printer true fmt ;
    free_var_equivalence_lemma_printer false fmt ;
    free_var_derive_equivalence_lemma_printer true fmt ;
    free_var_derive_equivalence_lemma_printer false fmt
  
  
  
end


