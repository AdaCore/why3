

open Ident
open Term
open Decl
open Task

let term_table = Hterm.create 257
let fmla_table = Hfmla.create 257
let extra_decls = ref []

let rec abstract_term keep t : term =
  match t.t_node with
    | Tconst _ | Tapp(_,[]) -> t
    | Tapp(ls,_) when keep ls ->
        t_map (abstract_term keep) (abstract_fmla keep) t
    | _ ->
        begin try Hterm.find term_table t with Not_found ->
          let ls = create_fsymbol (id_fresh "abstr") [] t.t_ty in
          let tabs = t_app ls [] t.t_ty in
          extra_decls := ls :: !extra_decls;
          Hterm.add term_table t tabs;
          tabs
        end

and abstract_fmla keep f =
  match f.f_node with
    | Ftrue | Ffalse -> f
    | Fnot _ | Fbinop _ ->
        f_map (abstract_term keep) (abstract_fmla keep) f
    | Fapp(ls,_) when keep ls ->
        f_map (abstract_term keep) (abstract_fmla keep) f
    | _ ->
        begin try Hfmla.find fmla_table f with Not_found ->
          let ls = create_psymbol (id_fresh "abstr") [] in
          let fabs = f_app ls [] in
          extra_decls := ls :: !extra_decls;
          Hfmla.add fmla_table f fabs;
          fabs
        end


let abstract_decl keep (d : decl) : decl list =
  let d = decl_map (abstract_term keep) (abstract_fmla keep) d in
  let l =
    List.fold_left
      (fun acc ls -> create_logic_decl [ls,None] :: acc)
      [d]
      !extra_decls
  in
  extra_decls := []; l

let abstraction (keep : lsymbol -> bool) (t: task) : task =
  Hfmla.clear fmla_table;
  Hterm.clear term_table;
  Trans.apply (Trans.decl (abstract_decl keep) None) t
