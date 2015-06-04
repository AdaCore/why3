open Task

let debug = Debug.register_info_flag "prepare_for_counterexmp"
  ~desc:"Print@ debugging@ messages@ about@ preparing@ the@ task@ for@ getting@ counter-example."

let meta_get_counterexmp =
  Theory.register_meta_excl "get_counterexmp" []
  ~desc:"Set@ when@ counter-example@ should@ be@ get."

let get_counterexmp task =
  let ce_meta = Task.find_meta_tds task meta_get_counterexmp in
  not (Theory.Stdecl.is_empty ce_meta.tds_set)

let prepare_for_counterexmp2 task = 
  if not (get_counterexmp task) then begin
    (* Counter-example will not be queried, do nothing *)
    Debug.dprintf debug "Not get ce@.";
    task
  end
  else begin
    (* Counter-example will be queried, prepare the task *)
    Debug.dprintf debug "Get ce@.";
    let comp_trans = Trans.compose 
      (Trans.goal Introduction.intros) 
      Intro_projections_counterexmp.intro_projections_counterexmp
    in
    (Trans.apply comp_trans) task
  end

let prepare_for_counterexmp = Trans.store prepare_for_counterexmp2

let () = Trans.register_transform "prepare_for_counterexmp" prepare_for_counterexmp
  ~desc:"Transformation@ that@ prepares@ the@ task@ for@ quering@ for@ \
    the@ counter-example@ model.@ This@ transformation@ does@ so@ only@ \
when@ the@ solver@ will@ be@ asked@ for@ the@ counter-example."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
