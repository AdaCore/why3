let prepare_for_counterexmp = 
  Trans.compose 
    Intro_projections_counterexmp.intro_projections_counterexmp
    (Trans.goal Introduction.intros)

let () = Trans.register_transform "prepare_for_counterexmp" prepare_for_counterexmp
  ~desc:"Transformation@ that@ prepares@ the@ task@ for@ quering@ for@ \
    the@ counter-example@ model.@ This@ transformation@ does@ so@ only@ \
when@ the@ solver@ will@ be@ asked@ for@ the@ counter-example."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
