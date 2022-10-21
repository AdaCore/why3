;; produced by dreal.drv ;;
(set-logic QF_NRA)
;; "forall z:'a, z1:'a. match_bool True z z1 = z"
(declare-fun forall_zclqtacm_z1clqtadt_match_bool_True_z_z1_eq_z () Bool)

;; "forall z:'a, z1:'a. match_bool False z z1 = z1"
(declare-fun forall_zclqtacm_z1clqtadt_match_bool_False_z_z1_eq_z1 () Bool)

;; "forall u:bool. u = True \\/ u = False"
(declare-fun forall_uclbooldt_u_eq_True_bssl_u_eq_False () Bool)

;; "forall u:unit. u = ()"
(declare-fun forall_uclunitdt_u_eq_lprp () Bool)

;; "forall x:real. sqr x = (x * x)"
(declare-fun forall_xclrealdt_sqr_x_eq_lpx_as_xrp () Bool)

;; "x"
(declare-fun x () Real)

;; "sqr x1"
(declare-fun sqr_x1 () Real)

;; Goal "sqr_pos"
;; File "/home/paul/repos/why3/examples/tests-provers/dreal.mlw", line 74, characters 7-14
(assert
  (not (>= sqr_x1 0.0)))

(check-sat)
