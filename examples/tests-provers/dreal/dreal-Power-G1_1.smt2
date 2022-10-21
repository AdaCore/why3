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

;; "forall x:real, y:real. (x +. y) = (x + y)"
(declare-fun forall_xclrealcm_yclrealdt_lpx_pldt_yrp_eq_lpx_pl_yrp () Bool)

;; "forall x:real, y:real. (x -. y) = (x - y)"
(declare-fun forall_xclrealcm_yclrealdt_lpx_mndt_yrp_eq_lpx_mn_yrp () Bool)

;; "forall x:real, y:real. (x *. y) = (x * y)"
(declare-fun forall_xclrealcm_yclrealdt_lpx_asdt_yrp_eq_lpx_as_yrp () Bool)

;; "forall x:real, y:real. (x /. y) = (x / y)"
(declare-fun forall_xclrealcm_yclrealdt_lpx_sldt_yrp_eq_lpx_sl_yrp () Bool)

;; "forall x:real. (-. x) = (- x)"
(declare-fun forall_xclrealdt_lpmndt_xrp_eq_lpmn_xrp () Bool)

;; "forall x:real. inv x = inv1 x"
(declare-fun forall_xclrealdt_inv_x_eq_inv1_x () Bool)

;; "forall x:real, y:real. x <=. y <-> x <= y"
(declare-fun forall_xclrealcm_yclrealdt_x_lseqdt_y_lsmngt_x_lseq_y () Bool)

;; "forall x:real, y:real. x >=. y <-> x >= y"
(declare-fun forall_xclrealcm_yclrealdt_x_gteqdt_y_lsmngt_x_gteq_y () Bool)

;; "forall x:real, y:real. x <. y <-> x < y"
(declare-fun forall_xclrealcm_yclrealdt_x_lsdt_y_lsmngt_x_ls_y () Bool)

;; "forall x:real, y:real. x >. y <-> x > y"
(declare-fun forall_xclrealcm_yclrealdt_x_gtdt_y_lsmngt_x_gt_y () Bool)

;; "e"
(declare-fun e () Real)

;; "e'def"
(assert (= e (exp 1.0)))

;; "forall x:real. log2 x = (log x / log 2.0)"
(declare-fun forall_xclrealdt_log2_x_eq_lplog_x_sl_log_2dt0rp () Bool)

;; "forall x:real. log10 x = (log x / log 10.0)"
(declare-fun forall_xclrealdt_log10_x_eq_lplog_x_sl_log_10dt0rp () Bool)

;; "forall x:int. power x 0 = one"
(declare-fun forall_xclintdt_power_x_0_eq_one () Bool)

;; "forall x:int, n:int. n >=' 0 -> power x (n +' 1) = (x *' power x n)"
(declare-fun forall_xclintcm_nclintdt_n_gteqqt_0_mngt_power_x_lpn_plqt_1rp_eq_lpx_asqt_power_x_nrp () Bool)

;; "forall x:int, n:int. n >' 0 -> power x n = (x *' power x (n -' 1))"
(declare-fun forall_xclintcm_nclintdt_n_gtqt_0_mngt_power_x_n_eq_lpx_asqt_power_x_lpn_mnqt_1rprp () Bool)

;; "forall x:int. power x 1 = x"
(declare-fun forall_xclintdt_power_x_1_eq_x () Bool)

;; "forall x:int, n:int, m:int.\n 0 <=' n -> 0 <=' m -> power x (n +' m) = (power x n *' power x m)"
(declare-fun forall_xclintcm_nclintcm_mclintdtnl_0_lseqqt_n_mngt_0_lseqqt_m_mngt_power_x_lpn_plqt_mrp_eq_lppower_x_n_asqt_power_x_mrp () Bool)

;; "forall x:int, n:int, m:int.\n 0 <=' n -> 0 <=' m -> power x (n *' m) = power (power x n) m"
(declare-fun forall_xclintcm_nclintcm_mclintdtnl_0_lseqqt_n_mngt_0_lseqqt_m_mngt_power_x_lpn_asqt_mrp_eq_power_lppower_x_nrp_m () Bool)

;; "forall x:int, y:int.\n (x *' y) = (y *' x) ->\n (forall n:int. 0 <=' n -> (power x n *' y) = (y *' power x n))"
(declare-fun forall_xclintcm_yclintdtnl_lpx_asqt_yrp_eq_lpy_asqt_xrp_mngtnl_lpforall_nclintdt_0_lseqqt_n_mngt_lppower_x_n_asqt_yrp_eq_lpy_asqt_power_x_nrprp () Bool)

;; "forall x:int, y:int.\n (x *' y) = (y *' x) ->\n (forall n:int. 0 <=' n -> power (x *' y) n = (power x n *' power y n))"
(declare-fun forall_xclintcm_yclintdtnl_lpx_asqt_yrp_eq_lpy_asqt_xrp_mngtnl_lpforall_nclintdt_0_lseqqt_n_mngt_power_lpx_asqt_yrp_n_eq_lppower_x_n_asqt_power_y_nrprp () Bool)

;; "forall x:int, y:int. x >=' 0 /\\ y >=' 0 -> power x y >=' 0"
(declare-fun forall_xclintcm_yclintdt_x_gteqqt_0_slbs_y_gteqqt_0_mngt_power_x_y_gteqqt_0 () Bool)

;; "forall x:int, y:int. x >' 0 /\\ y >=' 0 -> power x y >' 0"
(declare-fun forall_xclintcm_yclintdt_x_gtqt_0_slbs_y_gteqqt_0_mngt_power_x_y_gtqt_0 () Bool)

;; "forall x:int, n:int, m:int.\n 0 <' x /\\ 0 <=' n /\\ n <=' m -> power x n <=' power x m"
(declare-fun forall_xclintcm_nclintcm_mclintdtnl_0_lsqt_x_slbs_0_lseqqt_n_slbs_n_lseqqt_m_mngt_power_x_n_lseqqt_power_x_m () Bool)

;; "x"
(declare-fun x () Real)

;; "x2 >. 2.0"
(declare-fun x2_gtdt_2dt0 () Bool)

;; "(pow x2 3.0 *. 2.0) >. 20.0"
(declare-fun lppow_x2_3dt0_asdt_2dt0rp_gtdt_20dt0 () Bool)

;; Goal "G1"
;; File "/home/paul/repos/why3/examples/tests-provers/dreal.mlw", line 120, characters 5-7
(assert
  (not lppow_x2_3dt0_asdt_2dt0rp_gtdt_20dt0))

(check-sat)
