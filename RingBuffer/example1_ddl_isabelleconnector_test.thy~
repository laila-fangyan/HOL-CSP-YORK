theory example1_ddl_isabelleconnector_test 
	imports   DeadlockFreedom  example1_ddl (*Example1_ddlf_no_final can not be imported, why?*)
begin
(*
lemma Trans_stm0_core'_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans.Trans_stm0_core'\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans.Trans_stm0_core'.simps])
  (* Normalisation *)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
    (* Simplify away the events in the cases not inclucing interrupt *)
  apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )

  (* the below is simpler than above line, and works. the above is used in ex1_ddlf_no_final *)
 (*  apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )
*)
 
(*the guard can not be discharged*)
  nitpick
  sorry
  
*)

lemma Trans_stm0_core'_ddlf_auto:
 \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans.Trans_stm0_core'\<cdot>n)\<close>
  apply (Trans.deadlock_free' P_def: Trans.Trans_stm0_core'.simps)
(*is there a way to nitpick failed proof method?*)






end




