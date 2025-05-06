theory Example1_ddlf_no_final_isabelleconnector_test
  imports  DeadlockFreedom  Example1_ddlf_no_final
begin
                                 


method deadlock_free' uses P_def assms=
  (rule df_step_param_intro[OF P_def]
, simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
  , simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step
, insert NIDS_stm0.exhaust atLeast0AtMost, auto
, (simp add: Trans_ex1.SSTOP_nonTerm  Trans_ex1.prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq GlobalNdet_refine_no_step Trans_ex1.SSTOP_refine eat_lemma iso_tuple_UNIV_I)+
)


lemma Trans_ex1_ddlf_auto:
   \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1.Trans_ex1\<cdot>n)\<close>
  apply (deadlock_free' P_def: Trans_ex1.Trans_ex1.simps)
  nitpick





end



