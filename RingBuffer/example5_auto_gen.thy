
theory example5_auto_gen
	imports DeadlockFreedom
begin

subsection \<open> Model \<close>


	
	
datatype NIDS_stm05 = 
	NID_i0_stm05 | 
	NID_s0_stm05 | 
	NID_s1_stm05 
instantiation NIDS_stm05 :: discrete_cpo
begin

definition below_NIDS_stm05_def:
  "(x::NIDS_stm05) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm05_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm05\<close>

"internal__stm05" "NIDS_stm05"  |	
\<comment> \<open>flowchannel_stmbd_stm05\<close>

"interrupt_stm05"  |"exited_stm05"  |"exit_stm05"  |	
\<comment> \<open>var_channel_stmbd_stm05\<close>

"get_v1" "int"  |"set_v1" "int"  |"setL_v1" "int"  |"setR_v1" "int"  |
"get_bl" "bool"  |"set_bl" "bool"  |"setL_bl" "bool"  |"setR_bl" "bool"  |	
\<comment> \<open>event_channel_stmbd_stm05\<close>

"a_in"  |"a_out"  |
"b_in"  |"b_out"  |
"c_in"  |"c_out"  |
"a__in" "NIDS_stm05"  |
"b__in" "NIDS_stm05"  |
"c__in" "NIDS_stm05"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm05\<close>

"enter_i0_stm05"  |"interrupt_i0_stm05"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm05\<close>

"enter_s0_stm05"  |"entered_s0_stm05"  |"interrupt_s0_stm05"  |"enteredL_s0_stm05"  |"enteredR_s0_stm05"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm05\<close>

"enter_s1_stm05"  |"entered_s1_stm05"  |"interrupt_s1_stm05"  |"enteredL_s1_stm05"  |"enteredR_s1_stm05"  |	
\<comment> \<open>assumption-guarantee_viol_stm05\<close>

"aviol"  |"gviol" 	

                              
 
locale Trans 
begin

abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"


fixrec  
  SSTOP       :: "chan_event process"              and
  Terminate   :: "chan_event process"              
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>

fixrec  
Trans_stm05 :: "NIDS_stm05 \<rightarrow> chan_event process" and

Trans_stm05_core :: "NIDS_stm05 \<rightarrow> chan_event process"
where
[simp del] :\<open>Trans_stm05\<cdot>n = 
	((SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (assume (v1 \<ge> 1) (Trans_stm05\<cdot>n) (((((((n = NID_i0_stm05) \<^bold>& (((internal__stm05\<^bold>.NID_i0_stm05 \<rightarrow> (SSTOP \<triangle> (guar ((1::int) \<ge> 1) (set_v1\<^bold>!1 \<rightarrow> Skip))))\<^bold>;  (enter_s0_stm05 \<rightarrow> Trans_stm05\<cdot>NID_s0_stm05))))
	  \<box>
	  ((n = NID_s0_stm05) \<^bold>& ((((v1 \<ge> 1)) \<^bold>& (((internal__stm05\<^bold>.NID_s0_stm05 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm05 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm05 \<rightarrow> (SSTOP \<triangle> (get_bl\<^bold>?bl \<rightarrow> (assume True ((if (bl)then (SSTOP \<triangle> (b_out \<rightarrow> Skip))else(SSTOP \<triangle> (c_out \<rightarrow> Skip)))) (if (bl)then (SSTOP \<triangle> (b_out \<rightarrow> Skip))else(SSTOP \<triangle> (c_out \<rightarrow> Skip)))))))\<^bold>;  (enter_s1_stm05 \<rightarrow> Trans_stm05\<cdot>NID_s1_stm05))))))))))
	  \<box>
	  ((n = NID_s1_stm05) \<^bold>& ((((v1 < 1)) \<^bold>& (((internal__stm05\<^bold>.NID_s1_stm05 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm05 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm05 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm05 \<rightarrow> Trans_stm05\<cdot>NID_s0_stm05))))))))))
	  \<box>
	  ((n = NID_s1_stm05) \<^bold>& (((a__in\<^bold>.NID_s1_stm05 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm05 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm05 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm05 \<rightarrow> Trans_stm05\<cdot>NID_s0_stm05))))))))
	  \<box>
	  (share \<rightarrow> Trans_stm05\<cdot>n))
	  \<box>
	  (((interrupt_stm05 \<rightarrow> (SSTOP \<triangle> (exit_stm05 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm05 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))))) \<close>








|
[simp del] :\<open>Trans_stm05_core\<cdot>n = 
	((SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (assume (v1 \<ge> 1) (Trans_stm05_core\<cdot>n) (((((((n = NID_i0_stm05) \<^bold>& (((internal__stm05\<^bold>.NID_i0_stm05 \<rightarrow> (SSTOP \<triangle> (guar  ((1::int) \<ge> 1) (set_v1\<^bold>!1 \<rightarrow> Skip))))\<^bold>;  (enter_s0_stm05 \<rightarrow> Trans_stm05_core\<cdot>NID_s0_stm05))))
	  \<box>
	  ((n = NID_s0_stm05) \<^bold>& ((((v1 \<ge> 1)) \<^bold>& (((internal__stm05\<^bold>.NID_s0_stm05 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm05 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm05 \<rightarrow> (SSTOP \<triangle> (get_bl\<^bold>?bl \<rightarrow> (assume (bl = True) ((if (bl)then (SSTOP \<triangle> (b_out \<rightarrow> Skip))else(SSTOP \<triangle> (c_out \<rightarrow> Skip)))) (if (bl)then (SSTOP \<triangle> (b_out \<rightarrow> Skip))else(SSTOP \<triangle> (c_out \<rightarrow> Skip)))))))\<^bold>;  (enter_s1_stm05 \<rightarrow> Trans_stm05_core\<cdot>NID_s1_stm05))))))))))
	  \<box>
	  ((n = NID_s1_stm05) \<^bold>& ((((v1 < 1)) \<^bold>& (((internal__stm05\<^bold>.NID_s1_stm05 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm05 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm05 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm05 \<rightarrow> Trans_stm05_core\<cdot>NID_s0_stm05))))))))))
	  \<box>
	  ((n = NID_s1_stm05) \<^bold>& (((a__in\<^bold>.NID_s1_stm05 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm05 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm05 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm05 \<rightarrow> Trans_stm05_core\<cdot>NID_s0_stm05))))))))
)
  ))))) \<close>




lemma SSTOP_remove_seq: "SSTOP \<^bold>; P = SSTOP"
  by (meson AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SSTOP.simps non_terminating_Seq non_terminating_is_empty_ticks_of prefix_recursive_ddlf)



(*2 lemmas below used as assumptions in non_terminating_Interrupt_Seq*)
lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (meson Trans.SSTOP.unfold deadlock_free_implies_lifelock_free lifelock_free_is_non_terminating prefix_recursive_ddlf)

lemma prefix_Skip_no_initial_tick : \<open> (a\<rightarrow> Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)

lemma prefix_gviol_no_initial_tick : \<open> (gviol\<rightarrow> STOP)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)


lemma write_prefix_Skip_no_initial_tick : \<open>(c\<^bold>.a \<rightarrow>  Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: prefix_Skip_no_initial_tick write_is_write0)


lemma read_prefix_Skip_no_initial_tick : \<open> (c\<^bold>?a\<in>A \<rightarrow>  Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (smt (verit, best) Int_emptyI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(4) image_iff initials_Mprefix read_def)


lemma \<open>SSTOP \<triangle> ((a \<rightarrow> Skip) \<^bold>; STOP)\<^bold>;  (enter_s0_stm4 \<rightarrow>  Skip) = SSTOP \<triangle> ((a \<rightarrow> Skip) \<^bold>; STOP)\<close>
  by (metis SKIP_Seq SSTOP_nonTerm STOP_Seq Trans.prefix_Skip_no_initial_tick initials_write0 non_terminating_Interrupt_Seq
      write0_Seq)

lemma SSTOP_ddlf: 
  assumes P_def: \<open>SSTOP = share \<rightarrow> SSTOP\<close>
  shows \<open>deadlock_free SSTOP\<close>
  apply (rule df_step_intro[OF P_def])
  apply ( simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
  prefix_proving_Mndetprefix_UNIV_ref(3) eat_lemma no_step_refine 
             binops_proving_Mndetprefix_ref ndet_prefix_ext_choice Guard_def)
  done

lemma SSTOP_refine:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (meson interrupt_ref Trans.SSTOP.unfold assms)

lemma SSTOP_refine_plus:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (metis GlobalNdet_iterations'_Mndetprefix SSTOP.unfold assms interrupt_ref)


lemma Trans_ex4_ddlf:

  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm05_core\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm05_core.simps])
  (* Normalisation *)
  apply (rule SSTOP_refine_plus)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
  apply (rule read_proving_Mndetprefix_ref)
  apply (simp add: inj_def)
  apply simp+
  apply (simp add:  bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
  apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )
  (*discharge the guard*)
  using NIDS_stm05.exhaust atLeast0AtMost lessThan_Suc lessThan_Suc_atMost apply auto[1]

  apply (simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq     )
  apply (simp add: SSTOP_refine write0_Seq write_is_write0 GlobalNdet_refine_no_step eat_lemma)
  defer

  apply (simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq   write0_Seq   )
  apply (simp add: SSTOP_refine write0_Seq write_is_write0 GlobalNdet_refine_no_step eat_lemma)
  apply (simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq   write0_Seq)

(*TO DO: the last unsolved goal involves ifstmt, new lemma needed?*)
  apply (simp add: SSTOP_refine write0_Seq write_is_write0 GlobalNdet_refine_no_step eat_lemma)
  oops


end
end



