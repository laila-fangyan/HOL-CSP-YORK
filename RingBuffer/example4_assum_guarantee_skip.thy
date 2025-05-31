(*this theory proves deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S *)
theory example4_assum_guarantee_skip
	imports   DeadlockSKIPSFreedom
begin


subsection \<open> Model \<close>
text\<open>this is the assumption-guarantee version of example 4.\<close>

	
	
datatype NIDS_stm4 = 
	NID_i0_stm4 | 
	NID_s0_stm4 | 
	NID_s1_stm4 
instantiation NIDS_stm4 :: discrete_cpo
begin

definition below_NIDS_stm4_def:
  "(x::NIDS_stm4) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm4_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm4\<close>

"internal__stm4" "NIDS_stm4"  |	
\<comment> \<open>flowchannel_stmbd_stm4\<close>

"interrupt_stm4"  |"exited_stm4"  |"exit_stm4"  |	
\<comment> \<open>var_channel_stmbd_stm4\<close>

"get_v1" "int"  |"set_v1" "int"  |"setL_v1" "int"  |"setR_v1" "int"  |	
\<comment> \<open>event_channel_stmbd_stm4\<close>

"a_in"  |"a_out"  |
"a__in" "NIDS_stm4"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm4\<close>

"enter_i0_stm4"  |"interrupt_i0_stm4"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm4\<close>

"enter_s0_stm4"  |"entered_s0_stm4"  |"interrupt_s0_stm4"  |"enteredL_s0_stm4"  |"enteredR_s0_stm4"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm4\<close>

"enter_s1_stm4"  |"entered_s1_stm4"  |"interrupt_s1_stm4"  |"enteredL_s1_stm4"  |"enteredR_s1_stm4" |
\<comment> \<open>state_channel_in_stmbd_s1_stm4\<close>
 "aviol" | "gviol"
                              
locale Trans 
begin

(*
fixrec 
  AVIOL       :: "chan_event process" where
  [simp del] :\<open>AVIOL = aviol \<rightarrow> AVIOL\<close>
*)

abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"

(*can not be defined as a fun in CZT because process is not a type in CZT
so we implement the RHS in M2M and, LHS in M2T
*)

fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>


fixrec  
 
Trans_stm4 :: "NIDS_stm4 \<rightarrow> chan_event process"   and
 
Trans_stm4' :: "NIDS_stm4 \<rightarrow> chan_event process"  and
 
Trans_stm4_core :: "NIDS_stm4 \<rightarrow> chan_event process" and
 
Trans_stm4_core' :: "NIDS_stm4 \<rightarrow> chan_event process"
where
[simp del] :\<open>Trans_stm4\<cdot>n = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((( 
    (n = NID_i0_stm4) \<^bold>& ((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> (set_v1\<^bold>!1 \<rightarrow> Skip)))\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4\<cdot>NID_s0_stm4))
	  \<box>
	   (n = NID_s0_stm4) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm4\<^bold>.NID_s0_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm4 \<rightarrow>  Trans_stm4\<cdot>NID_s1_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm4\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4\<cdot>NID_s0_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((a__in\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4\<cdot>NID_s0_stm4))))))
	  \<box>
	  ((share \<rightarrow> Skip)  \<^bold>;  Trans_stm4\<cdot>n ) ))
	  \<box>
	  (((interrupt_stm4 \<rightarrow> (SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm4 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))) \<close>
 |
[simp del] :\<open>Trans_stm4'\<cdot>n = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> assume (v1 \<ge> 1) (Trans_stm4'\<cdot>n) ( ((((( 
    (n = NID_i0_stm4) \<^bold>& ((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> guar ((2::int) \<ge> 1) (set_v1\<^bold>!1 \<rightarrow> Skip)))  \<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4'\<cdot>NID_s0_stm4) )
	  \<box>
	   (n = NID_s0_stm4) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm4\<^bold>.NID_s0_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm4 \<rightarrow>  Trans_stm4'\<cdot>NID_s1_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm4\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4'\<cdot>NID_s0_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((a__in\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4'\<cdot>NID_s0_stm4))))))
	 ) )
	  \<box>
	  (((interrupt_stm4 \<rightarrow> (SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm4 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))  )) \<close>



 |
[simp del] :\<open>Trans_stm4_core\<cdot>n = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (assume (v1 \<ge> 1) (Trans_stm4_core\<cdot>n) (((((( 
    (n = NID_i0_stm4) \<^bold>& ((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> guar ((2::int) \<ge> 1) (set_v1\<^bold>!2 \<rightarrow> Skip)))\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4_core\<cdot>NID_s0_stm4))
	  \<box>
	   (n = NID_s0_stm4) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm4\<^bold>.NID_s0_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm4 \<rightarrow> Trans_stm4_core\<cdot>NID_s1_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm4\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4_core\<cdot>NID_s0_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((a__in\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4_core\<cdot>NID_s0_stm4))))))
	 ) )
	 )))) \<close>


 |
[simp del] :\<open>Trans_stm4_core'\<cdot>n = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (if (v1 \<ge> 1) then 
     ((((( 
    (n = NID_i0_stm4) \<^bold>& ((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> (if ((1::int) \<ge> 1) then(set_v1\<^bold>!1 \<rightarrow> Skip) else (gviol \<rightarrow> STOP))))\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4_core'\<cdot>NID_s0_stm4))
	  \<box>
	   (n = NID_s0_stm4) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm4\<^bold>.NID_s0_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm4 \<rightarrow> Trans_stm4_core'\<cdot>NID_s1_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm4\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4_core'\<cdot>NID_s0_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((a__in\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4_core'\<cdot>NID_s0_stm4))))))
	 ) 
	 ) else (aviol \<rightarrow> Trans_stm4_core'\<cdot>n)
))) \<close>


lemma SSTOP_remove_seq: "SSTOP \<^bold>; P = SSTOP"
  by (meson AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S DeadlockFreedom.prefix_recursive_ddlf SSTOP.simps non_terminating_Seq
      non_terminating_is_empty_ticks_of)



(*2 lemmas below used as assumptions in non_terminating_Interrupt_Seq*)
lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (meson AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S DeadlockFreedom.prefix_recursive_ddlf Trans.SSTOP.unfold
      non_terminating_is_empty_ticks_of)

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
  shows \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SSTOP\<close>
  apply (rule df_step_intro[OF P_def])
  by (metis GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_Mndetprefix GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_is_Ndet_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations Ndet_FD_self_left
      dual_order.refl dual_order.trans prefix_proving_Mndetprefix_UNIV_ref(3))


lemma SSTOP_refine:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>  \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>  \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (meson DeadlockSKIPSFreedom.interrupt_ref Trans.SSTOP.unfold assms)

lemma SSTOP_refine_plus:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>  \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (metis GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_Mndetprefix SSTOP_refine assms)


find_theorems SKIPS UNIV
lemma Trans_ex4'_ddlf:
  "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. Trans_stm4'\<cdot>n)  "
  
  (* Step 1: to apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm4'.simps])
  
  (* Step 2: Normalisation *)
  (*to remove SSTOP interrupt and the var input*)
  apply (rule SSTOP_refine_plus) (*can this be grouped as norm? ? ? ?*)
  apply (rule GlobalNdet_reduce_read)
   apply (simp add: inj_on_def)

  (*to simplify away seq Skip*)
  apply (simp add:  read_Seq write_Seq write0_Seq)

  (*to normalize extchoice but not the unguarded ones which are the termination, so biextchoic_normalization_nguard and biextchoic_normalization_nguard_prefix are no longer needed *)
  apply (simp add:  bi_extchoice_norm  biextchoic_normalization )
  
  (*to split goal into aviol and not aviol*)
  apply (auto intro!:bi_extchoice_norm )

  (*to split the not aviol goal into transitions and terminations*)
  apply (rule ndet_prefix_ext_choice)

  defer (*to move the transitions' goal to the end*)
  (*to split the two terminations*)
  apply (rule ndet_prefix_ext_choice)

  (*to prove the 1st termination*)
  apply (rule eat_lemma)
  apply (simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick  non_terminating_Interrupt_Seq      )
  apply (rule SSTOP_refine  )
  apply (simp add: write0_Seq write_is_write0)
  apply (rule eat_lemma)
  apply (rule SSTOP_refine  )
  apply (rule eat_lemma)+
  apply (rule GlobalNdet_Skip)

  (*to prove the 2nd termination*)
  apply (rule eat_lemma)+
  apply (rule GlobalNdet_Skip)

  (*to prove aviol*)
  apply (auto intro!: eat_lemma GlobalNdet_refine_no_step)

  (*to prove transitions*)
  apply (auto intro!:bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )

  defer (*to move the goal of guards to the end and to be discharged by sledgehammer*)

  (*to discharge goal for each transition*)
  apply (simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq  SSTOP_refine  write_is_write0 GlobalNdet_refine_no_step eat_lemma)+
   
  (*to discharge the last goal for guards using sledgehammer*)
  using NIDS_stm4.exhaust atLeast0AtMost lessThan_Suc lessThan_Suc_atMost by auto
  



(*this version tries to do normalization first, then step-wise proof*)

lemma Trans_ex4_ddlf_norm_then_proof:

  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm4_core\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm4_core.simps])
  (* Normalisation *)


  apply (simp add:  bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix )

  apply (rule SSTOP_refine_plus)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
  apply (rule read_proving_Mndetprefix_ref)
  apply (simp add: inj_def)
    apply simp+
  apply (simp add:  bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
  
  apply auto
  apply (rule generalized_refine_guarded_extchoice_star)
  using NIDS_stm4.exhaust atLeast0AtMost lessThan_Suc lessThan_Suc_atMost apply auto[1]
  
  apply (auto intro!: prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine  write_proving_Mndetprefix_UNIV_ref  )
  (*discharge the guard*)


  apply (simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq    )
  apply (rule SSTOP_refine)
  apply (simp add: write0_Seq write_is_write0)
  apply (simp add: GlobalNdet_refine_no_step eat_lemma)
  
  apply (simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq  SSTOP_refine  write_is_write0 GlobalNdet_refine_no_step eat_lemma)+

  done


method deadlock_free' uses P_def assms=
  (rule df_step_param_intro[OF P_def]
, rule SSTOP_refine_plus
, simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, rule read_proving_Mndetprefix_ref
, simp add: inj_def
, simp+
, simp add:  bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step
, insert NIDS_stm4.exhaust  atLeast0AtMost lessThan_Suc lessThan_Suc_atMost ,auto
,(simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq  SSTOP_refine  write_is_write0 GlobalNdet_refine_no_step eat_lemma
)+

)
(*

lemma Trans_ex4_ddlf_auto:
   \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm4_core\<cdot>n)\<close>
  by (deadlock_free' P_def: Trans_stm4_core.simps)

*)
method normalization uses P_def assms=
  (rule df_step_param_intro[OF P_def]
, rule SSTOP_refine_plus
, simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, rule read_proving_Mndetprefix_ref
, simp add: inj_def
, simp+
, simp add:  bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

method deadlock_free uses P_def assms=
  (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step
, insert NIDS_stm4.exhaust  atLeast0AtMost lessThan_Suc lessThan_Suc_atMost ,auto
,(simp add: SSTOP_nonTerm  write_prefix_Skip_no_initial_tick prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq  SSTOP_refine  write_is_write0 GlobalNdet_refine_no_step eat_lemma
)+ )


lemma Trans_ex4_ddlf_auto_3_steps:
   \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm4_core\<cdot>n)\<close>
  apply (normalization P_def: Trans_stm4_core.simps)
  sledgehammer
  apply deadlock_free 
  done

end
end



