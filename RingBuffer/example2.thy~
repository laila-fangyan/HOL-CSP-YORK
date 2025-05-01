theory example2 
	imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation Law_Interrupt_Seq
begin

default_sort type


no_notation floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)

no_notation Cons  ("_ \<cdot>/ _" [66,65] 65)

abbreviation "dot"    :: "['a \<Rightarrow> 'b, 'a, 'b process] \<Rightarrow> 'b process"
  where      "dot c
 a P \<equiv> write c a P"

syntax   "_dot"  :: "[id, logic, 'a process] => 'a process"
                                        ("(3(_\<^bold>._) /\<rightarrow> _)" [0,0,78] 78)
translations
 
  "_dot c p P"     \<rightleftharpoons> "CONST dot c p P"


subsection \<open> Model \<close>


	
	
datatype NIDS_stm3 = 
	NID_i0_stm3 | 
	NID_s0_stm3 | 
	NID_s1_stm3 
instantiation NIDS_stm3 :: discrete_cpo
begin

definition below_NIDS_stm3_def:
  "(x::NIDS_stm3) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm3_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm3\<close>

"internal__stm3" "NIDS_stm3"  |	
\<comment> \<open>flowchannel_stmbd_stm3\<close>

"interrupt_stm3"  |"exited_stm3"  |"exit_stm3"  |	
\<comment> \<open>var_channel_stmbd_stm3\<close>

"get_v1" "int"  |"set_v1" "int"  |"setL_v1" "int"  |"setR_v1" "int"  |	
\<comment> \<open>event_channel_stmbd_stm3\<close>

"a_in"  |"a_out"  |
"a__in" "NIDS_stm3"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm3\<close>

"enter_i0_stm3"  |"interrupt_i0_stm3"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm3\<close>

"enter_s0_stm3"  |"entered_s0_stm3"  |"interrupt_s0_stm3"  |"enteredL_s0_stm3"  |"enteredR_s0_stm3"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm3\<close>

"enter_s1_stm3"  |"entered_s1_stm3"  |"interrupt_s1_stm3"  |"enteredL_s1_stm3"  |"enteredR_s1_stm3" 	
 
 
locale Trans
begin

fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              and
Trans_stm3 :: "NIDS_stm3 \<rightarrow> chan_event process"  and
Trans_stm3_core :: "NIDS_stm3 \<rightarrow> chan_event process"  and
Trans_stm3_core' :: "NIDS_stm3 \<rightarrow> chan_event process" and
Trans_stm3_core'' :: "NIDS_stm3 \<rightarrow> chan_event process" and
Trans_stm3_core''' :: "NIDS_stm3 \<rightarrow> chan_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>|

[simp del] :\<open>Trans_stm3 \<cdot>n=  
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> ((((((
     (n = NID_i0_stm3) \<^bold>& ((internal__stm3\<^bold>.NID_i0_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3\<cdot>NID_s0_stm3))
	  \<box>
	    (n = NID_s0_stm3) \<^bold>&  ((v1 \<ge> 1) \<^bold>& (((internal__stm3\<^bold>.NID_s0_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm3 \<rightarrow> Trans_stm3\<cdot>NID_s1_stm3))))))))
	  \<box>
	   (n = NID_s1_stm3) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm3\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3\<cdot>NID_s0_stm3))))))))
	  \<box>
	   (n = NID_s1_stm3) \<^bold>&  ((a__in\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3\<cdot>NID_s0_stm3))))))
	  \<box>
	  ((share \<rightarrow> Skip)\<^bold>;  Trans_stm3\<cdot>n)    ))
	  \<box>
	  (((interrupt_stm3 \<rightarrow> (SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm3 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))) \<close> |

[simp del] :\<open>Trans_stm3_core \<cdot>n= 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((
    (n = NID_i0_stm3) \<^bold>& ((internal__stm3\<^bold>.NID_i0_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core\<cdot>NID_s0_stm3))
	  \<box>
	  (n = NID_s0_stm3) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm3\<^bold>.NID_s0_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm3 \<rightarrow> Trans_stm3_core\<cdot>NID_s1_stm3))))))))
	  \<box>
	   (n = NID_s1_stm3) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm3\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core\<cdot>NID_s0_stm3))))))))
	  \<box>
	   (n = NID_s1_stm3) \<^bold>& ((a__in\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core\<cdot>NID_s0_stm3))))))
	  \<box>
	  ((share \<rightarrow> Skip)\<^bold>;  Trans_stm3_core\<cdot>n)    ))
	 )) \<close>
|

[simp del] :\<open>Trans_stm3_core' \<cdot>n= 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((
    (n = NID_i0_stm3) \<^bold>& ((internal__stm3\<^bold>.NID_i0_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core'\<cdot>NID_s0_stm3))
	  \<box>
	  (n = NID_s0_stm3) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm3\<^bold>.NID_s0_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm3 \<rightarrow> Trans_stm3_core'\<cdot>NID_s1_stm3))))))))
	  \<box>
	   (n = NID_s1_stm3) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm3\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core'\<cdot>NID_s0_stm3))))))))
	  \<box>
	   (n = NID_s1_stm3) \<^bold>& ((a__in\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core'\<cdot>NID_s0_stm3))))))
	  ))
	 )) \<close>

|

[simp del] :\<open>Trans_stm3_core''\<cdot>n= 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((
    (n = NID_i0_stm3) \<^bold>& ((internal__stm3\<^bold>.NID_i0_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core''\<cdot>NID_s0_stm3))
	  \<box>
	   (((n = NID_s0_stm3) \<and> (v1 \<ge> 1)) \<^bold>& (((internal__stm3\<^bold>.NID_s0_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm3 \<rightarrow> Trans_stm3_core''\<cdot>NID_s1_stm3))))))))
	  \<box>
	   ( ((n = NID_s1_stm3) \<and> (v1 < 1)) \<^bold>& (((internal__stm3\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core''\<cdot>NID_s0_stm3))))))))
	  \<box>
	   (n = NID_s1_stm3) \<^bold>& ((a__in\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Trans_stm3_core''\<cdot>NID_s0_stm3))))))
	  ))
	 )) \<close>

|

[simp del] :\<open>Trans_stm3_core''' \<cdot>n= 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((
   ( (n = NID_i0_stm3) \<^bold>& ((internal__stm3\<^bold>.NID_i0_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Skip)) \<^bold>; Trans_stm3_core'''\<cdot>NID_s0_stm3)
	  \<box>
	  ((n = NID_s0_stm3) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm3\<^bold>.NID_s0_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm3 \<rightarrow> Skip))))))) \<^bold>; Trans_stm3_core'''\<cdot>NID_s1_stm3) 
)
	  \<box>
	   ((n = NID_s1_stm3) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm3\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Skip))))))) \<^bold>; Trans_stm3_core'''\<cdot>NID_s0_stm3)
)
	  \<box>
	   ((n = NID_s1_stm3) \<^bold>& ((a__in\<^bold>.NID_s1_stm3 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3 \<rightarrow> Skip)))))\<^bold>; Trans_stm3_core'''\<cdot>NID_s0_stm3)
)
	  ))
	 )) \<close>

lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Trans.SSTOP.unfold ex1_m' non_terminating_is_empty_ticks_of)

lemma prefix_Skip_no_initial_tick : \<open> (a\<rightarrow> Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)

lemma SSTOP_refine:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (meson SSTOP.simps assms interrupt_ref)

lemma SSTOP_refine_plus:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (metis GlobalNdet_iterations'_Mndetprefix SSTOP.unfold assms interrupt_ref)

(*this trans has share \<rightarrow> Trans, so is deadlock free. also because has True &, so guards do not need to be proved.*)
lemma Trans_stm3_core_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm3_core\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm3_core.simps])
  (* Normalisation *)

  apply (simp add: guard_pushed_in bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
  
  apply (rule SSTOP_refine_plus)
  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
  apply (rule read_prefix_proving_Mndetprefix_ref    )
  apply (simp add: inj_def)
  apply (rule generalized_refine_guarded_extchoice_star)
  apply (simp add: atLeast0_atMost_Suc)

  apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )

  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!:  SSTOP_refine eat_lemma GlobalNdet_refine_no_step)
   (* The following is replaced by the line above
  apply (rule SSTOP_refine  )
  apply (rule eat_lemma)
  apply (rule SSTOP_refine  )
  apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
  *)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!:  SSTOP_refine eat_lemma GlobalNdet_refine_no_step)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!:  SSTOP_refine eat_lemma GlobalNdet_refine_no_step)
  done


lemma Trans_stm3_core'_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm3_core'\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm3_core'.simps])
  (* Normalisation *)
  apply (simp add: guard_pushed_in bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
apply (rule SSTOP_refine_plus)
  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  apply (rule read_prefix_proving_Mndetprefix_ref    )
  apply (simp add: inj_def)
  apply (rule generalized_refine_guarded_extchoice_star)
  
   apply (simp add: atLeast0_atMost_Suc)
  nitpick
(*nitpick returns a counterexample, how do we set v1 as 1*)
  oops



lemma Trans_stm3_core'''_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm3_core'''\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm3_core'''.simps])
  (* Normalisation *)
  apply (simp add: skip_seq )
(*trans not fully pushed in, TBD*)


  apply (simp add: guard_pushed_in bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  apply (rule SSTOP_refine_plus)
  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

apply (rule read_prefix_proving_Mndetprefix_ref    )
   apply (simp add: inj_def)
  apply (rule generalized_refine_guarded_extchoice_star)
  nitpick
   apply (simp add: atLeast0_atMost_Suc)
  using NIDS_stm3.exhaust apply blast
  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )

(*the guard can not be discharged*)
  nitpick
  oops
end
end



