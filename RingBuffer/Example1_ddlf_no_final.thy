theory Example1_ddlf_no_final 
	  imports DeadlockFreedom  RS_Deadlock_Freeness
begin
                                 

subsection \<open> Model \<close>
	
datatype NIDS_stm0 = 
	NID_i0_stm0 | 
	NID_s0_stm0 | 
	NID_s1_stm0
instantiation NIDS_stm0 :: discrete_cpo
begin

definition below_NIDS_def:
  "(x::NIDS_stm0) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_def)

end

\<comment> \<open>Channel Declaration\<close>
datatype trans_event = 
"share"|
\<comment> \<open>terminate_channel\<close>
"terminate"|
	
\<comment> \<open>internal_channel_stmbd_stm0\<close>

"internal__stm0" "NIDS_stm0"|
	
\<comment> \<open>flowchannel_stmbd_stm0\<close>

"interrupt_stm0" | 
"exited_stm0" | 
"exit_stm0" | 
	
\<comment> \<open>var_channel_stmbd_stm0\<close>
	
\<comment> \<open>event_channel_stmbd_stm0\<close>

"a_in" |
"a_out" |

"a__in" "NIDS_stm0"|


"b_in" |
"b_out" |

"b__in" "NIDS_stm0"|


"c_in" |
"c_out" |

"c__in" "NIDS_stm0"|
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0\<close>

"enter_i0_stm0" |
"interrupt_i0_stm0"|
	
\<comment> \<open>state_channel_in_stmbd_s0_stm0\<close>

"enter_s0_stm0"| 
"entered_s0_stm0"| 
"interrupt_s0_stm0"|
"enteredL_s0_stm0"|
"enteredR_s0_stm0"|
	
\<comment> \<open>state_channel_in_stmbd_s1_stm0\<close>

"enter_s1_stm0" |
"entered_s1_stm0" |
"interrupt_s1_stm0"| 
"enteredL_s1_stm0" |
"enteredR_s1_stm0" |
	
\<comment> \<open>state_channel_in_stmbd_s2_stm0\<close>

"enter_s2_stm0" |
"entered_s2_stm0" |
"interrupt_s2_stm0"| 
"enteredL_s2_stm0" |
"enteredR_s2_stm0" 

locale Trans_ex1 = 
 fixes d :: nat
begin
fixrec  SSTOP       :: "trans_event process"              and
        Trans_ex1   :: "NIDS_stm0 \<rightarrow> trans_event process" and
        Trans_ex1'  :: "NIDS_stm0 \<rightarrow> trans_event process" and
        Trans_ex1'' :: "NIDS_stm0 \<rightarrow> trans_event process" and
        Terminate    ::"trans_event process"              and
        Trans_ex1''' :: "NIDS_stm0 \<rightarrow> trans_event process"and
        Trans_ex1'''' :: "NIDS_stm0 \<rightarrow> trans_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|

[simp del] :\<open>Trans_ex1\<cdot>n = 
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))))
 \<close>|

[simp del] :\<open>Trans_ex1'\<cdot>n = 
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1'\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1'\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1'\<cdot>NID_s0_stm0))))
    \<box>
	  ((share \<rightarrow> Skip)\<^bold>; Trans_ex1'\<cdot>n)
\<close>|

[simp del] :\<open>Trans_ex1''\<cdot>n = 
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1''\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& ( ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1''\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1''\<cdot>NID_s0_stm0))))
    \<box> 
    ((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)))\<^bold>; (SSTOP \<triangle> (exited_stm0 \<rightarrow>   (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip) 
\<close>

|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>
|
[simp del] :\<open>Trans_ex1'''\<cdot>n = 
    ((n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1'''\<cdot>NID_s0_stm0 ))) 
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1'''\<cdot>NID_s1_stm0 )))))) 
	  \<box>
	  ((n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1'''\<cdot>NID_s0_stm0))))) 
    \<box>
	  ((share \<rightarrow> Skip)\<^bold>; Trans_ex1'''\<cdot>n)
    \<box> 
    ((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)))\<^bold>; (SSTOP \<triangle> (exited_stm0 \<rightarrow>   (terminate \<rightarrow> Terminate))))
	  \<box>
	  (terminate \<rightarrow> Terminate)
\<close>
|
[simp del] :\<open>Trans_ex1''''\<cdot>n = 
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1''\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& ( ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1''''\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1''''\<cdot>NID_s0_stm0))))
    \<box>
	  ((share \<rightarrow> Skip)\<^bold>; Trans_ex1''''\<cdot>n)
    \<box> 
    ((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)))\<^bold>; (SSTOP \<triangle> (exited_stm0 \<rightarrow>   (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip) 
\<close>



lemma SSTOP_remove_seq: "SSTOP \<^bold>; P = SSTOP"
  by (metis Trans_ex1.SSTOP.unfold deadlock_free_implies_lifelock_free prefix_recursive_ddlf lifelock_free_is_non_terminating non_terminating_Seq)


(*2 lemmas below used as assumptions in non_terminating_Interrupt_Seq*)
lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Trans_ex1.SSTOP.unfold prefix_recursive_ddlf non_terminating_is_empty_ticks_of)

lemma prefix_Skip_no_initial_tick : \<open> (a\<rightarrow> Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)


lemma ndet_prefix_ext_choice:
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D R"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> R"
  by (metis mono_Det_FD Det_id assms(1) assms(2))

lemma SSTOP_ddlf: 
  assumes P_def: \<open>SSTOP = share \<rightarrow> SSTOP\<close>
  shows \<open>deadlock_free SSTOP\<close>
  apply (rule df_step_intro[OF P_def])
  apply ( simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
  prefix_proving_Mndetprefix_UNIV_ref(3) eat_lemma no_step_refine 
             binops_proving_Mndetprefix_ref ndet_prefix_ext_choice Guard_def)
  done

(*TO DO: this lemma needs to be proved first to validate lemma "Trans_ex1_ddlf"*)
lemma SSTOP_refine:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (meson interrupt_ref Trans_ex1.SSTOP.unfold assms)

  
(*this is a valid proof*)
(*
lemma Trans_ex1_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_ex1.simps])
  (* Normalisation *)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )


  (*discharge the guards*)
  using NIDS_stm0.exhaust atLeast0_atMost_Suc apply auto[1]
    
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
 (* the above 6 steps equivalent to the line below: *)

  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  done

*)

lemma Trans_ex1''_restriction_fix :
  \<open>Rep_cfun Trans_ex1 =
   (\<upsilon> X. (\<lambda>n.
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> X NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  X NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> X NID_s0_stm0))))))\<close>
  
  apply (rule restriction_fix_unique[symmetric])
   apply (solves simp)
  by (metis (no_types, lifting) ext Trans_ex1.Trans_ex1.simps)


lemma deadlock_free_SSTOP :
  \<open>deadlock_free SSTOP\<close>
  using SSTOP_ddlf Trans_ex1.SSTOP.unfold by blast

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SSTOP :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SSTOP\<close>
  by (simp add: deadlock_free_SSTOP deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)

lemma Trans_ex1_ddlf_with_RS_ind:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n)  \<close>
proof (rule deadlock_free_GlobalNdet)
  show \<open>UNIV \<noteq> {}\<close> by simp
next
  let ?f = \<open>\<lambda>X n.
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> X NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  X NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> X NID_s0_stm0))))\<close>
  show \<open>deadlock_free (Trans_ex1\<cdot>n)\<close> for n
  proof (subst Trans_ex1''_restriction_fix, induct arbitrary: n rule: restriction_fix_ind[where f = ?f])
    show \<open>constructive ?f\<close> by simp
  next
    show \<open>adm\<^sub>\<down> (\<lambda>X. \<forall>n. deadlock_free (X n))\<close> unfolding deadlock_free_def by simp
  next
    show \<open>deadlock_free (DF UNIV)\<close> by (simp add: deadlock_free_def)
  next
    fix X :: \<open>NIDS_stm0 \<Rightarrow> (trans_event) process\<close> and n
    assume hyp : \<open>deadlock_free (X n)\<close> for n
    show \<open>deadlock_free (?f X n)\<close>
      apply (cases n)

      by (auto simp add: hyp deadlock_free_SSTOP deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SSTOP intro!: deadlock_free_introset deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset)
  qed
qed






method deadlock_free' uses P_def assms=
  (rule df_step_param_intro[OF P_def]
, simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
  , simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step
, insert NIDS_stm0.exhaust atLeast0AtMost, auto
, (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)+
)

thm "Trans_ex1.simps"

lemma Trans_ex1_ddlf_auto:
   \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n)\<close>
  by (deadlock_free' P_def: Trans_ex1.simps)




lemma Trans_ex1'_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1'\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_ex1'.simps])
  (* Normalisation *)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )
  (*move the goal for guards to the last*)

    
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )

   apply (rule SSTOP_refine)
   apply (rule eat_lemma)
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
 (* the above 5 steps equivalent to :
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I) *)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  done


lemma Trans_ex1''_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1''\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_ex1''.simps])
  (* Normalisation *)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )
  (*move the goal for guards to the last*)
    
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq)

   apply (rule SSTOP_refine)
   apply (rule eat_lemma)
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)+
   apply (simp add: GlobalNdet_refine_no_step)
   (* the above 5 steps equivalent to :
   apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I) *)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
   apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
   apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  oops
(*using deadlock_free, this is ddl and can not be proved*)


lemma Trans_ex1''_ddlf'':
\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S(\<sqinter> n \<in> UNIV. Trans_ex1''\<cdot>n  )\<close>
  (* Apply induction *)
  apply (rule df_step_param_intro_skip[OF Trans_ex1''.simps])
  oops


text\<open>20250404, The last two branches in the complete version of Trans (Trans_ex1'') lead to termination, and is deadlock. In order to prove the deadlock freedom of the transitions' behaviour, we can use the proof strategies: 2 options available\<close>
text\<open>option 1: because Skip is ddl, we turn the last 2 branches from terminating to non-terminating: to replace Skip with Terminate \<close>
term "Terminate = terminate \<rightarrow> Terminate"

lemma Trans_ex1'''_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1'''\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_ex1'''.simps])
  (* Normalisation *)

  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )
  (*move the goal for guards to the last*)

    
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)

 (* the above 5 steps equivalent to the next 2 lines:
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I) 
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
*)

  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
    apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)

  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
   apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  oops



text\<open>option 2: we construct a sequential composition as follows, then use the lemma norm_extchoice_seq and  non_terminating_Seq, to decompose the goal to obtain the subgoal of "deadlock_free Trans_core" \<close>
term "deadlock_free (Trans_stm0 \<^bold>; SSTOP)"

lemma norm_extchoice_seq: \<open>(P \<box> Q) \<^bold>; R = (P\<^bold>; R)  \<box> (Q \<^bold>; R)\<close>
  oops

lemma norm_extchoice_seq_gen:
  assumes "finite I" and "I \<noteq> {}"
  shows "(\<box> i \<in> I. P i) \<^bold>; R = (\<box> i \<in> I. (P i \<^bold>; R))"
  oops

  thm non_terminating_Seq
  term "( \<sqinter> n \<in> UNIV. Trans_ex1''\<cdot>n \<^bold>; SSTOP)"


lemma push_seq_into_guarded_extchoice:
  assumes "finite I" and "I \<noteq> {}"
  shows "(\<box> i\<in>I. (G i) \<^bold>& (P i)) \<^bold>; R = (\<box> i\<in>I. (G i) \<^bold>& (P i \<^bold>; R))"
  oops

lemma push_seq_into_guarded_extchoice_single:
 "( (G ) \<^bold>& (P )) \<^bold>; R = ( (G ) \<^bold>& (P  \<^bold>; R))"
  by (simp add: Guard_def)

lemma Guard_seq_indexed:
  assumes "finite I" and "I \<noteq> {}"
  shows "(\<box> i\<in>I. G i \<^bold>& P i) \<^bold>; Q = (\<box> i\<in>I. G i \<^bold>& (P i \<^bold>; Q))"
  using assms
  oops


lemma norm_guarded_extchoice_seq_gen:
  assumes "finite I" and "I \<noteq> {}"
  shows "(\<box> i\<in>I. G i \<^bold>& P i) \<^bold>; Q = (\<box> i\<in>I. G i \<^bold>& (P i \<^bold>; Q))"
  oops




(* new idea *)








lemma \<open>Trans_ex1'' =
Abs_cfun (\<lambda> n. (n = NID_i0_stm0) \<^bold>& (internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip \<^bold>; enter_s0_stm0 \<rightarrow> Trans_ex1''\<cdot>NID_s0_stm0) \<box>
       (n = NID_s0_stm0) \<^bold>&
       (a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip \<^bold>; SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>;
        SSTOP \<triangle> (exited_stm0 \<rightarrow> Skip \<^bold>; enter_s1_stm0 \<rightarrow> Trans_ex1''\<cdot>NID_s1_stm0)) \<box>
       (n = NID_s1_stm0) \<^bold>&
       (b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip \<^bold>; SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>;
        SSTOP \<triangle> (exited_stm0 \<rightarrow> Skip \<^bold>; enter_s0_stm0 \<rightarrow> Trans_ex1''\<cdot>NID_s0_stm0)) \<box>
       (interrupt_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>; SSTOP \<triangle> (exited_stm0 \<rightarrow> terminate \<rightarrow> Skip)) \<box>
       (terminate \<rightarrow> Skip))
\<close>
  using Trans_ex1.Trans_ex1''.unfold by blast


lemma Trans_ex1''_restriction_fix :
  \<open>Rep_cfun Trans_ex1'' =
   (\<upsilon> X. (\<lambda> n. (n = NID_i0_stm0) \<^bold>& (internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip \<^bold>; enter_s0_stm0 \<rightarrow> X NID_s0_stm0) \<box>
       (n = NID_s0_stm0) \<^bold>&
       (a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip \<^bold>; SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>;
        SSTOP \<triangle> (exited_stm0 \<rightarrow> Skip \<^bold>; enter_s1_stm0 \<rightarrow> X NID_s1_stm0)) \<box>
       (n = NID_s1_stm0) \<^bold>&
       (b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip \<^bold>; SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>;
        SSTOP \<triangle> (exited_stm0 \<rightarrow> Skip \<^bold>; enter_s0_stm0 \<rightarrow> X NID_s0_stm0)) \<box>
       (interrupt_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>; SSTOP \<triangle> (exited_stm0 \<rightarrow> terminate \<rightarrow> Skip)) \<box>
       (terminate \<rightarrow> Skip)))\<close>
  
  apply (rule restriction_fix_unique[symmetric])
   apply (solves simp)
  by (metis (no_types, lifting) ext Trans_ex1.Trans_ex1''.simps)


lemma Trans_ex1''_ddlf':
 \<open>deadlock_free( \<sqinter> n \<in> UNIV. (Trans_ex1''\<cdot>n \<^bold>; Terminate ) )\<close>
proof (subst deadlock_free_GlobalNdet_iff, intro conjI ballI)
  show \<open>UNIV \<noteq> {}\<close> by simp
next
  show \<open>deadlock_free (Trans_ex1''\<cdot>n \<^bold>; Terminate)\<close> for n
  proof (rule deadlock_free_Seq)
    show \<open>deadlock_free Terminate\<close>
      by (meson Trans_ex1.Terminate.unfold prefix_recursive_ddlf)
  next
    let ?f = \<open>(\<lambda>X n. (n = NID_i0_stm0) \<^bold>& (internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip \<^bold>; enter_s0_stm0 \<rightarrow> X NID_s0_stm0) \<box>
                     (n = NID_s0_stm0) \<^bold>&
                     (a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip \<^bold>; SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>;
                      SSTOP \<triangle> (exited_stm0 \<rightarrow> Skip \<^bold>; enter_s1_stm0 \<rightarrow> X NID_s1_stm0)) \<box>
                     (n = NID_s1_stm0) \<^bold>&
                     (b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip \<^bold>; SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>;
                      SSTOP \<triangle> (exited_stm0 \<rightarrow> Skip \<^bold>; enter_s0_stm0 \<rightarrow> X NID_s0_stm0)) \<box>
                     (interrupt_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip) \<^bold>; SSTOP \<triangle> (exited_stm0 \<rightarrow> terminate \<rightarrow> Skip)) \<box>
                     (terminate \<rightarrow> Skip))\<close>
    show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Trans_ex1''\<cdot>n)\<close>
    proof (unfold Trans_ex1''_restriction_fix,
           induct arbitrary: n rule: restriction_fix_ind[where f = ?f])
      show \<open>constructive ?f\<close> by simp
    next
      show \<open>adm\<^sub>\<down> (\<lambda>a. \<forall>x. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (a x))\<close>
        unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def by simp
    next
      show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
        by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)
    next
      fix X :: \<open>NIDS_stm0 \<Rightarrow> (trans_event) process\<close> and n
      assume hyp : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (X n)\<close> for n

      have \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SSTOP\<close>
        using SSTOP_ddlf Trans_ex1.SSTOP.unfold deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S by blast
      
      show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (?f X n)\<close>
        apply (cases n)
        by (auto simp add: hyp \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SSTOP\<close> intro!: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset)
    qed
  qed
qed




(* Benoît: initially I was trying to use the strategy below,
           not working but we could keep the idea for elsewhere

(* 
lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det_GuardedL :
  \<open>\<lbrakk>b \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P; deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q\<rbrakk>
   \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (b \<^bold>& P \<box> Q)\<close>
  by (simp add: Guard_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det_GuardedR :
  \<open>\<lbrakk>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P; b \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q\<rbrakk>
   \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<box> b \<^bold>& Q)\<close>
  by (simp add: Guard_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det_GuardedLR :
  \<open>\<lbrakk>b \<or> c; b \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P; c \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q\<rbrakk>
   \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (b \<^bold>& P \<box> c \<^bold>& Q)\<close>
  by (auto simp add: Guard_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_STOP)


method deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det_breaker =
  (* not very useful *)
  match conclusion in \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S proc\<close> for proc \<Rightarrow>
    \<open>match (proc) in \<open>b \<^bold>& P \<box> c \<^bold>& Q\<close> for b c P Q \<Rightarrow>
      \<open>rule deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det_GuardedLR\<close>
                 \<bar> \<open>b \<^bold>& P \<box> Q\<close> for b P Q \<Rightarrow>
      \<open>rule deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det_GuardedL\<close>
                 \<bar> \<open>P \<box> c \<^bold>& Q\<close> for c P Q \<Rightarrow>
      \<open>rule deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det_GuardedR\<close>
                 \<bar> \<open>P \<box> Q\<close> for P Q \<Rightarrow>
      \<open>rule deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det\<close>
                 \<bar> \<open>P\<close> for P \<Rightarrow> fail\<close>
    
 *)

  oops


lemma aux_self_leF_Det : \<open>P \<sqsubseteq>\<^sub>F Q1 \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q2 \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q1 \<box> Q2\<close>
  by (metis Ndet_F_Det Ndet_id mono_Ndet_F trans_F)

lemma transitived_Ndet_F_self_left : \<open>P \<sqsubseteq>\<^sub>F P' \<Longrightarrow> P \<sqinter> Q \<sqsubseteq>\<^sub>F P'\<close>
  by (metis Ndet_F_self_right Ndet_commute trans_F)

lemma transitived_Mndetprefix_UNIV_F_write0 :
  \<open>a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>F a \<rightarrow> Q\<close>
  by (meson Mndetprefix_F_write0 mono_write0_F trans_F)


method unfold_one_iteration =
  subst numeral_eq_Suc, subst iterate_Suc, simp del: One_nat_def


method progress_one_step =
  unfold_one_iteration,
  rule transitived_Ndet_F_self_left,
  rule transitived_Mndetprefix_UNIV_F_write0,
  solves simp


find_theorems deadlock_free Interrupt
  (* TODO: do lemmas about this ? *)


lemma \<open>P \<sqsubseteq>\<^sub>F SSTOP \<triangle> Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>F SSTOP \<and> \<close>


  find_theorems SSTOP
 

lemma Trans_ex1''_ddlf:
 assumes P_def: \<open>\<And>n. P n =  (Trans_ex1''\<cdot>n \<^bold>; Terminate )\<close>
 shows \<open>deadlock_free( \<sqinter> n \<in> UNIV.  P n )\<close>
proof (subst deadlock_free_GlobalNdet_iff, intro conjI ballI)
  show \<open>UNIV \<noteq> {}\<close> by simp
next
  show \<open>deadlock_free (P n)\<close> for n
  proof (unfold P_def, rule deadlock_free_Seq)
    show \<open>deadlock_free Terminate\<close>
      by (meson Trans_ex1.Terminate.unfold prefix_recursive_ddlf)
  next
    show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Trans_ex1''\<cdot>n)\<close>
    proof (rule constructive_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S[OF Trans_ex1''.simps])
      
    proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def,
            induct arbitrary: n rule: fix_ind_k[where k = 8])
      case admissibility
      then show ?case by simp
    next
      case base_k_steps
      then show ?case sorry
    next
      case (step X)
      thm step.hyps[THEN spec, of 0, simplified]
      
      show ?case
        apply (subst Trans_ex1''.unfold, subst beta_cfun, solves simp)
        apply (simp add: write0_Seq write_is_write0)
        apply (cases \<open>n = NID_i0_stm0\<close>, simp_all)


         apply (intro aux_self_leF_Det)[1]
           apply progress_one_step
           apply unfold_one_iteration

            apply (rule transitived_Ndet_F_self_left)
           apply (rule transitived_Mndetprefix_UNIV_F_write0, solves simp)
           apply (rule step.hyps[THEN spec, of 6, simplified, THEN spec])

          apply progress_one_step
          apply (subst non_terminating_Interrupt_Seq[OF SSTOP_nonTerm])
           apply (solves \<open>simp add: initials_write0 image_iff\<close>)
          apply (simp add: write0_Seq)
          apply (subst SSTOP.unfold)
          apply (subst Interrupt_write0)
          apply (rule aux_self_leF_Det)
           apply progress_one_step
           apply (subst SSTOP.unfold)
           apply (subst Interrupt_write0)
           apply (rule aux_self_leF_Det)
            apply progress_one_step
            apply progress_one_step
  
            apply unfold_one_iteration
            apply (solves \<open>simp add: numeral_eq_Suc Ndet_F_self_right UNIV_unit\<close>)

        apply progress_one_step
           apply (subst SSTOP.unfold)
           apply (subst Interrupt_write0)
           apply (rule aux_self_leF_Det)
            apply progress_one_step
            apply progress_one_step
            apply (solves \<open>simp add: numeral_eq_Suc Ndet_F_self_right UNIV_unit\<close>)

           apply progress_one_step
            apply (subst SSTOP.unfold)
          apply (subst Interrupt_write0)
           apply (rule aux_self_leF_Det)
            apply progress_one_step
            apply progress_one_step
            apply (solves \<open>simp add: numeral_eq_Suc Ndet_F_self_right UNIV_unit\<close>)
           apply progress_one_step

          apply (subst SSTOP.unfold)
           apply (subst Interrupt_write0)
           apply (rule aux_self_leF_Det)
            apply progress_one_step
            apply progress_one_step
            apply (solves \<open>simp add: numeral_eq_Suc Ndet_F_self_right UNIV_unit\<close>)
            apply progress_one_step
          
        apply (simp)
        apply (solves \<open>simp add: Ndet_F_self_right UNIV_unit\<close>)
            apply unfold_one_iteration
            apply (rule transitived_Ndet_F_self_left)
            apply (rule transitived_Mndetprefix_UNIV_F_write0, solves simp)
              
            apply )
        
        thm  non_terminating_Interrupt_Seq[OF SSTOP_nonTerm]


        oops
          
        apply (subst Interrupt_write0)
        
        thm Interrupt_write0
        find_theorems Interrupt write0
        sledgehammer
        apply (simp add: SSTOP_nonTerm)
        find_theorems Interrupt non_terminating

        using step.hyps[THEN spec, of 0, simplified, THEN spec]
        sledgehammer
          
         apply (auto intro!: aux_self_leF_Det)[1]
           apply (rule transitived_Ndet_F_self_left)
           apply (unfold write_is_write0)
           apply (rule transitived_Mndetprefix_UNIV_F_write0)
            apply simp
      
        apply (rule transitived_Mndetprefix_F_write0)
        find_theorems failure_refine write0 Mndetprefix

        oops
        sledgehammer
         apply split_failure_refine_Det
          apply split_failure_refine_Det

        apply (rule Ndet_F_self_left)
        find_theorems Ndet name: lef
         apply (subst Ndet_id[symmetric])
          apply (rule aux_Ndet_leF_Det)
        thm mono_Ndet_F 
        thm trans_F[OF _ Ndet_F_Det]
        apply (rule Ndet_F_Det[OF trans_F])
        find_theorems failure_refine Ndet Det
        apply (simp add: bi_extchoice_norm biextchoic_normalization )
        
        find_theorems Guard Seq
        find_theorems non_terminating Interrupt
        thm non_terminating_Interrupt_Seq[of SSTOP]
        sorry
    qed
*)

    find_theorems Guard True
      
      find_theorems 
      thm df_step_param_intro
      apply (simp add: bi_extchoice_norm biextchoic_normalization )
      apply (rule df_step_intro)
      thm df_step_intro
      thm df_step_param_intro thm 
      thm df_step_param_intro[of \<open>\<lambda>n. Trans_ex1''\<cdot>n\<close> \<open>\<lambda>n. Trans_ex1''\<cdot>n\<close>, simplified]
      apply (rule )
      sorry
    thm bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
  next
    show \<open>deadlock_free Terminate\<close>
      by (meson Trans_ex1.Terminate.unfold prefix_recursive_ddlf)
  qed
qed
  apply (rule df_step_param_intro[OF P_def])
  apply (subst Trans_ex1''.simps)  
                           
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
  
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

(* do we need a generalized norm_extchoice_seq?*)
  oops

(*
lemma Trans_ex1''_ddlf:
 assumes P_def: \<open>P n = \<sqinter> n \<in> UNIV. Trans_ex1''\<cdot>n \<^bold>; SSTOP \<close>
  shows \<open>deadlock_free  P \<close>
  apply (rule df_step_param_intro[OF P_def])
  oops

*)


method deadlock_free_trans uses P_def assms=
  (rule df_step_param_intro[OF P_def]
,simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
  , simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step
,insert NIDS_stm0.exhaust atLeast0_atMost_Suc , auto 
, (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq GlobalNdet_refine_no_step SSTOP_refine eat_lemma write0_Seq)+
)

(*
lemma Trans_ex1_ddlf_auto:
 \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n) \<close>
  by (deadlock_free_trans P_def: Trans_ex1.simps)

*)
thm Trans_ex1.simps

(*TO DO: This method needs to be updated, as it uses lemma [simp]: "(SSTOP \<triangle> Q) \<^bold>; R = SSTOP \<triangle> (Q \<^bold>; R)"*)
method normalization uses P_def =
  (subst P_def
  , simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)


lemma trans_norm:
 \<open>Trans_ex1\<cdot>n =  \<box>i\<in>{0..Suc (Suc 0)}.
            (if i \<le> Suc 0 then if i = 0 then n = NID_i0_stm0 else n = NID_s0_stm0 else n = NID_s1_stm0) \<^bold>&
            (if i \<le> Suc 0
             then if i = 0 then internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)
                  else a__in\<^bold>.NID_s0_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> SSTOP \<triangle> (exited_stm0 \<rightarrow> enter_s1_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s1_stm0))
             else b__in\<^bold>.NID_s1_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> SSTOP \<triangle> (exited_stm0 \<rightarrow> enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)))  \<close>
  apply (normalization P_def: Trans_ex1.simps)
  oops


method deadlock_free_trans_step2 uses P_def assms=
  (rule df_step_param_intro[OF P_def]
,simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step SSTOP_refine
, insert NIDS_stm0.exhaust atLeast0_atMost_Suc , auto 
)


lemma Trans_ex1_step2_df_a: 
  assumes P_def: \<open>\<And> n. Trans_ex1\<cdot>n  = \<box>i\<in>{0..Suc (Suc 0)}.
            (if i \<le> Suc 0 then if i = 0 then n = NID_i0_stm0 else n = NID_s0_stm0 else n = NID_s1_stm0) \<^bold>&
            (if i \<le> Suc 0
             then if i = 0 then internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)
                  else a__in\<^bold>.NID_s0_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> SSTOP \<triangle> (exited_stm0 \<rightarrow> enter_s1_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s1_stm0))
             else b__in\<^bold>.NID_s1_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> SSTOP \<triangle> (exited_stm0 \<rightarrow> enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)))\<close> 
 shows\<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n) \<close>
  by (deadlock_free_trans_step2 P_def: P_def)




(*
lemma [simp]: "(P \<triangle> Q) \<^bold>; R = (P \<^bold>; R) \<triangle> (Q \<^bold>; R)"
*)


(*ORIGINAL IsaCircus:
 Trans_stm0 = 	
(((((((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))
	  \<box>
	  ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s1_stm0 \<rightarrow> Skip))))))
	  \<box>
	  ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip));; Trans_stm0)
	  \<box>
	  ( ((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip) ))*)



(* this is the simpliest proved version with no interrupt or skip at the end
fixrec Trans_ex1  :: "NIDS_stm0 \<rightarrow> trans_event process"
  where \<open>Trans_ex1\<cdot>n = 

    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s1_stm0)))))

	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ( (exit_stm0 \<rightarrow> Skip))  \<^bold>; ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)))

\<close>

declare Trans_ex1.simps [simp del]

thm Trans_ex1.simps

lemma Trans_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n) \<close>
  apply (rule df_step_param_intro[OF Trans_ex1.simps])

  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
 
  apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step)
  using NIDS_stm0.exhaust atLeast0_atMost_Suc apply auto[1]
  done
 *)

end
end


