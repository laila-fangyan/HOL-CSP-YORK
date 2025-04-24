theory example1_ddl 
	imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation Law_Interrupt_Seq  (*Example1_ddlf_no_final can not be imported, why?*)
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


	
	
datatype NIDS_stm0 = 
	NID_i0_stm0 | 
	NID_s0_stm0 | 
	NID_s1_stm0 | 
	NID_s2_stm0 
instantiation NIDS_stm0 :: discrete_cpo
begin

definition below_NIDS_stm0_def:
  "(x::NIDS_stm0) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm0_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm0\<close>

"internal__stm0" "NIDS_stm0"  |	
\<comment> \<open>flowchannel_stmbd_stm0\<close>

"interrupt_stm0"  |"exited_stm0"  |"exit_stm0"  |	
\<comment> \<open>event_channel_stmbd_stm0\<close>

"a_in"  |"a_out"  |
"b_in"  |"b_out"  |
"c_in"  |"c_out"  |
"a__in" "NIDS_stm0"  |
"b__in" "NIDS_stm0"  |
"c__in" "NIDS_stm0"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0\<close>

"enter_i0_stm0"  |"interrupt_i0_stm0"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm0\<close>

"enter_s0_stm0"  |"entered_s0_stm0"  |"interrupt_s0_stm0"  |"enteredL_s0_stm0"  |"enteredR_s0_stm0"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm0\<close>

"enter_s1_stm0"  |"entered_s1_stm0"  |"interrupt_s1_stm0"  |"enteredL_s1_stm0"  |"enteredR_s1_stm0"  |	
\<comment> \<open>state_channel_in_stmbd_s2_stm0\<close>

"enter_s2_stm0"  |"entered_s2_stm0"  |"interrupt_s2_stm0"  |"enteredL_s2_stm0"  |"enteredR_s2_stm0" 	

                              
 
locale Trans =
fixes d :: nat
begin

fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              and
 
Trans_stm0 :: "NIDS_stm0 \<rightarrow> chan_event process" and
 
Trans_stm0_core :: "NIDS_stm0 \<rightarrow> chan_event process" and
 
Trans_stm0_core' :: "NIDS_stm0 \<rightarrow> chan_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>|

[simp del] :\<open>Trans_stm0\<cdot>n = 
	((((((
     (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0 \<rightarrow> Trans_stm0\<cdot>NID_s0_stm0))
	  \<box>
	   (n = NID_s0_stm0) \<^bold>&  ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm0 \<rightarrow> Trans_stm0\<cdot>NID_s1_stm0))))))
	  \<box>
	   (n = NID_s1_stm0) \<^bold>&  ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0 \<rightarrow> Trans_stm0\<cdot>NID_s0_stm0))))))
	  \<box>
	  (n = NID_s0_stm0) \<^bold>&  ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s2_stm0 \<rightarrow> Trans_stm0\<cdot>NID_s2_stm0))))))
	  \<box>
(	  (share \<rightarrow> Skip) \<^bold>;  Trans_stm0\<cdot>n) ))
	  \<box>
	  (((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))) \<close>
|

[simp del] :\<open>Trans_stm0_core\<cdot>n = 
	(((((
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0 \<rightarrow> Trans_stm0_core\<cdot>NID_s0_stm0))
	  \<box>
	   (n = NID_s0_stm0) \<^bold>&  ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm0 \<rightarrow> Trans_stm0_core\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>&  ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0 \<rightarrow> Trans_stm0_core\<cdot>NID_s0_stm0))))))
	  \<box>
	  (n = NID_s0_stm0) \<^bold>& ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s2_stm0 \<rightarrow> Trans_stm0_core\<cdot>NID_s2_stm0))))))
	  \<box>
(	  (share \<rightarrow> Skip) \<^bold>;  Trans_stm0_core\<cdot>n) ))
	   \<close>
|

[simp del] :\<open>Trans_stm0_core'\<cdot>n = 
	(((((
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0 \<rightarrow> Trans_stm0_core'\<cdot>NID_s0_stm0))
	  \<box>
	   (n = NID_s0_stm0) \<^bold>&  ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm0 \<rightarrow> Trans_stm0_core'\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>&  ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0 \<rightarrow> Trans_stm0_core'\<cdot>NID_s0_stm0))))))
	  \<box>
	  (n = NID_s0_stm0) \<^bold>& ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>;  (enter_s2_stm0 \<rightarrow> Trans_stm0_core'\<cdot>NID_s2_stm0))))))
	 ))
	   \<close>



lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Trans.SSTOP.unfold ex1_m' non_terminating_is_empty_ticks_of)

lemma prefix_Skip_no_initial_tick : \<open> (a\<rightarrow> Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)

lemma SSTOP_refine:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (meson SSTOP.simps assms interrupt_ref)



lemma Trans_stm0_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm0\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm0.simps])
  (* Normalisation *)
  apply  (simp add: Det_assoc)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)


  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
 
  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )

  (*The line below to discharge the guard is not needed? Because the last choice is always true*)
  (*using atLeast0AtMost apply auto[1]*)
 

    
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )

   apply (rule SSTOP_refine)
   apply (rule eat_lemma)
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
 (* the above 5 steps equivalent to one line :
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I) *)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
    apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)

  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
   apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  oops



lemma Trans_stm0_core_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm0_core\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm0_core.simps])
  (* Normalisation *)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )

  (*The line below to discharge the guard is not needed? Because the last choice is always true*)
  (*using atLeast0AtMost apply auto[1]*)
 

    
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )

   apply (rule SSTOP_refine)
   apply (rule eat_lemma)
   apply (rule SSTOP_refine)
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
 (* the above 5 steps equivalent to one line :
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I) *)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)
  done


lemma Trans_stm0_core'_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm0_core'\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm0_core'.simps])
  (* Normalisation *)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
  eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )

(*the guard can not be discharged*)
  nitpick
  oops

end
thm Trans.Trans_stm0_core_def
term "Trans.Trans_stm0_core"
end



