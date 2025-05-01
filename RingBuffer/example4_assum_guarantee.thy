theory example4_assum_guarantee 
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

"enter_s1_stm4"  |"entered_s1_stm4"  |"interrupt_s1_stm4"  |"enteredL_s1_stm4"  |"enteredR_s1_stm4" 	

                              
 
locale Trans 
begin

fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              and
 
Trans_stm4 :: "NIDS_stm4 \<rightarrow> chan_event process"   and
 
Trans_stm4' :: "NIDS_stm4 \<rightarrow> chan_event process"  and
 
Trans_stm4_core :: "NIDS_stm4 \<rightarrow> chan_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close> |
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
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((( 
    (n = NID_i0_stm4) \<^bold>& ((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> (set_v1\<^bold>!1 \<rightarrow> Skip)))\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4'\<cdot>NID_s0_stm4))
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
	  (terminate \<rightarrow> Skip))))) \<close>



 |
[simp del] :\<open>Trans_stm4_core\<cdot>n = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((( 
    (n = NID_i0_stm4) \<^bold>& ((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> (set_v1\<^bold>!1 \<rightarrow> Skip)))\<^bold>;  (enter_s0_stm4 \<rightarrow>  Trans_stm4_core\<cdot>NID_s0_stm4))
	  \<box>
	   (n = NID_s0_stm4) \<^bold>& ((v1 \<ge> 1) \<^bold>& (((internal__stm4\<^bold>.NID_s0_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm4 \<rightarrow> Trans_stm4_core\<cdot>NID_s1_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((v1 < 1) \<^bold>& (((internal__stm4\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4_core\<cdot>NID_s0_stm4))))))))
	  \<box>
	   (n = NID_s1_stm4) \<^bold>& ((a__in\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4_core\<cdot>NID_s0_stm4))))))
	 ) )
	 ))) \<close>





lemma SSTOP_remove_seq: "SSTOP \<^bold>; P = SSTOP"
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Trans.SSTOP.unfold ex1_m' non_terminating_Seq non_terminating_is_empty_ticks_of)



(*2 lemmas below used as assumptions in non_terminating_Interrupt_Seq*)
lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Trans.SSTOP.unfold ex1_m' non_terminating_is_empty_ticks_of)

lemma prefix_Skip_no_initial_tick : \<open> (a\<rightarrow> Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)


lemma write_prefix_Skip_no_initial_tick : \<open>\<forall>a\<in>A .(c\<^bold>.a \<rightarrow>  Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: prefix_Skip_no_initial_tick write_is_write0)

lemma read_prefix_Skip_no_initial_tick : \<open> (c\<^bold>?a\<in>A \<rightarrow>  Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (smt (verit, best) Int_emptyI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(4) image_iff initials_Mprefix read_def)

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

  
(*this is a valid proof*)
lemma Trans_ex1_ddlf:
 (* assumes\<open> 1 \<le> v1 \<close>
  shows *)
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_stm4_core\<cdot>n)  \<close>
  (* Apply induction *)
  apply (rule df_step_param_intro[OF Trans_stm4_core.simps])
  (* Normalisation *)
  apply (simp add: guard_pushed_in bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
  apply (rule SSTOP_refine_plus)

  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  apply (rule read_proving_Mndetprefix_ref)
     apply (simp add: inj_def)

  (* Simplify away the events in the cases not inclucing interrupt *)
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )
  
      
      apply (simp add: atLeast0_atMost_Suc)
      defer
      defer
      (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
 
      apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq GlobalNdet_refine_no_step SSTOP_refine eat_lemma iso_tuple_UNIV_I)+

  oops



end
end



