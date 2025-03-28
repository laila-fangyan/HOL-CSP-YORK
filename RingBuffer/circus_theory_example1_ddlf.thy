theory circus_theory_example1_ddlf
	  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation
begin


lemma Guard_seq: "(b \<^bold>& P) \<^bold>; Q = b \<^bold>& (P \<^bold>; Q)"
  by (simp add: Guard_def)


default_sort type


no_notation floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)

no_notation Cons  ("_ \<cdot>/ _" [66,65] 65)

term "write"

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
	NID_s1_stm0
instantiation NIDS_stm0 :: discrete_cpo
begin

definition below_NIDS_def:
  "(x::NIDS_stm0) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_def)

end

(*instantiation NIDS_stm0 :: discrete_cpo*)

locale Trans_ex1 = 
 fixes d :: nat
begin
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

fixrec  SSTOP ::"trans_event process" and
Trans_ex1  :: "NIDS_stm0 \<rightarrow> trans_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Trans_ex1\<cdot>n = 
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))))
\<close>

lemma [simp]: "(SSTOP \<triangle> Q) \<^bold>; R = SSTOP \<triangle> (Q \<^bold>; R)"
  sorry

lemma [simp]: "SSTOP \<^bold>; P = SSTOP"
  by (meson deadlock_free_write0_iff ex_Skip non_deadlock_free_SKIP)

lemma SSTOP_refine:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P"
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D SSTOP \<triangle> P"
  by (meson deadlock_free_write0_iff ex_Skip non_deadlock_free_SKIP)


lemma Trans_ddlf:
  \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n) \<close>
  apply (rule df_step_param_intro[OF Trans_ex1.simps])
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)
  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
   apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step SSTOP_refine)
  using NIDS_stm0.exhaust atLeast0_atMost_Suc apply auto[1]
  done


method deadlock_free_trans uses P_def assms=
  (rule df_step_param_intro[OF P_def]
,simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
  , simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step SSTOP_refine
, insert NIDS_stm0.exhaust atLeast0_atMost_Suc , auto 
)


lemma Trans_ddlf_a:
 \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n) \<close>
  by (deadlock_free_trans P_def: Trans_ex1.simps)


thm Trans_ex1.simps

method normalization uses P_def =
  (subst P_def
  , simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

lemma trans_norm:
  assumes P_def: \<open> \<And>i. Trans_ex1\<cdot>i =  (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>;  ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s1_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; (SSTOP \<triangle>  (exit_stm0 \<rightarrow> Skip))  \<^bold>; ( SSTOP \<triangle>((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))))\<close>
  shows
 \<open>Trans_ex1\<cdot>i =  \<box>i\<in>{0..Suc (Suc 0)}.
            (if i \<le> Suc 0 then if i = 0 then n = NID_i0_stm0 else n = NID_s0_stm0 else n = NID_s1_stm0) \<^bold>&
            (if i \<le> Suc 0
             then if i = 0 then internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)
                  else a__in\<^bold>.NID_s0_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> SSTOP \<triangle> (exited_stm0 \<rightarrow> enter_s1_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s1_stm0))
             else b__in\<^bold>.NID_s1_stm0 \<rightarrow> SSTOP \<triangle> (exit_stm0 \<rightarrow> SSTOP \<triangle> (exited_stm0 \<rightarrow> enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)))  \<close>
 
  by (normalization P_def: P_def)



method deadlock_free_trans_step2 uses P_def assms=
  (rule df_step_param_intro[OF P_def]
,simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step SSTOP_refine
, insert NIDS_stm0.exhaust atLeast0_atMost_Suc , auto 
)


lemma Trans_ex1_step2_df_a: 
  assumes P_def: \<open>\<And> i. Trans_ex1\<cdot>i  = \<box>i\<in>{0..Suc (Suc 0)}.
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


(* Trans_stm0 = 	(((((((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))
	  \<box>
	  ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s1_stm0 \<rightarrow> Skip))))))
	  \<box>
	  ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip));; Trans_stm0)
	  \<box>
	  (((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))*)


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


(* this version has no interrupt but skip at the end
fixrec Trans_ex1  :: "NIDS_stm0 \<rightarrow> trans_event process"
  where \<open>Trans_ex1\<cdot>n = 

    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s1_stm0)))))

	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ( (exit_stm0 \<rightarrow> Skip))  \<^bold>; ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)))
	  \<box>
	  (share \<rightarrow> Skip)
	  \<box>
	  ((interrupt_stm0 \<rightarrow>  (exit_stm0 \<rightarrow> Skip))\<^bold>;  (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip)))
	  \<box>
	  (terminate \<rightarrow> Skip)
\<close>
*)
end

end



