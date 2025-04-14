theory circus_theory_example1_ddlf
	  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete" "HOL-CSP.Process"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation Law_Interrupt_Seq
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

fixrec  SSTOP       :: "trans_event process"              and
        Trans_ex1   :: "NIDS_stm0 \<rightarrow> trans_event process" and
        Trans_ex1'  :: "NIDS_stm0 \<rightarrow> trans_event process" and
        Trans_ex1'' :: "NIDS_stm0 \<rightarrow> trans_event process" and
        Terminate    ::"trans_event process"              and
        Trans_ex1''' :: "NIDS_stm0 \<rightarrow> trans_event process"
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
	  ((share \<rightarrow> Skip)\<^bold>; Trans_ex1''\<cdot>n)
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


lemma \<open>(a\<rightarrow> P ) \<^bold>; Q = a \<rightarrow> (P \<^bold>; Q)\<close>
  by (simp add: write0_Seq)


lemma SSTOP_remove_seq: "SSTOP \<^bold>; P = SSTOP"
  by (metis Trans_ex1.SSTOP.unfold deadlock_free_implies_lifelock_free ex1_m' lifelock_free_is_non_terminating non_terminating_Seq)


(*2 lemmas below used as assumptions in non_terminating_Interrupt_Seq*)
lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Trans_ex1.SSTOP.unfold ex1_m' non_terminating_is_empty_ticks_of)

lemma prefix_Skip_no_initial_tick : \<open> (a\<rightarrow> Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)

lemma SSTOP_ddlf: 
  assumes P_def: \<open>SSTOP = share \<rightarrow> SSTOP\<close>
  shows \<open>deadlock_free SSTOP\<close>
  apply (rule df_step_intro[OF P_def])
  apply ( simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
  prefix_proving_Mndetprefix_UNIV_ref(3) eat_lemma no_step_refine 
             binops_proving_Mndetprefix_ref ndet_prefix_ext_choice Guard_def)
  done

(*this is not used*)
lemma SSTOP_refine:
  assumes "deadlock_free P" (* and    \<open>P\<^sup>0 \<inter> range tick = {}\<close>*)
  shows "deadlock_free ( SSTOP \<triangle> P)"
  oops

(*TO DO: this lemma needs to be proved first to validate lemma "Trans_ex1_ddlf"*)

lemma SSTOP_refine_generalized:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P" and "Q = a \<rightarrow> Q"
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  Q \<triangle> P"
proof (unfold refine_defs, safe)
  show \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t Y
  proof (induct t)
    from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P\<close> show \<open>([], Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> ([], Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
      apply (subst (asm) \<open>Q = a \<rightarrow> Q\<close>)
      apply (simp add: refine_defs write0_projs F_Interrupt GlobalNdet_iterations'_def F_GlobalNdet F_iterate_Mndetprefix_UNIV subset_iff)
      by (metis append_is_Nil_conv is_processT6_TR is_processT8 list.size(3) self_append_conv2)
  next
    fix e t Y assume hyp : \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    assume \<open>(e # t, Y) \<in> \<F> (Q \<triangle> P)\<close>
    hence \<open>(e # t, Y) \<in> \<F> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    then consider \<open>(e # t, Y) \<in> \<F> P\<close> | \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      by (auto simp add: Interrupt_write0 F_Det F_write0)
    thus \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    proof cases
      assume \<open>(e # t, Y) \<in> \<F> P\<close>
      with \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        by (simp add: refine_defs subset_iff)
    next
      assume \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      from this(2)[THEN hyp] have \<open>(t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> .
      thus \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        apply (auto simp add: \<open>e = ev a\<close> GlobalNdet_iterations'_def F_GlobalNdet F_iterate_Mndetprefix_UNIV)
        by (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.discI(1) tickFree_Cons_iff)
    qed
  qed
next
  show \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t
  proof (induct t)
    from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>[] \<in> \<D> (Q \<triangle> P) \<Longrightarrow> [] \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
      by (simp add: refine_defs subset_iff D_Interrupt GlobalNdet_iterations'_def D_GlobalNdet D_iterate_Mndetprefix_UNIV)
        (metis Nil_is_append_conv Nil_notin_D_Mprefix assms(2) write0_def)
  next
    fix e t assume hyp : \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    assume \<open>e # t \<in> \<D> (Q \<triangle> P)\<close>
    hence \<open>e # t \<in> \<D> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    hence \<open>e # t \<in> \<D> P \<or> t \<in> \<D> (Q \<triangle> P)\<close>
      by (auto simp add: D_Interrupt write0_projs)
    thus \<open>e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    proof (elim disjE)
      from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>e # t \<in> \<D> P \<Longrightarrow> e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        by (simp add: refine_defs subset_iff)
    next
      show \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        by (auto simp add: GlobalNdet_iterations'_def D_GlobalNdet D_iterate_Mndetprefix_UNIV dest!: hyp)
          (metis D_imp_front_tickFree \<open>e # t \<in> \<D> (Q \<triangle> P)\<close> append.left_neutral
            append_Cons front_tickFree_nonempty_append_imp is_processT7)
    qed
  qed
qed
   





lemma SSTOP_refine':
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (meson SSTOP_refine_generalized Trans_ex1.SSTOP.unfold assms)


(*TBC:  this proof uses SSTOP_refine'*)
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
  (*move the goal for guards to the last*)

  (*discharge the guards*)
  using NIDS_stm0.exhaust atLeast0_atMost_Suc apply auto[1]
    
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
   apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )

   apply (rule SSTOP_refine')
   apply (rule eat_lemma)
   apply (rule SSTOP_refine')
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
 (* the above 5 steps equivalent to :
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I) *)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I)
  done


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

   apply (rule SSTOP_refine')
   apply (rule eat_lemma)
   apply (rule SSTOP_refine')
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
 (* the above 5 steps equivalent to :
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I) *)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
  apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I)
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

   apply (rule SSTOP_refine')
   apply (rule eat_lemma)
   apply (rule SSTOP_refine')
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)
 (* the above 5 steps equivalent to :
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I) *)
  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
    apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I)
  oops
(*this is ddl and can not be proved*)



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
   apply (rule SSTOP_refine')
   apply (rule eat_lemma)
   apply (rule SSTOP_refine')
   apply (rule eat_lemma)+
  apply (simp add: GlobalNdet_refine_no_step)

 (* the above 5 steps equivalent to the next 2 lines:
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I) 
 apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I)
*)

  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
    apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I)

  apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq write0_Seq )
   apply (auto intro!: GlobalNdet_refine_no_step SSTOP_refine' eat_lemma iso_tuple_UNIV_I)
  apply (subst Terminate_def) 


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
  by (simp add: Guard_seq)
  

lemma Guard_seq_indexed:
  assumes "finite I" and "I \<noteq> {}"
  shows "(\<box> i\<in>I. G i \<^bold>& P i) \<^bold>; Q = (\<box> i\<in>I. G i \<^bold>& (P i \<^bold>; Q))"
  using assms
  oops


lemma norm_guarded_extchoice_seq_gen:
  assumes "finite I" and "I \<noteq> {}"
  shows "(\<box> i\<in>I. G i \<^bold>& P i) \<^bold>; Q = (\<box> i\<in>I. G i \<^bold>& (P i \<^bold>; Q))"
  oops

lemma Trans_ex1''_ddlf:
 assumes P_def: \<open>\<And> n. P n =  (Trans_ex1''\<cdot>n \<^bold>; SSTOP )\<close>
  shows \<open>deadlock_free( \<sqinter> n \<in> UNIV.  P n )\<close>
  apply (rule df_step_param_intro[OF P_def])
  apply (subst Trans_ex1''.simps)  

  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq)

  apply (simp add: norm_extchoice_seq_gen)

  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

(* do we need a generalized norm_extchoice_seq?*)
  oops

lemma Trans_ex1''_ddlf:
 assumes P_def: \<open>P n = \<sqinter> n \<in> UNIV. Trans_ex1''\<cdot>n \<^bold>; SSTOP \<close>
  shows \<open>deadlock_free  P \<close>
  apply (rule df_step_param_intro[OF P_def])
  oops




method deadlock_free_trans uses P_def assms=
  (rule df_step_param_intro[OF P_def]
,simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
  , simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step
,insert NIDS_stm0.exhaust atLeast0_atMost_Suc , auto 
, (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq GlobalNdet_refine_no_step SSTOP_refine eat_lemma write0_Seq)+
)


lemma Trans_ex1_ddlf_auto:
 \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_ex1\<cdot>n) \<close>
  by (deadlock_free_trans P_def: Trans_ex1.simps)


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
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step SSTOP_refine'
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



