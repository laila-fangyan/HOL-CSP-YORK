theory circus_theory_example2 
	  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation
begin



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

locale Trans_ex2 = 
 fixes c :: nat
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

"get_v1"  "int" |
"set_v1"  "int" |
"setL_v1" "int" |
"setR_v1" "int" |
	
\<comment> \<open>event_channel_stmbd_stm0\<close>

"a_in" |
"a_out" |

"a__in" "NIDS_stm0"|
	
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
"enteredR_s1_stm0" 



text\<open>this version is simplified by removing SSTOP \<triangle> and some () \<close>
fixrec Trans_ex2  :: "NIDS_stm0 \<rightarrow> trans_event process"
  where \<open>Trans_ex2\<cdot>n = 
 get_v1\<^bold>?v1 \<rightarrow>
 (
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex2\<cdot>NID_s0_stm0))
	  \<box>
	  (((n = NID_s0_stm0) \<and> (v1 \<ge> 1)) \<^bold>& (((internal__stm0\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex2\<cdot>NID_s1_stm0)))))
	  \<box>
	  (((n = NID_s1_stm0) \<and> (v1 < 1)) \<^bold>& (((internal__stm0\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ( (exit_stm0 \<rightarrow> Skip)\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex2\<cdot>NID_s0_stm0))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((a__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ( (exit_stm0 \<rightarrow> Skip))  \<^bold>; ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex2\<cdot>NID_s0_stm0)))
	  \<box>
	  (share \<rightarrow> Skip)
	  \<box>
	  ((interrupt_stm0 \<rightarrow>  (exit_stm0 \<rightarrow> Skip))\<^bold>;  (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip)))
	  \<box>
	  (terminate \<rightarrow> Skip))
\<close>

lemma "deadlock_free (Trans_ex2\<cdot>n)"
  apply (rule df_step_intro[OF Trans_ex2.simps])  
  apply (simp add: biextchoic_normalization bi_extchoice_norm biextchoic_normalization_nguard read_Seq write_Seq write0_Seq)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  oops

text\<open>simplified by removing SSTOP \<triangle> ,but  have all () kept\<close>
(*
fixrec Trans_ex2  :: "NIDS_stm0 \<rightarrow> trans_event process"
  where \<open>Trans_ex2\<cdot>n = 
 get_v1\<^bold>?v1 \<rightarrow>
 (((((
    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex2\<cdot>NID_s0_stm0))
	  \<box>
	  (((n = NID_s0_stm0) \<and> (v1 \<ge> 1)) \<^bold>& (((internal__stm0\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex2\<cdot>NID_s1_stm0))))))
	  \<box>
	  (((n = NID_s1_stm0) \<and> (v1 < 1)) \<^bold>& (((internal__stm0\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ( (exit_stm0 \<rightarrow> Skip)\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex2\<cdot>NID_s0_stm0)))))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((a__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ( (exit_stm0 \<rightarrow> Skip))  \<^bold>; ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex2\<cdot>NID_s0_stm0))))
	  \<box>
	  (share \<rightarrow> Skip))
	  \<box>
	  (((interrupt_stm0 \<rightarrow>  (exit_stm0 \<rightarrow> Skip))\<^bold>;  (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip)))
	  \<box>
	  (terminate \<rightarrow> Skip)))
\<close>
*)

text\<open>this version of Trans is with operator \<triangle> and ()\<close>
(*
fixrec Trans_ex2  :: "NIDS \<rightarrow> trans_event process"
  where \<open>Trans_ex2\<cdot>n = 
 get_v1\<^bold>?v1 \<rightarrow>
 (((((
    ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))
	  \<box>
	  ((v1 \<ge> 1) \<^bold>& (((internal__stm0\<^bold>.NID_s0_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s1_stm0 \<rightarrow> Skip))))))))
	  \<box>
	  ((v1 < 1) \<^bold>& (((internal__stm0\<^bold>.NID_s1_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))))))))
	  \<box>
	  ((a__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip))
	  \<box>
	  (((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))
\<close>
*)
end
end


