theory circus_theory_example1_add_s2_ddl
	  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation circus_theory_example1_ddlf
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
	NID_s1_stm0 |
	NID_s2_stm0
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



fixrec Trans_ex1  :: "NIDS_stm0 \<rightarrow> trans_event process"
  where \<open>Trans_ex1\<cdot>n = 

    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s1_stm0)))))
 \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((c__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s2_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s2_stm0)))))
	  \<box>
	  (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ( (exit_stm0 \<rightarrow> Skip))  \<^bold>; ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0)))



	((((( (n = NID_i0_stm0) \<^bold>& ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Skip))
	  \<box>
	 (n = NID_s0_stm0) \<^bold>&  ((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip)\<^bold>; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow> Skip))))))
	  \<box>
	 (n = NID_s1_stm0) \<^bold>& ((b__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip)\<^bold>; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip))\<^bold>; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip))\<^bold>; Trans_stm0\<cdot>n)
	  \<box>
	  (((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))
\<close>

(*
fixrec Trans_ex1  :: "NIDS_stm0 \<rightarrow> trans_event process"
  where \<open>Trans_ex1\<cdot>n = 

    (n = NID_i0_stm0) \<^bold>&  ((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip)\<^bold>; (enter_s0_stm0 \<rightarrow> Trans_ex1\<cdot>NID_s0_stm0))
	  \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((a__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s1_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s1_stm0)))))

 \<box>
	  ((n = NID_s0_stm0) \<^bold>& (((c__in\<^bold>.NID_s0_stm0 \<rightarrow> Skip) \<^bold>;( (exit_stm0 \<rightarrow> Skip))\<^bold>;  ((exited_stm0 \<rightarrow> Skip)\<^bold>; (enter_s2_stm0 \<rightarrow>  Trans_ex1\<cdot>NID_s2_stm0)))))


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
lemma skip_seq: "(a \<rightarrow> Skip) \<^bold>; b\<rightarrow>P = a \<rightarrow>b\<rightarrow> P"
  by (simp add: write0_Seq)




(*Trans_stm0 = 
	(((((((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))
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
end
  find_theorems "?P \<box> ?Q" "?P\<^bold>;?R"
lemma \<open>(P \<box> Q)\<^bold>;R = (P\<^bold>;R) \<box> (Q\<^bold>;R)\<close>

end



