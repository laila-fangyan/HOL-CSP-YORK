theory circus_theory_HOLCSP 
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


	
	
datatype NIDS_stm0_ex1 = 
	NID_i0_stm0_ex1 | 
	NID_s0_stm0_ex1 | 
	NID_s1_stm0_ex1 | 
	NID_s2_stm0_ex1 
instantiation NIDS_stm0_ex1 :: discrete_cpo
begin

definition below_NIDS_stm0_ex1_def:
  "(x::NIDS_stm0_ex1) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm0_ex1_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm0_ex1\<close>

"internal__stm0_ex1" "NIDS_stm0_ex1"  |	
\<comment> \<open>flowchannel_stmbd_stm0_ex1\<close>

"interrupt_stm0_ex1"  |"exited_stm0_ex1"  |"exit_stm0_ex1"  |	
\<comment> \<open>event_channel_stmbd_stm0_ex1\<close>

"a_in"  |"a_out"  |
"b_in"  |"b_out"  |
"c_in"  |"c_out"  |
"a__in" "NIDS_stm0_ex1"  |
"b__in" "NIDS_stm0_ex1"  |
"c__in" "NIDS_stm0_ex1"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0_ex1\<close>

"enter_i0_stm0_ex1"  |"interrupt_i0_stm0_ex1"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm0_ex1\<close>

"enter_s0_stm0_ex1"  |"entered_s0_stm0_ex1"  |"interrupt_s0_stm0_ex1"  |"enteredL_s0_stm0_ex1"  |"enteredR_s0_stm0_ex1"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm0_ex1\<close>

"enter_s1_stm0_ex1"  |"entered_s1_stm0_ex1"  |"interrupt_s1_stm0_ex1"  |"enteredL_s1_stm0_ex1"  |"enteredR_s1_stm0_ex1"  |	
\<comment> \<open>state_channel_in_stmbd_s2_stm0_ex1\<close>

"enter_s2_stm0_ex1"  |"entered_s2_stm0_ex1"  |"interrupt_s2_stm0_ex1"  |"enteredL_s2_stm0_ex1"  |"enteredR_s2_stm0_ex1" 	

                              
 
locale Trans =
fixes d :: nat
begin

fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              and
 
Trans_stm0_ex1 :: "NIDS_stm0_ex1 \<rightarrow> chan_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>|

[simp del] :\<open>Trans_stm0_ex1 = 
	((((((((internal__stm0_ex1\<^bold>.NID_i0_stm0_ex1 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0_ex1 \<rightarrow> Skip))
	  \<box>
	  ((a__in\<^bold>.NID_s0_stm0_ex1 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0_ex1 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm0_ex1 \<rightarrow> Skip))))))
	  \<box>
	  ((b__in\<^bold>.NID_s1_stm0_ex1 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0_ex1 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm0_ex1 \<rightarrow> Skip))))))
	  \<box>
	  ((c__in\<^bold>.NID_s0_stm0_ex1 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm0_ex1 \<rightarrow> Skip)\<^bold>;  (enter_s2_stm0_ex1 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip))\<^bold>;  Trans_stm0_ex1)
	  \<box>
	  (((interrupt_stm0_ex1 \<rightarrow> (SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm0_ex1 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))) \<close>

end
end



