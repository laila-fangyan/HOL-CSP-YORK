
theory GA_Trans
  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo" "HOL-CSP_Proc-Omata.CompactificationSync"
          Guard
begin

\<comment> \<open>This version uses fixrec to model Trans of Gas Analysis\<close>

default_sort type


no_notation floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)

no_notation Cons  ("_ \<cdot>/ _" [66,65] 65)


definition "dot"    :: "['a \<Rightarrow> 'b, 'a, 'b process] \<Rightarrow> 'b process"
  where      "dot c
 a P \<equiv> Mprefix {c a} (\<lambda> x. P)"



syntax   "_dot"  :: "[id, logic, 'a process] => 'a process"
                                        ("(3(_\<^bold>._) /\<rightarrow> _)" [0,0,78] 78)

translations
 
  "_dot c p P"     \<rightleftharpoons> "CONST dot c p P"


subsection\<open>The bounded buffer processes definition\<close>

type_synonym Chem = nat
type_synonym Intensity = nat

	
	
datatype NIDS = 
	NID_i1  | 
	NID_GasDetected  | 
	NID_j1  | 
	NID_Reading  | 
	NID_Analysis  | 
	NID_NoGas 	
	
datatype Status = 
	noGas | 
	gasD	
	
datatype Angle = 
	Left | 
	Right | 
	Back | 
	Front

datatype GasSensor =
	c : "Chem" |
	i : "Intensity"



locale Trans =
  fixes goreq :: "Intensity \<times>Intensity \<Rightarrow> bool"

  fixes analysis :: "(GasSensor list) \<Rightarrow> Status"

  fixes location :: "(GasSensor list) \<Rightarrow> Angle"

  fixes intensity :: "(GasSensor list) \<Rightarrow> Intensity"

  fixes angle :: "nat \<Rightarrow> Angle"

  fixes thr:: "Intensity"

begin


\<comment> \<open>Channel Declaration\<close>
datatype trans_event =  
"share" |
\<comment> \<open>internal_channel\<close>
"internal__chan" "NIDS" |
\<comment> \<open>flowchannel\<close>
"interrupt" |
"exited" |
"exit" |
"terminate" |
\<comment> \<open>variable_channel\<close>
"get_sts" "Status" |
"set_sts" "Status" |
"get_gs" "(GasSensor list)" |
"set_gs" "(GasSensor list)" |
"get_ins" "Intensity" |
"set_ins" "Intensity" |
"get_anl" "Angle" |
"set_anl" "Angle" |
\<comment> \<open>event_channel\<close>
"gas_in" "(GasSensor list)" |
"gas_out" "(GasSensor list)" |
"resume_in" |
"resume_out" |
"turn_in" "Angle" |
"turn_out" "Angle" |
"stop_in" |
"stop_out" |
"gas__in" "NIDS \<times> (GasSensor list)" |
(*"gas__in" "NIDS \<Rightarrow> GasSensor list \<Rightarrow> trans_event"|
*)"resume__in" "NIDS" |
"turn__in" "NIDS \<times> Angle" |
"stop__in" "NIDS" |
\<comment> \<open>state_channel\<close>
"enter_i1" |
"enter_GasDetected" |
"enter_j1" |
"enter_Reading" |
"enter_Analysis" | 
"enter_NoGas"

definition trans :: "trans_event process"
  where  \<open>trans \<equiv> 
  get_sts\<^bold>?(sts) \<rightarrow> get_ins\<^bold>?(ins) \<rightarrow> 
  (
  (internal__chan\<^bold>.(NID_i1) \<rightarrow> ((set_gs\<^bold>![] \<rightarrow> SKIP) \<^bold>; (set_anl\<^bold>!Front \<rightarrow> SKIP))) \<^bold>; (enter_Reading  \<rightarrow> SKIP)

  \<box>
   ((internal__chan\<^bold>.(NID_NoGas ) \<rightarrow> SKIP)\<^bold>; (( (exit  \<rightarrow> SKIP))\<^bold>; ( ((exited  \<rightarrow> SKIP)\<^bold>; (enter_Reading  \<rightarrow> SKIP)))))
  \<box>
  ((sts = noGas) \<^bold>& (((internal__chan\<^bold>.(NID_Analysis ) \<rightarrow> SKIP)\<^bold>; (( (exit  \<rightarrow> SKIP))\<^bold>; ( ((exited  \<rightarrow> ( (resume_out \<rightarrow> SKIP)))\<^bold>; (enter_NoGas  \<rightarrow> SKIP)))))))
  \<box>
  ((sts = gasD) \<^bold>& (((internal__chan\<^bold>.(NID_Analysis) \<rightarrow> SKIP)\<^bold>; (( (exit \<rightarrow> SKIP))\<^bold>; ( ((exited \<rightarrow> SKIP)\<^bold>; (enter_GasDetected \<rightarrow> SKIP)))))))
  \<box>
  (goreq(ins,thr) \<^bold>& (((internal__chan\<^bold>.(NID_GasDetected) \<rightarrow> SKIP)\<^bold>; (( (exit \<rightarrow> SKIP))\<^bold>; ( ((exited \<rightarrow> ( (stop_out \<rightarrow> SKIP)))\<^bold>; (enter_j1 \<rightarrow> SKIP)))))))
  \<box>
  ((\<not>goreq(ins,thr)) \<^bold>& (((internal__chan\<^bold>.(NID_GasDetected) \<rightarrow> SKIP)\<^bold>; (( exit \<rightarrow> SKIP)\<^bold>; ( ((exited \<rightarrow> (( (get_gs\<^bold>?(gs) \<rightarrow> ((size(gs) > 0) \<^bold>&  (set_anl\<^bold>!location(gs) \<rightarrow> SKIP))))\<^bold>;  (get_anl\<^bold>?(anl) \<rightarrow> ( (turn_out\<^bold>!anl \<rightarrow> SKIP)))))\<^bold>; (enter_Reading \<rightarrow> SKIP)))))))
  \<box>

  ((interrupt \<rightarrow> (exit \<rightarrow> SKIP)) \<^bold>; (exited \<rightarrow> (terminate \<rightarrow> SKIP)))
  \<box>
  (terminate \<rightarrow> SKIP)
) \<close>
 (* \<box>
  (gas__in\<^bold>.(NID_Reading)\<^bold>?(gs) \<rightarrow> (set_gs\<^bold>!gs \<rightarrow> SKIP)) \<^bold>; ((exit  \<rightarrow> SKIP) \<^bold>; ( (exited  \<rightarrow> SKIP) \<^bold>; (enter_Analysis  \<rightarrow> SKIP)))  *)




lemma deadlock_free_trans : \<open>deadlock_free (trans)\<close>
proof (unfold deadlock_free_def DF_def)
  show \<open>(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow>  X) \<sqsubseteq>\<^sub>F\<^sub>Dtrans\<close>

  proof (induct arbitrary: L rule: fix_ind)
    show \<open>adm (\<lambda>a. \<forall>L. a \<sqsubseteq>\<^sub>F\<^sub>D BBuf\<cdot>(length L)\<cdot>L)\<close> by (simp add: monofunI)
  next
    show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D BBuf\<cdot>(length L)\<cdot>L\<close> for L by simp
  next
    fix X L assume hyp : \<open>X \<sqsubseteq>\<^sub>F\<^sub>D BBuf\<cdot>(length L)\<cdot>L\<close> for L
    show \<open>(\<Lambda> X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D BBuf\<cdot>(length L)\<cdot>L\<close>
    proof (subst beta_cfun)
      show \<open>cont (\<lambda>X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<close> by simp
    next
      show \<open>\<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D BBuf\<cdot>(length L)\<cdot>L\<close>
        apply (subst BBuf.unfold)
        apply simp
      proof -
        consider \<open>L = []\<close> \<open>length L < maxbuff\<close> | \<open>L \<noteq> []\<close> \<open>length L < maxbuff\<close>
        | \<open>L \<noteq> []\<close> \<open>\<not> length L < maxbuff\<close> by auto \<comment> \<open>we use @{thm maxbuff_g0} here\<close>
        thus \<open>\<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D
             (length L < maxbuff) \<^bold>& (input\<^bold>?x \<rightarrow> BBuf\<cdot>(Suc (length L))\<cdot>(L @ [x])) \<box>
             (L \<noteq> []) \<^bold>& (output\<^bold>!hd L \<rightarrow> BBuf\<cdot>(length L - Suc 0)\<cdot>(tl L))\<close>
          (is \<open>\<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D ?P\<close>)
        proof cases
          show \<open>L = [] \<Longrightarrow> length L < maxbuff \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D ?P\<close>
            apply (simp add: Det_STOP)
            apply (simp add: read_def)
            apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD])
              apply simp_all
            by (rule hyp[of \<open>[_]\<close>, simplified])
        next
          show \<open>L \<noteq> [] \<Longrightarrow> length L < maxbuff \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D ?P\<close>
            apply simp
            apply (subst Ndet_id[symmetric])
            apply (rule Ndet_trans_Det_FD)

             apply (unfold read_def)
             apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD]; simp)
             apply (metis hyp length_append_singleton)

            apply (unfold write_def)
            apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD]; simp)
            by (metis One_nat_def hyp length_tl)
        next
          show \<open>L \<noteq> [] \<Longrightarrow> \<not> length L < maxbuff \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D ?P\<close>
            apply (simp add: Det_commute[of STOP, simplified Det_STOP])
            apply (unfold write_def)
            apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD]; simp)
            by (metis One_nat_def hyp length_tl)
        qed
      qed
    qed
  qed
qed



end


end