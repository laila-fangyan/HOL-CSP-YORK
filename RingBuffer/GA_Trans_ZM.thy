(*<*)
\<comment>\<open> **********************************************************************************
 * This file models the transitions of GasAnalysis in HOL-CSP based 
 * the RoboChart Circus semantics.
 * 
 * A modification of adding the state variable 'state' is made so that 
 * the model is more Z-Machine style.
 * 
 * Date: 12-10-2024
 *************************************************************************************\<close>
(*>*)

theory GA_Trans_ZM
  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation
begin

\<comment> \<open>This version uses fixrec to model Trans of Gas Analysis\<close>

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

instantiation NIDS :: discrete_cpo
begin

definition below_NIDS_def:
  "(x::NIDS) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_def)

end


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
"gas__in" " (GasSensor list)" | (*gas__in type changed to GasSensor List, the NID is hidden because 1) the source node is explicit now, 2) the multi-prefix is not implemented, thus 'gas__in\<^bold>.(NID_Reading)\<^bold>?(gs)' is not supported*)
(*"gas__in" "NIDS \<times> (GasSensor list)" |*)
(*"gas__in" "NIDS \<Rightarrow> GasSensor list \<Rightarrow> trans_event"|
*)
"resume__in" "NIDS" |
"turn__in" "NIDS \<times> Angle" |
"stop__in" "NIDS" |
\<comment> \<open>state_channel\<close>
"enter_i1" |
"enter_GasDetected" |
"enter_j1" |
"enter_Reading" |
"enter_Analysis" | 
"enter_NoGas"


find_theorems GlobalDet
find_theorems " ?P \<box> ?Q"
thm Global_Deterministic_Choice.GlobalDet_unit

lemma Push_in_prefix : \<open>a \<rightarrow> (P \<box> Q) = (a \<rightarrow> P) \<box> (a \<rightarrow> Q)\<close>
  sorry

lemma skip_seq: "(a \<rightarrow> Skip) \<^bold>; P = a \<rightarrow> P"
  by (simp add: write0_Seq)


(*
fixrec Trans' :: "NIDS \<rightarrow> trans_event process"
  where  \<open>Trans'\<cdot>n =
  get_sts\<^bold>?(sts) \<rightarrow> get_ins\<^bold>?(ins) \<rightarrow> 
  (
  (n = NID_i1) \<^bold>& ((internal__chan\<^bold>.(NID_i1) \<rightarrow> ((set_gs\<^bold>![] \<rightarrow> Skip) \<^bold>; (set_anl\<^bold>!Front \<rightarrow> Skip))) \<^bold>; (enter_Reading  \<rightarrow> Trans'\<cdot>NID_Reading))

  \<box>
  (n = NID_NoGas) \<^bold>&  ((internal__chan\<^bold>.(NID_NoGas ) \<rightarrow> Skip) \<^bold>; ((exit  \<rightarrow> Skip)\<^bold>; ( ((exited  \<rightarrow> Skip)\<^bold>; (enter_Reading  \<rightarrow> Trans'\<cdot>NID_Reading)))))
\<box>
  ((n = NID_Analysis) \<and> (sts = noGas)) \<^bold>& ((((internal__chan\<^bold>.(NID_Analysis ) \<rightarrow> Skip)\<^bold>; (( (exit  \<rightarrow> Skip))\<^bold>; ( ((exited  \<rightarrow> ( resume_out \<rightarrow> Skip) ) \<^bold>; (enter_NoGas  \<rightarrow>  Trans'\<cdot>NID_NoGas)))))))
 ) \<close>



declare Trans'.simps [simp del]

term dot

ML \<open>
@{term "internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip"}
\<close>

lemma "internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip \<^bold>; exit \<rightarrow> exited \<rightarrow> resume_out \<rightarrow> enter_NoGas \<rightarrow> Trans'\<cdot>NID_NoGas = undefined"
  oops

lemma "deadlock_free (Trans'\<cdot>n)"
  apply (rule df_step_intro[OF Trans'.simps])  
  apply (simp add: biextchoic_normalization bi_extchoice_norm read_Seq write_Seq write0_Seq)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  thm read_proving_Mndetprefix_UNIV_ref
  apply (rule read_proving_Mndetprefix_UNIV_ref)
    apply (meson Trans.trans_event.inject(2) inj_onI)
   apply (simp)
  apply (rule eat_read_lemma)
   apply (simp add: inj_on_def)
  thm generalized_refine_guarded_extchoice
    apply (rule_tac generalized_refine_guarded_extchoice_star)
  thm   prefix_proving_Mndetprefix_UNIV_ref(3) eat_lemma no_step_refine 
             binops_proving_Mndetprefix_ref ndet_prefix_ext_choice Guard_def
  oops (*proof failed because some transitions are missing from Trans*)

lemma "Trans'\<cdot>n = a"
  apply (subst Trans'.simps)
  apply (simp del: Trans'.simps add: bi_extchoice_norm biextchoic_normalization Guard_seq)

  oops


find_theorems Trans'

term "g \<^bold>& (a \<rightarrow> Skip) \<^bold>; b \<rightarrow> P" (* \<^bold>&  84*) (* \<^bold>; 74*) (* \<^bold>\<rightarrow> 77*) (* \<^bold>\<box> 82*)

term "g \<^bold>& ( (a \<rightarrow> Skip) \<^bold>; b \<rightarrow> P)"

lemma deadlock_free_Trans' : \<open>deadlock_free (Trans'\<cdot>n)\<close>
proof (unfold deadlock_free_def DF_def)
  show \<open>(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow>  X) \<sqsubseteq>\<^sub>F\<^sub>D Trans'\<cdot>n\<close>
  
  proof (induct arbitrary: n rule: fix_ind)
    show \<open> adm (\<lambda>a. \<forall>n. a \<sqsubseteq>\<^sub>F\<^sub>D Trans'\<cdot>n)\<close> sorry
  next
    show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Trans'\<cdot>n\<close> for n sorry
  next
    fix X n assume hyp : \<open>X \<sqsubseteq>\<^sub>F\<^sub>D Trans'\<cdot>n\<close> for n
    show \<open>(\<Lambda> X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D Trans'\<cdot>n\<close>
    proof (subst beta_cfun)
      show \<open>cont (\<lambda>X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<close> by simp
    next
        show \<open>\<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D Trans'\<cdot>n\<close>
          apply (subst Trans'.unfold)
        proof -
        consider \<open>n = NID_i1\<close> | \<open>n = NID_NoGas\<close> | \<open>n = NID_Analysis\<close> \<open>sts = noGas\<close> | 
                 \<open>n = NID_Analysis\<close> \<open> sts = GasD \<close> | \<open>n = NID_GasDetected \<close> \<open> goreq(ins,thr)\<close>
                 \<open>n = NID_GasDetected\<close> \<open> \<not>goreq(ins,thr) \<close>   | \<open>n = NID_Reading \<close>  
      
        proof cases
          assumes P_def:  \<open>P = Trans'\<cdot>NID_i1\<close>
          show \<open>n = NID_i1 \<Longrightarrow> deadlock_free Trans'\<cdot>n \<close>
             apply (deadlock_free P_def: Trans'\<cdot>n)


          show \<open>n = NID_i1 \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>
 
            apply (simp add: Det_STOP)
            apply (simp add: read_def)
            apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD])
              apply simp_all
            by (rule hyp[of \<open>[_]\<close>, simplified])
        next
           show \<open>n = NID_NoGas \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans'\<cdot>n \<close>

        next
          show \<open>n = NID_Analysis \<Longrightarrow> sts = noGas \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans'\<cdot>n \<close>

        next
          show \<open>n = NID_Analysis \<Longrightarrow> sts = GasD \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans'\<cdot>n \<close>
        next
          show \<open>n = NID_GasDetected \<Longrightarrow>  goreq(ins,thr) \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans'\<cdot>n \<close>
        next
          show \<open>n = NID_GasDetected \<Longrightarrow>  \<not>goreq(ins,thr) = NID_NoGas \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans'\<cdot>n \<close>
        next
          show \<open>n = NID_Reading  \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans'\<cdot>n \<close>
       
         qed
      qed
    qed
  qed
qed

corollary \<open>deadlock_free (Trans'\<cdot>NID_i1)\<close>
  by (metis deadlock_free_Trans' list.size(3))

lemma 
  assumes P_def: \<open>P = (Trans\<cdot>n)\<close>
  shows \<open>deadlock_free (Trans\<cdot>n)\<close>
  by (deadlock_free P_def: P_def)

lemma "(Trans'\<cdot>n) = undefined"
  apply (subst Trans.Trans.unfold)
  


lemma deadlock_free_Trans : \<open>deadlock_free (Trans'\<cdot>n)\<close>
proof (unfold deadlock_free_def DF_def)
  show \<open>(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow>  X) \<sqsubseteq>\<^sub>F\<^sub>D Trans\<cdot>n\<close>
  
  proof (induct arbitrary: n rule: fix_ind)
    show \<open> adm (\<lambda>a. \<forall>n. a \<sqsubseteq>\<^sub>F\<^sub>D Trans\<cdot>n)\<close> sorry
  next
    show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Trans\<cdot>n\<close> for n sorry
  next
    fix X n assume hyp : \<open>X \<sqsubseteq>\<^sub>F\<^sub>D Trans\<cdot>n\<close> for n
    show \<open>(\<Lambda> X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D Trans\<cdot>n\<close>
    proof (subst beta_cfun)
      show \<open>cont (\<lambda>X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<close> by simp
    next
        show \<open>\<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D Trans\<cdot>n\<close>
        apply (subst Trans.unfold)
      

      proof -
        consider \<open>n = NID_i1\<close> | \<open>n = NID_NoGas\<close> | \<open>n = NID_Analysis\<close> \<open>sts = noGas\<close> | 
                 \<open>n = NID_Analysis\<close> \<open> sts = GasD \<close> | \<open>n = NID_GasDetected \<close> \<open> goreq(ins,thr)\<close>
                 \<open>n = NID_GasDetected\<close> \<open> \<not>goreq(ins,thr) \<close>   | \<open>n = NID_Reading \<close>  
      
        proof cases
          assumes P_def:  \<open>P = Trans\<cdot>NID_i1\<close>
          show \<open>n = NID_i1 \<Longrightarrow> deadlock_free Trans\<cdot>n \<close>
             apply (deadlock_free P_def: Trans\<cdot>n)


          show \<open>n = NID_i1 \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>
 
            apply (simp add: Det_STOP)
            apply (simp add: read_def)
            apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD])
              apply simp_all
            by (rule hyp[of \<open>[_]\<close>, simplified])
        next
           show \<open>n = NID_NoGas \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>

        next
          show \<open>n = NID_Analysis \<Longrightarrow> sts = noGas \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>

        next
          show \<open>n = NID_Analysis \<Longrightarrow> sts = GasD \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>
        next
          show \<open>n = NID_GasDetected \<Longrightarrow>  goreq(ins,thr) \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>
        next
          show \<open>n = NID_GasDetected \<Longrightarrow>  \<not>goreq(ins,thr) = NID_NoGas \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>
        next
          show \<open>n = NID_Reading  \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D  Trans\<cdot>n \<close>
       
         qed
      qed
    qed
  qed
qed

corollary \<open>deadlock_free (Trans'\<cdot>NID_i1)\<close>
  by (metis deadlock_free_Trans list.size(3))


*)

(*the complete version of Trans*)

fixrec Trans :: "NIDS \<rightarrow> trans_event process"
  where  \<open>Trans\<cdot>n =
  get_sts\<^bold>?(sts) \<rightarrow> get_ins\<^bold>?(ins) \<rightarrow> 
  (
  (n = NID_i1) \<^bold>& ((internal__chan\<^bold>.(NID_i1) \<rightarrow> ((set_gs\<^bold>![] \<rightarrow> Skip) \<^bold>; (set_anl\<^bold>!Front \<rightarrow> Skip))) \<^bold>; (enter_Reading  \<rightarrow> Trans\<cdot>NID_Reading))

  \<box>
  (n = NID_NoGas) \<^bold>&  ((internal__chan\<^bold>.(NID_NoGas ) \<rightarrow> Skip)\<^bold>; (( (exit  \<rightarrow> Skip))\<^bold>; ( ((exited  \<rightarrow> Skip)\<^bold>; (enter_Reading  \<rightarrow> Trans\<cdot>NID_Reading)))))
  \<box>
  (((n = NID_Analysis) \<and> sts = noGas) \<^bold>& (((internal__chan\<^bold>.(NID_Analysis ) \<rightarrow> Skip)\<^bold>; (( (exit  \<rightarrow> Skip))\<^bold>; ( ((exited  \<rightarrow> ( (resume_out \<rightarrow> Skip)))\<^bold>; (enter_NoGas  \<rightarrow>  Trans\<cdot>NID_NoGas)))))))
  \<box>
  (((n = NID_Analysis) \<and> sts = gasD) \<^bold>& (((internal__chan\<^bold>.(NID_Analysis) \<rightarrow> Skip)\<^bold>; (( (exit \<rightarrow> Skip))\<^bold>; ( ((exited \<rightarrow> Skip)\<^bold>; (enter_GasDetected \<rightarrow> Trans\<cdot>NID_GasDetected   )))))))
  \<box>
 (((n = NID_GasDetected) \<and> goreq(ins,thr)) \<^bold>& (((internal__chan\<^bold>.(NID_GasDetected) \<rightarrow> Skip)\<^bold>; (( (exit \<rightarrow> Skip))\<^bold>; ( ((exited \<rightarrow> ( (stop_out \<rightarrow> Skip)))\<^bold>; (enter_j1 \<rightarrow> Trans\<cdot>NID_j1 )))))))
  \<box>
  (((n = NID_GasDetected) \<and> \<not>goreq(ins,thr)) \<^bold>& ( (((internal__chan\<^bold>.(NID_GasDetected) \<rightarrow> Skip)\<^bold>; (( exit \<rightarrow> Skip)\<^bold>; ( ((exited \<rightarrow> (( (get_gs\<^bold>?(gs) \<rightarrow> ((size(gs) > 0) \<^bold>&  (set_anl\<^bold>!location(gs) \<rightarrow> Skip)))) \<^bold>;  (get_anl\<^bold>?(anl) \<rightarrow> ( (turn_out\<^bold>!anl \<rightarrow> Skip)))))\<^bold>; (enter_Reading \<rightarrow> Trans\<cdot>NID_Reading ))))))))
 \<box>
   ((n = NID_Reading) \<^bold>& ((gas__in\<^bold>?(gs) \<rightarrow> (set_gs\<^bold>!gs \<rightarrow> Skip)) \<^bold>; ((exit  \<rightarrow> Skip) \<^bold>; ( (exited  \<rightarrow> Skip) \<^bold>; (enter_Analysis  \<rightarrow>  Trans\<cdot>NID_Analysis)))))
 \<box>

  ((interrupt \<rightarrow> (exit \<rightarrow> Skip)) \<^bold>; (exited \<rightarrow> (terminate \<rightarrow> Skip)))
  \<box>
  (terminate \<rightarrow> Skip)
) \<close>

declare Trans.simps [simp del]

term dot

ML \<open>
@{term "internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip"}
\<close>

lemma "internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip \<^bold>; exit \<rightarrow> exited \<rightarrow> resume_out \<rightarrow> enter_NoGas \<rightarrow> Trans'\<cdot>NID_NoGas = undefined"
  oops

lemma "deadlock_free (Trans\<cdot>n)"
  apply (rule df_step_intro[OF Trans.simps])  
  apply (simp add: biextchoic_normalization bi_extchoice_norm biextchoic_normalization_nguard read_Seq write_Seq write0_Seq)(*same issue as ex11, guards after Suc0 are not discharged*)

  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  thm read_proving_Mndetprefix_UNIV_ref
  apply (rule read_proving_Mndetprefix_UNIV_ref)
    apply (meson Trans.trans_event.inject(2) inj_onI)
   apply (simp)
  apply (rule eat_read_lemma)
   apply (simp add: inj_on_def)
  thm generalized_refine_guarded_extchoice
  apply (rule_tac generalized_refine_guarded_extchoice_star)

  using atLeast0AtMost apply auto[1]
 
  oops
end


end