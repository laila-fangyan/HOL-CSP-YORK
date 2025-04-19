(*<*)
\<comment>\<open> **********************************************************************************
 * This file models the transitions of GasAnalysis in HOL-CSP based 
 * the RoboChart Circus semantics.
 * 
 * A modification of adding the state variable 'state' is made from the IsaCircus models.
 * 
 * Date: 12-10-2024
 *************************************************************************************\<close>
(*>*)

theory GA_Trans_HOL_CSP_param
  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation Law_Interrupt_Seq
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

"gas__in" " (GasSensor list)" | 
(*gas__in type changed to GasSensor List, the NID is hidden because 1) the source node is explicit now, 2) the multi-prefix is not implemented, thus 'gas__in\<^bold>.(NID_Reading)\<^bold>?(gs)' is not supported*)
(*"gas__in" "NIDS \<times> (GasSensor list)" |*)
(*"gas__in" "NIDS \<Rightarrow> GasSensor list \<Rightarrow> trans_event"| ?
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

lemma skip_seq: "(a \<rightarrow> Skip) \<^bold>; P = a \<rightarrow> P"
  by (simp add: write0_Seq)
fixrec SSTOP :: "trans_event process"        and
       Trans_GA :: "NIDS \<rightarrow> trans_event process"   and
       Trans_GA' :: "NIDS \<rightarrow> trans_event process"
where  
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Trans_GA\<cdot>n =
	(SSTOP \<triangle> (get_sts\<^bold>?sts \<rightarrow> (get_ins\<^bold>?ins \<rightarrow> (
    ((((((((
    (n=NID_i1) \<^bold>&  ((internal__chan\<^bold>.NID_i1 \<rightarrow> ((SSTOP \<triangle> (set_gs\<^bold>![] \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> (set_anl\<^bold>!Front \<rightarrow> Skip)))) \<^bold>; (enter_Reading \<rightarrow> Trans_GA\<cdot>NID_Reading))
	  )
	  \<box>
	  (n = NID_NoGas) \<^bold>& ((internal__chan\<^bold>.NID_NoGas \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> Skip) \<^bold>; (enter_Reading \<rightarrow> Trans_GA\<cdot>NID_Reading))))))
	  \<box>
	  (((n = NID_Analysis) \<and> (sts = noGas)) \<^bold>& (((internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (resume_out \<rightarrow> Skip))) \<^bold>; (enter_NoGas \<rightarrow> Trans_GA\<cdot>NID_NoGas))))))))
	  \<box>
	  (((n = NID_Analysis) \<and> (sts = gasD) )\<^bold>& (((internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> Skip) \<^bold>; (enter_GasDetected \<rightarrow> Trans_GA\<cdot>NID_GasDetected))))))))
	  \<box>
	  (((n = NID_GasDetected) \<and> goreq((ins,thr))) \<^bold>& (((internal__chan\<^bold>.NID_GasDetected \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (stop_out \<rightarrow> Skip))) \<^bold>; (enter_j1 \<rightarrow> Trans_GA\<cdot>NID_j1))))))))
	  \<box>
	  (((n = NID_GasDetected) \<and> (\<not>goreq((ins,thr)))) \<^bold>& (((internal__chan\<^bold>.NID_GasDetected \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> ((SSTOP \<triangle> (get_gs\<^bold>?gs \<rightarrow> ((size((gs)) > 0) \<^bold>& ((SSTOP \<triangle> (set_anl\<^bold>!location((gs)) \<rightarrow> Skip)))))) \<^bold>; (SSTOP \<triangle> (get_anl\<^bold>?anl \<rightarrow> (SSTOP \<triangle> (turn_out\<^bold>!anl \<rightarrow> Skip)))))) \<^bold>; (enter_Reading \<rightarrow> Trans_GA\<cdot>NID_Reading))))))))
	  \<box>
	  (share \<rightarrow> Trans_GA\<cdot>n)) )
	  \<box>
	  (((interrupt \<rightarrow> (SSTOP \<triangle> (exit \<rightarrow> Skip))) \<^bold>; (SSTOP \<triangle> (exited \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))))) \<close>
|
[simp del] :\<open>Trans_GA'\<cdot>n =
	(SSTOP \<triangle> (get_sts\<^bold>?sts \<rightarrow> (get_ins\<^bold>?ins \<rightarrow> (
    ((((((((
    (n=NID_i1) \<^bold>&  ((internal__chan\<^bold>.NID_i1 \<rightarrow> ((SSTOP \<triangle> (set_gs\<^bold>![] \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> (set_anl\<^bold>!Front \<rightarrow> Skip)))) \<^bold>; (enter_Reading \<rightarrow> Trans_GA'\<cdot>NID_Reading))
	  )
	  \<box>
	  (n = NID_NoGas) \<^bold>& ((internal__chan\<^bold>.NID_NoGas \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> Skip) \<^bold>; (enter_Reading \<rightarrow> Trans_GA'\<cdot>NID_Reading))))))
	  \<box>
	  (((n = NID_Analysis) \<and> (sts = noGas)) \<^bold>& (((internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (resume_out \<rightarrow> Skip))) \<^bold>; (enter_NoGas \<rightarrow> Trans_GA'\<cdot>NID_NoGas))))))))
	  \<box>
	  (((n = NID_Analysis) \<and> (sts = gasD) )\<^bold>& (((internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> Skip) \<^bold>; (enter_GasDetected \<rightarrow> Trans_GA'\<cdot>NID_GasDetected))))))))
	  \<box>
	  (((n = NID_GasDetected) \<and> goreq((ins,thr))) \<^bold>& (((internal__chan\<^bold>.NID_GasDetected \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (stop_out \<rightarrow> Skip))) \<^bold>; (enter_j1 \<rightarrow> Trans_GA'\<cdot>NID_j1))))))))
	  \<box>
	  (((n = NID_GasDetected) \<and> (\<not>goreq((ins,thr)))) \<^bold>& (((internal__chan\<^bold>.NID_GasDetected \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> ((SSTOP \<triangle> (get_gs\<^bold>?gs \<rightarrow> ((size((gs)) > 0) \<^bold>& ((SSTOP \<triangle> (set_anl\<^bold>!location((gs)) \<rightarrow> Skip)))))) \<^bold>; (SSTOP \<triangle> (get_anl\<^bold>?anl \<rightarrow> (SSTOP \<triangle> (turn_out\<^bold>!anl \<rightarrow> Skip)))))) \<^bold>; (enter_Reading \<rightarrow> Trans_GA'\<cdot>NID_Reading))))))))
	 ) )
	 )))) \<close>
(* this is the complete version, but with issue in gas__in\<^bold>.NID_Reading?gs
the version above removed the transition containing gas__in\<^bold>.NID_Reading?gs
[simp del] :\<open>Trans_GA\<cdot>n =
	(SSTOP \<triangle> (get_sts\<^bold>?sts \<rightarrow> (get_ins\<^bold>?ins \<rightarrow> (
    ((((((((
    (n=NID_i1) \<^bold>&  ((internal__chan\<^bold>.NID_i1 \<rightarrow> ((SSTOP \<triangle> (set_gs\<^bold>![] \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> (set_anl\<^bold>!Front \<rightarrow> Skip)))) \<^bold>; (enter_Reading \<rightarrow> Trans_GA\<cdot>NID_Reading))
	  \<box>
	  (n = NID_Reading) \<^bold>& ((gas__in\<^bold>.NID_Reading?gs \<rightarrow> (SSTOP \<triangle> (set_gs\<^bold>!gs \<rightarrow> Skip))) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> Skip) \<^bold>; (enter_Analysis \<rightarrow> Trans_GA\<cdot>NID_Analysis))))))
	  \<box>
	  (n = NID_NoGas) \<^bold>& ((internal__chan\<^bold>.NID_NoGas \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> Skip) \<^bold>; (enter_Reading \<rightarrow> Trans_GA\<cdot>NID_Reading))))))
	  \<box>
	  (((n = NID_Analysis) \<and> (sts = noGas)) \<^bold>& (((internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (resume_out \<rightarrow> Skip))) \<^bold>; (enter_NoGas \<rightarrow> Trans_GA\<cdot>NID_NoGas))))))))
	  \<box>
	  (((n = NID_Analysis) \<and> (sts = gasD) )\<^bold>& (((internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> Skip) \<^bold>; (enter_GasDetected \<rightarrow> Trans_GA\<cdot>NID_GasDetected))))))))
	  \<box>
	  (((n = NID_GasDetected) \<and> goreq((ins,thr))) \<^bold>& (((internal__chan\<^bold>.NID_GasDetected \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (stop_out \<rightarrow> Skip))) \<^bold>; (enter_j1 \<rightarrow> Trans_GA\<cdot>NID_j1))))))))
	  \<box>
	  (((n = NID_GasDetected) \<and> (\<not>goreq((ins,thr)))) \<^bold>& (((internal__chan\<^bold>.NID_GasDetected \<rightarrow> Skip) \<^bold>; ((SSTOP \<triangle> (exit \<rightarrow> Skip)) \<^bold>; (SSTOP \<triangle> ((exited \<rightarrow> ((SSTOP \<triangle> (get_gs\<^bold>?gs \<rightarrow> ((size((gs)) > 0) \<^bold>& ((SSTOP \<triangle> (set_anl\<^bold>!location((gs)) \<rightarrow> Skip)))))) \<^bold>; (SSTOP \<triangle> (get_anl\<^bold>?anl \<rightarrow> (SSTOP \<triangle> (turn_out\<^bold>!anl \<rightarrow> Skip)))))) \<^bold>; (enter_Reading \<rightarrow> Trans_GA\<cdot>NID_Reading))))))))
	  \<box>
	  (share \<rightarrow> Trans_GA\<cdot>n)) )
	  \<box>
	  (((interrupt \<rightarrow> (SSTOP \<triangle> (exit \<rightarrow> Skip))) \<^bold>; (SSTOP \<triangle> (exited \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))))) \<close>
*)

term dot

ML \<open>
@{term "internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip"}
\<close>


(*2 lemmas below used as assumptions in non_terminating_Interrupt_Seq*)
lemma SSTOP_nonTerm: \<open>non_terminating SSTOP\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SSTOP.unfold ex1_m'
      non_terminating_is_empty_ticks_of)


lemma prefix_Skip_no_initial_tick : \<open> (a\<rightarrow> Skip)\<^sup>0 \<inter> range tick = {}\<close>
  by (simp add: image_iff initials_write0)


(*TO DO: this lemma is  to validate lemma "Trans_ex1_ddlf"*)
lemma SSTOP_refine:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P" (* and    \<open>P\<^sup>0 \<inter> range tick = {}\<close>*)
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (meson Trans.SSTOP.unfold assms interrupt_ref)

lemma SSTOP_refine_plus:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D  P" 
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D  ( SSTOP \<triangle> P)"
  by (metis GlobalNdet_iterations'_Mndetprefix SSTOP.unfold assms interrupt_ref)

lemma Trans_GA'_ddlf_manual:
 \<open>deadlock_free (\<sqinter> n \<in> UNIV. Trans_GA'\<cdot>n) \<close>
 apply (rule df_step_param_intro[OF Trans_GA'.simps])
  (* Normalisation *)
  apply (simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq )

  (*to remove the first SSTOP \<triangle>*)
  apply (rule SSTOP_refine_plus)
  (* Rewrite the goal to allow multiple events *)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )

  (*to remove the read prefix for shared variables*)
  apply (rule read_prefix_proving_Mndetprefix_ref    )
   apply (simp add: inj_def)
  apply (rule proc_plus_read_prefix_ref)
   apply (simp add: inj_on_def)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )
  (* Simplify away the events in the cases not inclucing interrupt *)
  (* apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step )*)

  (*discharge the guards*)
  using NIDS.exhaust Status.exhaust atLeast0_atMost_Suc apply auto[1]
 
  (* Simplify the  interrupt using non_terminating_Interrupt_Seq*)
    apply (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq GlobalNdet_refine_no_step SSTOP_refine eat_lemma write0_Seq)+
                                          
  oops

term "g \<^bold>& (a \<rightarrow> Skip) \<^bold>; b \<rightarrow> P" (* \<^bold>&  84*) (* \<^bold>; 74*) (* \<^bold>\<rightarrow> 77*) (* \<^bold>\<box> 82*)

term "g \<^bold>& ( (a \<rightarrow> Skip) \<^bold>; b \<rightarrow> P)"


method deadlock_free_trans uses P_def assms=
  (rule df_step_param_intro[OF P_def]
,simp add: bi_extchoice_norm  biextchoic_normalization  biextchoic_normalization_nguard_prefix read_Seq write_Seq write0_Seq
  , simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym]
, auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3)
 generalized_refine_guarded_extchoice_star eat_lemma no_step_refine generalized_refine_guarded_extchoice write_proving_Mndetprefix_UNIV_ref GlobalNdet_refine_no_step
,insert NIDS_stm0.exhaust atLeast0_atMost_Suc , auto 
, (simp add: SSTOP_nonTerm  prefix_Skip_no_initial_tick non_terminating_Interrupt_Seq GlobalNdet_refine_no_step SSTOP_refine' eat_lemma write0_Seq)+
)

(*
lemma deadlock_free_Trans_GA : \<open>deadlock_free (Trans_GA\<cdot>n)\<close>
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



lemma deadlock_free_Trans : \<open>deadlock_free (Trans_GA\<cdot>n)\<close>
proof (unfold deadlock_free_def DF_def)
  show \<open>(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow>  X) \<sqsubseteq>\<^sub>F\<^sub>D Trans_GA\<cdot>n\<close>
  
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


ML \<open>
@{term "internal__chan\<^bold>.NID_Analysis \<rightarrow> Skip"}
\<close>




end