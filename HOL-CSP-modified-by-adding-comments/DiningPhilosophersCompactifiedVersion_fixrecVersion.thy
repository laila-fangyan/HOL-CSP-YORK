(*<*)
\<comment>\<open> ********************************************************************
 * Project         : Proc-Omata - Using automata to reason on HOL-CSP processes
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Benoît Ballenghien
 *
 * This file       : Philosophers may dine, always ! - fixrec version
 *
 * Copyright (c) 2022 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)


chapter \<open> Can philosophers dine ? \<close>

theory DiningPhilosophersCompactifiedVersion_fixrecVersion
  imports "HOLCF-Library.Int_Discrete" CompactificationSync NormalizationProperties
begin


\<comment> \<open>TODO: prove that we may have a deadlock if we only have rphils\<close>


section \<open>Results concerning only our dining problem\<close>

subsection \<open>Preliminary lemmas for proof automation\<close>

lemma Suc_mod: \<open>n > 1 \<Longrightarrow> i \<noteq> Suc i mod n\<close>
  by (metis One_nat_def mod_Suc mod_if mod_mod_trivial n_not_Suc_n)

lemmas suc_mods = Suc_mod Suc_mod[symmetric]

lemma l_suc: \<open>n > 1 \<Longrightarrow> \<not> n \<le> Suc 0\<close>
  by simp 

lemma minus_suc: \<open>n > 0 \<Longrightarrow> n - Suc 0 \<noteq> n\<close>
  by linarith

declare Un_insert_right[simp del] Un_insert_left[simp del]

(*declare Mprefix_Un_distrib[simp]  is there an issue declaring this lemma simp ? *)



subsection \<open>Methods\<close> (* move this in an other file *)

default_sort type (* very important here *)

no_notation   floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)


method adm_prover = simp add: cont_fun monofunI

\<comment> \<open>With the lemma @{thm eval_nat_numeral} we don't need to have numeral_4_is_4 numeral_5_is_5 etc.\<close>
method base_k_steps_breaker = (simp_all add: eval_nat_numeral All_less_Suc, safe?)?

method show_norm_eq uses rec eps tau =
       (subst rec, simp add: eps tau write0_def Mprefix_Un_distrib Det_commute)+

method show_P_is_P_d for k::nat and f :: \<open>('\<sigma> \<Rightarrow> 'e process) \<rightarrow> '\<sigma> \<Rightarrow> 'e process\<close>
                      uses P_def P_rec P_dnorm_def P_dnorm_rec eps tau = (* TODO: see if we can automatically obtain fork_\<epsilon> fork_\<tau> from A_def *)
  rule FD_antisym, 
  subst P_def, induct rule: fix_ind_k_skip[where k = 1], simp, adm_prover, base_k_steps_breaker, ((auto split: prod.split)?)[1],
  (show_norm_eq rec: P_dnorm_rec eps: eps tau: tau)[1],
  (subst P_dnorm_def, induct rule: fix_ind_k_skip[where k = k and f = f], simp, adm_prover, base_k_steps_breaker),
  (show_norm_eq rec: P_rec eps: eps tau: tau)       



subsection\<open>1. The dining processes definition in HOL-CSP\<close>

locale DiningPhilosophers =
  
  fixes N :: nat
  assumes N_g1[simp] : \<open>N > 1\<close>  

begin

datatype dining_event  = picks  (phil: nat) (fork: nat)
  | putsdown (phil: nat) (fork: nat)

fixrec     RPHIL  :: \<open>int \<rightarrow> dining_event process\<close>
       and LPHIL0 :: \<open>dining_event process\<close>
       and FORK   :: \<open>int \<rightarrow> dining_event process\<close>
where 
   RPHIL_rec [simp del] :
   \<open>RPHIL\<cdot>j = (let i = nat j in (picks i i \<rightarrow> (picks i (i-1) \<rightarrow> (putsdown i (i-1) \<rightarrow> (putsdown i i \<rightarrow> RPHIL\<cdot>j)))))\<close>
 | LPHIL0_rec[simp del] :
   \<open>LPHIL0 = (picks 0 (N-1) \<rightarrow> (picks 0 0 \<rightarrow> (putsdown 0 0 \<rightarrow> (putsdown 0 (N-1) \<rightarrow> LPHIL0))))\<close>
 | FORK_rec  [simp del] :
   \<open>FORK\<cdot>j  = (let i = nat j in (picks i i \<rightarrow> (putsdown i i \<rightarrow> FORK\<cdot>j)) \<box>
                                (picks ((i+1) mod N) i \<rightarrow> (putsdown ((i+1) mod N) i \<rightarrow> FORK\<cdot>j)))\<close>


abbreviation \<open>PHILS n \<equiv> \<^bold>|\<^bold>|\<^bold>| P \<in># add_mset LPHIL0 (mset (map (\<lambda>i. RPHIL\<cdot>(int i)) [1..< n])). P\<close>
abbreviation \<open>FORKS n \<equiv> \<^bold>|\<^bold>|\<^bold>| P \<in># mset (map (\<lambda>i. FORK\<cdot>(int i)) [0..< n]). P\<close>
term " \<^bold>|\<^bold>|\<^bold>| P \<in># mset (map (\<lambda>i. FORK\<cdot>(int i)) [0..< n]). P"

abbreviation \<open>NPHILS \<equiv> PHILS N\<close>
abbreviation \<open>NFORKS \<equiv> FORKS N\<close>



corollary \<open>N = 3 \<Longrightarrow> NPHILS = LPHIL0 ||| RPHIL\<cdot>1 ||| RPHIL\<cdot>2\<close>
  by (simp add: eval_nat_numeral upt_rec Sync_assoc)


definition DINING :: \<open>dining_event process\<close>
  where \<open>DINING = (NFORKS || NPHILS)\<close>



subsection \<open>2. Translation into normal form - Proc-Omata\<close>

lemma N_g0[simp]: \<open>0 < N\<close> using N_g1 by linarith

lemmas N_pos_simps[simp] = suc_mods[OF N_g1] l_suc[OF N_g1] minus_suc[OF N_g0]



subsubsection \<open>2.1   \<^const>\<open>FORK\<close>, \<^const>\<open>LPHIL0\<close> and \<^const>\<open>RPHIL\<close> are normalizable\<close>

text \<open>2.1.1  Automata creation: Definition of one \<^emph>\<open>fork\<close> and one \<^emph>\<open>philosopher\<close> automata\<close>

type_synonym id\<^sub>f\<^sub>o\<^sub>r\<^sub>k = nat
type_synonym \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k  = nat
type_synonym id\<^sub>p\<^sub>h\<^sub>i\<^sub>l = nat
type_synonym \<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l  = nat


definition   fork_A :: \<open>id\<^sub>f\<^sub>o\<^sub>r\<^sub>k \<Rightarrow> (\<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k, dining_event) A\<^sub>d\<close> (\<open>A\<^sub>f\<close>)      
  where \<open>A\<^sub>f i \<equiv> recursive_constructor_A\<^sub>d
                [((0, picks i i),    \<lfloor>1\<rfloor>), ((0, picks ((i + 1) mod N) i),    \<lfloor>2\<rfloor>),
                 ((1, putsdown i i), \<lfloor>0\<rfloor>), ((2, putsdown ((i + 1) mod N) i), \<lfloor>0\<rfloor>)] 
                {} 
                {}
        \<close>


definition  rphil_A :: \<open>id\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> (\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l, dining_event) A\<^sub>d\<close> (\<open>A\<^sub>r\<^sub>p\<close>)
  where \<open>A\<^sub>r\<^sub>p i \<equiv> recursive_constructor_A\<^sub>d
                 [((0, picks i i),        \<lfloor>1\<rfloor>), ((1, picks i (i - 1)), \<lfloor>2\<rfloor>),
                  ((2, putsdown i (i-1)), \<lfloor>3\<rfloor>), ((3, putsdown i i),    \<lfloor>0\<rfloor>)] {} {}\<close>

definition lphil0_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l, dining_event) A\<^sub>d\<close> (\<open>A\<^sub>l\<^sub>p\<close>)
  where \<open>A\<^sub>l\<^sub>p \<equiv> recursive_constructor_A\<^sub>d
               [((0, picks 0 (N - 1)), \<lfloor>1\<rfloor>), ((1, picks 0 0),          \<lfloor>2\<rfloor>),
                ((2, putsdown 0 0),    \<lfloor>3\<rfloor>), ((3, putsdown 0 (N - 1)), \<lfloor>0\<rfloor>)] {} {}\<close>



text \<open>2.1.2 Turn Auotmata to Proc-Omata:  Definition and first properties of associated normal processes\<close>


definition fork_P_d :: \<open>id\<^sub>f\<^sub>o\<^sub>r\<^sub>k \<Rightarrow> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k \<Rightarrow> dining_event process\<close>  where \<open>fork_P_d  i \<equiv> P\<lbrakk>A\<^sub>f i\<rbrakk>\<^sub>d\<close>
definition rphil_P_d :: \<open>id\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> \<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> dining_event process\<close> where \<open>rphil_P_d i \<equiv> P\<lbrakk>A\<^sub>r\<^sub>p i\<rbrakk>\<^sub>d\<close>
definition lphil0_P_d :: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> dining_event process\<close>         where \<open>lphil0_P_d  \<equiv> P\<lbrakk>A\<^sub>l\<^sub>p\<rbrakk>\<^sub>d\<close>


(*? what are these lemmas for? *)
lemmas   fork_P_d_rec = P_d_rec[of \<open>A\<^sub>f _\<close>,  folded fork_P_d_def]
   and  rphil_P_d_rec = P_d_rec[of \<open>A\<^sub>r\<^sub>p _\<close>, folded rphil_P_d_def]
   and lphil0_P_d_rec = P_d_rec[of \<open>A\<^sub>l\<^sub>p\<close>,   folded lphil0_P_d_def]


\<comment> \<open>Enableness \<epsilon>\<close> (*why is this form?  *)
schematic_goal   fork_\<epsilon>: \<open>\<epsilon> (A\<^sub>f i) s = ?S\<close>
           and  rphil_\<epsilon>: \<open>\<epsilon> (A\<^sub>r\<^sub>p i) s = ?T\<close>
           and lphil0_\<epsilon>: \<open>\<epsilon> A\<^sub>l\<^sub>p s = ?U\<close>
  unfolding fork_A_def rphil_A_def lphil0_A_def by \<epsilon>_det_calc+

schematic_goal   fork_\<tau>: \<open>\<tau> (A\<^sub>f i) s = ?S\<close>
           and  rphil_\<tau>: \<open>\<tau> (A\<^sub>r\<^sub>p i) s = ?T\<close>
           and lphil0_\<tau>: \<open>\<tau> A\<^sub>l\<^sub>p s = ?U\<close>
  unfolding fork_A_def rphil_A_def lphil0_A_def by \<tau>_det_calc+



corollary   ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx: \<open>e \<in> \<epsilon> (A\<^sub>f i) s \<Longrightarrow> fork e = i\<close> 
      and  rphil_phil: \<open>e \<in> \<epsilon> (A\<^sub>r\<^sub>p i) s \<Longrightarrow> phil e = i\<close>
      and lphil0_phil: \<open>e \<in> \<epsilon> A\<^sub>l\<^sub>p s     \<Longrightarrow> phil e = 0\<close>
    (*sledgehammer
  apply (smt (verit, best) UnE dining_event.sel(3) dining_event.sel(4) emptyE fork_\<epsilon> insertE)
  apply (smt (verit, ccfv_SIG) dining_event.sel(1) dining_event.sel(2) empty_iff rphil_\<epsilon> singletonD)
  by (metis (no_types, lifting) DiningPhilosophers.lphil0_\<epsilon> DiningPhilosophers_axioms dining_event.sel(1) dining_event.sel(2) empty_iff singletonD)
*)
  by (auto simp add: fork_\<epsilon> rphil_\<epsilon> lphil0_\<epsilon> split: if_split_asm)



corollary ev_id\<^sub>p\<^sub>h\<^sub>i\<^sub>lx: \<open>i < n \<Longrightarrow> e \<in> \<epsilon> ((A\<^sub>l\<^sub>p # map A\<^sub>r\<^sub>p [1..< n]) ! i) s \<Longrightarrow> phil e = i\<close>
  (*sledgehammer
  by (metis add.commute less_diff_conv less_one linordered_semidom_class.add_diff_inverse lphil0_phil nth_Cons' nth_map_upt rphil_phil)
  *)
  by (cases \<open>i = 0\<close>; simp add: lphil0_phil rphil_phil) 


\<comment> \<open>independence\<close>
lemma indep_forks: \<open>i \<noteq> j \<Longrightarrow> \<epsilon> (A\<^sub>f i) s \<inter> \<epsilon> (A\<^sub>f j) s' = {}\<close>
  and indep_phils: \<open>i \<noteq> 0 \<Longrightarrow> \<epsilon> A\<^sub>l\<^sub>p s \<inter> \<epsilon> (A\<^sub>r\<^sub>p i) s' = {}\<close>
                   \<open>i \<noteq> j \<Longrightarrow> \<epsilon> (A\<^sub>r\<^sub>p i) s \<inter> \<epsilon> (A\<^sub>r\<^sub>p j) s' = {}\<close>
 (*sledgehammer
   apply (metis DiningPhilosophers.ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx DiningPhilosophers_axioms disjoint_iff_not_equal)
  using DiningPhilosophers.lphil0_phil DiningPhilosophers_axioms rphil_phil apply fastforce
  by (metis DiningPhilosophers.rphil_phil DiningPhilosophers_axioms disjoint_iff_not_equal)
*)
  using ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx lphil0_phil rphil_phil by (metis disjoint_iff_not_equal)+ 



text \<open>2.1.3 Manual proof of Equalities between HOL-CSP and Proc-Omata:   \<^const>\<open>FORK\<close>, \<^const>\<open>RPHIL\<close>, \<^const>\<open>LPHIL0\<close>
      and respectively \<^const>\<open>fork_P_d\<close>, \<^const>\<open>rphil_P_d\<close>, \<^const>\<open>lphil0_P_d\<close>\<close>

(* \<and> *)
lemma FORK_is_fork_P_d: \<open>FORK\<cdot>(int i) = fork_P_d i 0\<close>
  by (show_P_is_P_d 2 \<open>\<Lambda> X. P_d_step (\<epsilon> (A\<^sub>f i)) (\<tau> (A\<^sub>f i)) X\<close> P_def: FORK_def P_rec: FORK_rec
      P_dnorm_def: fork_P_d_def P_dnorm_rec: fork_P_d_rec eps: fork_\<epsilon> tau: fork_\<tau>)

lemma RPHIL_is_rphil_P_d: \<open>RPHIL\<cdot>(int i) = rphil_P_d i 0\<close>

  by (show_P_is_P_d 4 \<open>\<Lambda> X. P_d_step (\<epsilon> (A\<^sub>r\<^sub>p i)) (\<tau> (A\<^sub>r\<^sub>p i)) X\<close> P_def: RPHIL_def P_rec: RPHIL_rec
      P_dnorm_def: rphil_P_d_def P_dnorm_rec: rphil_P_d_rec eps: rphil_\<epsilon> tau: rphil_\<tau>)
     
 lemma LPHIL0_is_lphil0_P_d: \<open>LPHIL0 = lphil0_P_d 0\<close>
   by (show_P_is_P_d 4 \<open>\<Lambda> X. P_d_step (\<epsilon> A\<^sub>l\<^sub>p) (\<tau> A\<^sub>l\<^sub>p) X\<close> P_def: LPHIL0_def P_rec: LPHIL0_rec
       P_dnorm_def: lphil0_P_d_def P_dnorm_rec: lphil0_P_d_rec eps: lphil0_\<epsilon> tau: lphil0_\<tau>)



subsubsection  \<open>2.2  \<^const>\<open>FORKS\<close> is normalizable\<close>

text \<open>2.2.1 Automata: Definition of the all-forks automaton\<close>

type_synonym \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s = \<open>nat list\<close>


definition forks_A :: \<open>(\<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s, dining_event) A\<^sub>d\<close> (\<open>A\<^sub>F\<close>) where \<open>A\<^sub>F \<equiv> \<^sub>d\<Otimes>\<lbrakk>{}\<rbrakk> (map A\<^sub>f [0..<N])\<close>



text \<open>2.2.2 Proc-Omata: Definition and first properties of the associated normal process\<close>

definition forks_P_d:: \<open>\<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>forks_P_d \<equiv> P\<lbrakk>A\<^sub>F\<rbrakk>\<^sub>d\<close>


\<comment> \<open>Enableness \<epsilon>\<close>
\<comment> \<open>\<epsilon> for the entire set of forks is equivalent to the union of \<epsilon>  of each individual fork.\<close>
lemma forks_\<epsilon>: \<open>length fs = N \<Longrightarrow> \<epsilon> A\<^sub>F fs = (\<Union>i<N. \<epsilon> (A\<^sub>f i) (fs ! i))\<close>
  unfolding forks_A_def using N_g1 by (subst iterated_combine\<^sub>d_general_form_\<epsilon>) auto


\<comment> \<open>refinement forks_P_d is refined by NFORKS\<close>
text \<open>2.2.3  Equality between HOL-CSP and Proc-Omata: \<^const>\<open>NFORKS\<close> and \<^const>\<open>forks_P_d\<close>\<close>

lemma NFORKS_is_forks_P_d: \<open>NFORKS = forks_P_d (replicate N 0)\<close>
  unfolding forks_P_d_def forks_A_def
  apply (subst P_d_mset_compactification_Sync_upt_version)
  by (simp_all add: FORK_is_fork_P_d[unfolded fork_P_d_def] indep_forks)



subsubsection \<open>2.3  \<^const>\<open>PHILS\<close> is normalizable\<close>

text \<open>2.3.1 Automaton: Definition of the all-philosophers automaton\<close>

type_synonym \<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s = \<open>nat list\<close>


definition phils_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s, dining_event) A\<^sub>d\<close> (\<open>A\<^sub>P\<close>) where \<open>A\<^sub>P \<equiv> \<^sub>d\<Otimes>\<lbrakk>{}\<rbrakk> (A\<^sub>l\<^sub>p # map A\<^sub>r\<^sub>p [1..<N])\<close>

\<comment> \<open> if expression is more general, helpful to the proof\<close>
lemma phils_A_def_bis: \<open>A\<^sub>P = \<^sub>d\<Otimes>\<lbrakk>{}\<rbrakk> (map (\<lambda>i. if i = 0 then A\<^sub>l\<^sub>p else A\<^sub>r\<^sub>p i) [0..<N])\<close>
  (*sledgehammer: 
  by (smt (z3) N_g0 One_nat_def add.right_neutral add_diff_cancel_left' length_map length_upt lessI list.map(2) map_upt_eqI minus_suc nth_map_upt phils_A_def upt.simps(1) upt_rec)
  *)
  unfolding phils_A_def apply (subst (2) upt_rec, simp)
  apply (subgoal_tac \<open>map (\<lambda>i. if i = 0 then A\<^sub>l\<^sub>p else A\<^sub>r\<^sub>p i) [Suc 0..<N] = map A\<^sub>r\<^sub>p [Suc 0..<N]\<close>)
  by (presburger, subst list_eq_iff_nth_eq, simp)



text \<open>2.3.2 Proc-Omata: Definition and first properties of the associated normal process\<close>

definition phils_P_d:: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>phils_P_d \<equiv> P\<lbrakk>A\<^sub>P\<rbrakk>\<^sub>d\<close>

\<comment> \<open>Enableness \<epsilon>\<close>
lemma phils_\<epsilon>: \<open>length ps = N \<Longrightarrow> \<epsilon> A\<^sub>P ps = \<epsilon> A\<^sub>l\<^sub>p (ps ! 0) \<union> (\<Union>i\<in>{1..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (ps ! i))\<close>
  unfolding phils_A_def_bis
  apply (subst iterated_combine\<^sub>d_general_form_\<epsilon>, auto split: if_splits)
  using N_g0 by auto



text \<open>2.3.3 Equality between \<^const>\<open>NPHILS\<close> and \<^const>\<open>phils_P_d\<close>\<close>

lemma NPHILS_is_phils_P_d: \<open>NPHILS = phils_P_d (replicate N 0)\<close>
  unfolding phils_P_d_def phils_A_def_bis
  apply (subst P_d_mset_compactification_Sync_upt_version)

  apply (simp add: Int_commute indep_phils(1, 2), intro allI impI, simp split: if_splits)
  apply (subgoal_tac \<open>{0..<N} = insert 0 {1..<N}\<close>)
   apply (simp add: LPHIL0_is_lphil0_P_d lphil0_P_d_def)
  by (rule arg_cong[OF image_mset_cong]) (auto simp add: RPHIL_is_rphil_P_d rphil_P_d_def)



subsubsection \<open>2.4 The complete process  \<^const>\<open>DINING\<close> is normalizable\<close>

text \<open>2.4.1 Automaton: Definition of the dining automaton\<close>

definition 
dining_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<times> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s, dining_event) A\<^sub>d\<close> (\<open>A\<^sub>D\<close>) where \<open>A\<^sub>D \<equiv> A\<^sub>P \<^sub>d\<otimes>\<lbrakk>UNIV\<rbrakk>\<^sub>b\<^sub>i\<^sub>n\<^sub>t\<^sub>u\<^sub>p\<^sub>l\<^sub>e A\<^sub>F\<close>



text \<open>2.4.2  Proc-Omata: Definition and first properties of the associated normal process\<close>

definition dining_P_d:: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<times> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>dining_P_d \<equiv> P\<lbrakk>A\<^sub>D\<rbrakk>\<^sub>d\<close>

lemma dining_\<epsilon>:
  \<open>length ps = N \<Longrightarrow> length fs = N \<Longrightarrow>
   \<epsilon> A\<^sub>D (ps, fs) = (\<epsilon> A\<^sub>l\<^sub>p (ps ! 0) \<union> (\<Union>i\<in>{1..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (ps ! i))) \<inter> (\<Union>i<N. \<epsilon> (A\<^sub>f i) (fs ! i))\<close>
  by (simp add: dining_A_def binary_combine_tuple_\<epsilon> forks_\<epsilon> phils_\<epsilon>) 



text \<open>2.4.3 Equality between \<^const>\<open>DINING\<close> and \<^const>\<open>dining_P_d\<close>\<close>

lemma DINING_is_dining_P_d: \<open>DINING = dining_P_d (replicate N 0, replicate N 0)\<close>
  using P_d_binary_combine_tuple_Sync[of A\<^sub>P _ A\<^sub>F _ UNIV, folded dining_A_def,
                                        folded dining_P_d_def phils_P_d_def forks_P_d_def]
  by (metis DINING_def NFORKS_is_forks_P_d NPHILS_is_phils_P_d Sync_commute top_greatest)



subsection \<open>3. Proof:  Philosophers may dine ! Always !\<close>

method \<epsilon>_sets_simp uses opt = (simp_all split: if_split_asm)?,
                              simp_all add: fork_\<epsilon> lphil0_\<epsilon> rphil_\<epsilon> opt split: if_splits
method A_defs_simp uses opt = (simp_all split: if_split_asm)?,
                              simp_all add: fork_A_def lphil0_A_def rphil_A_def opt split: if_splits



\<comment> \<open>DF PROOF STRATEGY
A. to define the invariant that the system should satisfy
(B. to convert invarant definition into a lemma to facilitate the proof)
C. to prove the system satisfies the invariant by using Reachability Set,
   i.e., each reachable state satisfies inv (s \<in> Rd \<Rightarrow> inv s)
D. to prove  Enableness \<epsilon> \<noteq> {} =>  Deadlock Freedom assuming invariant is valid
   i.e., Deadlock-free for all states that satisfy inv
E. to prove \<^const>\<open>deadlock_free\<close> (P\<lbrakk>A\<rbrakk>d s)  : for each reachable state  \<forall>t \<in> \<R>d A s. \<epsilon> A t \<noteq> {}
\<close>


subsubsection \<open>3.1 Construction of an invariant for the dining automaton\<close>

\<comment> \<open>A. define the invariant that the system should satisfy\<close>
definition \<open>inv_dining ps fs \<equiv>
            length fs = N \<and> length ps = N
          \<and> (\<forall>i < N. fs ! i = 0 \<or> fs ! i = 1 \<or> fs ! i = 2) 
          \<and> (\<forall>i < N. ps ! i = 0 \<or> ps ! i = 1 \<or> ps ! i = 2 \<or> ps ! i = 3)
          \<and> (\<forall>i. Suc i < N \<longrightarrow> ((fs ! Suc i = 1) \<longleftrightarrow> ps ! Suc i \<noteq> 0)) 
          \<and> (fs ! (N - 1) = 2 \<longleftrightarrow> ps ! 0 \<noteq> 0)
          \<and> (\<forall>i < N - 1.           fs ! i = 2    \<longleftrightarrow> ps ! Suc i = 2)  
          \<and>    (fs ! 0  = 1   \<longleftrightarrow> ps ! 0 = 2)\<close> 



\<comment> \<open>B. to convert invariant definition into a lemma to facilitate the proof\<close>
lemma show_inv_dining: 
  \<open>length fs = N \<and> length ps = N \<Longrightarrow>
   (\<forall>i < N. fs ! i = 0 \<or> fs ! i = 1 \<or> fs ! i = 2) \<Longrightarrow>
   (\<forall>i < N. ps ! i = 0 \<or> ps ! i = 1 \<or> ps ! i = 2 \<or> ps ! i = 3) \<Longrightarrow>
   (\<forall>i. Suc i < N \<longrightarrow> (fs ! Suc i = 1 \<longleftrightarrow> ps ! Suc i \<noteq> 0)) \<Longrightarrow> (fs ! (N - 1) = 2 \<longleftrightarrow> ps ! 0 \<noteq> 0) \<Longrightarrow>
   (\<forall>i < N - 1. fs ! i = 2 \<longleftrightarrow> ps ! Suc i = 2) \<Longrightarrow> (fs ! 0  = 1 \<longleftrightarrow> ps ! 0 = 2) \<Longrightarrow> 
    inv_dining ps fs\<close>
  by (simp add: inv_dining_def)

\<comment> \<open>C. to proof Dinning satisfy the invariant by using Reachability Set, 
       i.e., all states satisfy the invariant. \<close>
\<comment> \<open>this lemma can be summarized as follows:
  If the system state s has evolved from the initial state (replicate N 0, replicate N 0) 
  through the recursive relation \<R>d Ad, then the system in state s will satisfy the invariant inv_dining.
  In other words, no matter how the system evolves, as long as it starts from the initial state
   and follows the system's state transition rules, the system's state will always satisfy the inv_dining invariant.\<close>

lemma inv_DINING: \<open>s \<in> \<R>\<^sub>d A\<^sub>D (replicate N 0, replicate N 0) \<Longrightarrow> inv_dining (fst s) (snd s)\<close>
proof(induct rule: \<R>\<^sub>d.induct)
  case init show ?case by (simp add: inv_dining_def)
next
  case (step t u e)
  obtain t_ps t_fs u_ps u_fs where t_pair: \<open>t = (t_ps, t_fs)\<close> and u_pair: \<open>u = (u_ps, u_fs)\<close> by fastforce
  hence inv_hyp: \<open>length t_fs = N\<close> \<open>length t_ps = N\<close> 
                 \<open>i < N \<Longrightarrow> t_fs ! i = 0 \<or> t_fs ! i = 1 \<or> t_fs ! i = 2\<close>
                 \<open>i < N \<Longrightarrow> t_ps ! i = 0 \<or> t_ps ! i = 1 \<or> t_ps ! i = 2 \<or> t_ps ! i = 3\<close>
                 \<open>Suc i < N \<Longrightarrow> (t_fs ! Suc i = 1) = (t_ps ! Suc i \<noteq> 0)\<close>
                 \<open>(t_fs ! (N - 1) = 2) = (t_ps ! 0 \<noteq> 0)\<close>
                 \<open>i < N - 1 \<Longrightarrow> (t_fs ! i = 2) = (t_ps ! Suc i = 2)\<close>
                 \<open>(t_fs ! 0 = 1) = (t_ps ! 0 = 2)\<close> for i
    using step.hyps(2)[simplified inv_dining_def] by simp_all
                
  have u_in_\<R>\<^sub>d_prem: \<open>(u_ps, u_fs) \<in> \<R>\<^sub>d A\<^sub>P (replicate N 0) \<times> \<R>\<^sub>d A\<^sub>F (replicate N 0)\<close>
    using \<R>\<^sub>d.step[OF step.hyps(1, 3), simplified dining_A_def]
    by (simp add: u_pair[symmetric], rule set_mp[OF \<R>\<^sub>d_binary_combine_tuple_subset])
  note u_in_\<R>\<^sub>d = u_in_\<R>\<^sub>d_prem[simplified mem_Times_iff, THEN conjunct1, simplified]
                 u_in_\<R>\<^sub>d_prem[simplified mem_Times_iff, THEN conjunct2, simplified]

  have same_length_u: \<open>length u_ps = N\<close> \<open>length u_fs = N\<close> 
    using same_length_\<R>\<^sub>d_iterated_combine_description[rotated, OF u_in_\<R>\<^sub>d(1)[unfolded phils_A_def]]
          same_length_\<R>\<^sub>d_iterated_combine_description[rotated, OF u_in_\<R>\<^sub>d(2)[unfolded forks_A_def]]
    by simp+

  have u_is: \<open>\<lfloor>u_ps\<rfloor> = \<tau> A\<^sub>P t_ps e\<close> \<open>\<lfloor>u_fs\<rfloor> = \<tau> A\<^sub>F t_fs e\<close>
    using step(3)[simplified dining_A_def, simplified binary_combine_tuple_defs]
    by (simp_all add: t_pair u_pair option.case_eq_if map_option_case split: if_splits)

  have e_in: \<open>e \<in> \<epsilon> A\<^sub>l\<^sub>p (t_ps ! 0) \<union> (\<Union>i\<in>{1..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (t_ps ! i))\<close>
             \<open>e \<in> (\<Union>i<N. \<epsilon> (A\<^sub>f i) (t_fs ! i))\<close>
    by (subst phils_\<epsilon>[symmetric], fact inv_hyp(2), simp add: \<epsilon>_simps, metis u_is(1))
       (subst forks_\<epsilon>[symmetric], fact inv_hyp(1), simp add: \<epsilon>_simps, metis u_is(2))

  have u_nth:
    \<open>i < N \<Longrightarrow> u_ps ! i = 
    (if i = 0 then (if e \<in> \<epsilon> A\<^sub>l\<^sub>p (t_ps ! 0) then \<lceil>\<tau> A\<^sub>l\<^sub>p (t_ps ! 0) e\<rceil> else t_ps ! 0)
     else if e \<in> \<epsilon> (A\<^sub>r\<^sub>p i) (t_ps ! i) then \<lceil>\<tau> (A\<^sub>r\<^sub>p i) (t_ps ! i) e\<rceil> else t_ps ! i)\<close> 
    \<open>i < N \<Longrightarrow> u_fs ! i =
     (if e \<in> \<epsilon> (A\<^sub>f i) (t_fs ! i) then \<lceil>\<tau> (A\<^sub>f i) (t_fs ! i) e\<rceil> else t_fs ! i)\<close> for i
    by (insert u_is(1), unfold phils_A_def, subst (asm) iterated_combine\<^sub>d_general_form_\<tau>,
        simp_all add: inv_hyp(2) split: if_splits)
       (insert u_is(2), unfold forks_A_def, subst (asm) iterated_combine\<^sub>d_general_form_\<tau>,
        simp_all add: inv_hyp(1) split: if_splits)

  have \<open>e \<in> \<epsilon> A\<^sub>P t_ps\<close> \<open>e \<in> \<epsilon> A\<^sub>F t_fs\<close> using u_is \<epsilon>_simps by fastforce+
  hence e_equiv: \<open>e \<in> \<epsilon> A\<^sub>l\<^sub>p (t_ps ! 0) \<longleftrightarrow> phil e = 0\<close>
                 \<open>Suc i < N \<Longrightarrow> e \<in> \<epsilon> (A\<^sub>r\<^sub>p (Suc i)) (t_ps ! Suc i) \<longleftrightarrow> phil e = Suc i\<close>
                 \<open>i < N \<Longrightarrow> e \<in> \<epsilon> (A\<^sub>f i) (t_fs ! i) \<longleftrightarrow> fork e = i\<close> for i
    using rphil_phil lphil0_phil ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx
    apply (simp_all add: phils_\<epsilon>[OF inv_hyp(2)] forks_\<epsilon>[OF inv_hyp(1)])
    by (fastforce, metis Zero_neq_Suc, blast)
  show ?case
  proof (simp add: u_pair, rule show_inv_dining[rule_format], simp add: same_length_u, goal_cases)
    case (1 i) thus ?case using u_nth(2)[of i] inv_hyp(3) by \<epsilon>_sets_simp A_defs_simp
  next
    case (2 i) thus ?case using u_nth(1)[of i] inv_hyp(4) by \<epsilon>_sets_simp A_defs_simp
  next
    case (3 i)
    with u_nth(1)[of \<open>Suc i\<close>] u_nth(2)[of \<open>Suc i\<close>] show ?case
      using inv_hyp(5)[of i] apply \<epsilon>_sets_simp apply A_defs_simp
      using e_equiv(3) fork_\<epsilon> e_equiv(2) rphil_\<epsilon> by fastforce+
  next
    case 4
    with u_nth(1)[of 0] u_nth(2) show ?case using inv_hyp(6) N_g1 apply \<epsilon>_sets_simp apply A_defs_simp
    apply (metis N_g0 One_nat_def Suc_pred fork_\<epsilon> dining_event.sel(3) 
                 dining_event.simps(3) inv_hyp(3) lessI singletonD e_equiv(3))
      using lphil0_\<epsilon> e_equiv(1) by force+
  next
    case (5 i)
    hence \<open>Suc i < N\<close> by linarith
    with u_nth(1)[of \<open>Suc i\<close>] u_nth(2)[of i] "5" show ?case 
      using inv_hyp(7)[of i] apply \<epsilon>_sets_simp apply A_defs_simp
      apply (metis Suc_lessD fork_\<epsilon> dining_event.sel(3) dining_event.simps(3) singletonD e_equiv(3))
      apply (metis One_nat_def Suc_lessD bot_nat_0.not_eq_extremum inv_hyp(3))
      using rphil_\<epsilon> e_equiv(2) by force+
  next
    case 6
    with u_nth(1)[of 0] u_nth(2)[of 0] show ?case
      using N_g1 inv_hyp(8) apply (simp split: if_split_asm) apply \<epsilon>_sets_simp apply A_defs_simp
      using lphil0_\<epsilon> e_equiv(1) fork_\<epsilon> e_equiv(3) by force+
  qed
qed






subsubsection \<open>3.2 The invariant \<^const>\<open>inv_dining\<close> implies deadlock freeness\<close>

method nonempty_Int_by_common_element for x = rule_tac ex_in_conv[THEN iffD1, OF exI, OF IntI, of x]


\<comment> \<open>D. to prove  Deadlock Freedom by using Enableness \<epsilon> \<noteq> {} assuming invariant \<close>
lemma inv_implies_DF: \<open>\<epsilon> A\<^sub>D (ps, fs) \<noteq> {}\<close> if hyp_inv: \<open>inv_dining ps fs\<close>
  apply (subst dining_\<epsilon>)
  apply (insert hyp_inv, unfold inv_dining_def, simp_all add: lphil0_\<epsilon>)
proof(elim conjE, intro conjI impI, goal_cases)
  case 1
  with 1(3)[rule_format, of 0, OF N_g0] show ?case
  proof(elim disjE, goal_cases)
    case 11:1 (* fs ! 0 = 0 *)
    thus ?case
      using 1(3)[rule_format, of 1, OF N_g1] apply(elim disjE) 
      (* fs ! 1 = 0 *)
      apply (subgoal_tac \<open>ps ! 1 = 0\<close>, nonempty_Int_by_common_element \<open>picks 1 1\<close>)
      using N_g1 apply \<epsilon>_sets_simp[3]
      apply (metis atLeastLessThan_iff le_refl less_irrefl_nat, blast, 
             metis less_zeroE linorder_neqE_nat)
      (* fs ! 1 = 1 *)
      apply (cases \<open>ps ! 1 = 1\<close>, nonempty_Int_by_common_element \<open>picks 1 0\<close>) (* ps ! 1 = 1 *)
      using N_g1 apply \<epsilon>_sets_simp[2]
      apply (metis One_nat_def atLeastLessThan_iff le_numeral_extra(4) less_numeral_extra(1),
             metis N_g0 lessThan_iff mod_less) 
      apply (nonempty_Int_by_common_element \<open>putsdown 1 1\<close>) (* ps ! 1 = 3 *)
      using N_g1 apply \<epsilon>_sets_simp[2]
      apply (metis atLeastLessThan_iff le_refl less_numeral_extra(3) zero_less_diff,
             metis gr0_conv_Suc lessThan_iff)
      (* fs ! 1 = 2 *)
      apply (cases \<open>N = 2\<close>, simp)
      apply (subgoal_tac \<open>ps ! 2 = 2\<close>, nonempty_Int_by_common_element \<open>putsdown 2 1\<close>)
      using N_g1 apply \<epsilon>_sets_simp
      by (metis One_nat_def Suc_lessI atLeastLessThan_iff diff_Suc_1 le_SucI
                le_numeral_extra(4) n_not_Suc_n numeral_2_eq_2 zero_less_Suc,
          metis One_nat_def Suc_1 Suc_lessI gr0_conv_Suc lessThan_iff
                less_diff_conv mod_less plus_1_eq_Suc,
          metis One_nat_def Suc_1)
  next
    case 12:2 (* fs ! 0 = 1 *)
    thus ?case by linarith
  next
    case 13:3 (* fs ! 0 = 2 *)
    thus ?case 
      apply (subgoal_tac \<open>ps ! 1 = 2\<close>, nonempty_Int_by_common_element \<open>putsdown 1 0\<close>)
      using N_g1 apply \<epsilon>_sets_simp
      by (metis atLeastLessThan_iff le_Suc_eq n_not_Suc_n numeral_2_eq_2 zero_less_Suc)
         (metis "13"(10) N_g0 One_nat_def Suc_1 lessThan_iff mod_less n_not_Suc_n zero_less_Suc)
  qed
next
  case 2
  from "2"(3, 7, 8, 10) N_g1 have f1: \<open>fs ! 0 \<noteq> 0 \<Longrightarrow> ps ! 1 = 2 \<and> fs ! 0 = 2\<close> by auto
  from 2 show ?case
    apply (cases \<open>fs ! 0 = 0\<close>)
    apply (nonempty_Int_by_common_element \<open>picks 0 0\<close>)
    using N_g1 apply \<epsilon>_sets_simp[2]
    using N_g0 apply blast
    apply (nonempty_Int_by_common_element \<open>putsdown 1 0\<close>)
    apply \<epsilon>_sets_simp
    by (metis N_g1 One_nat_def atLeastLessThan_iff f1 le_numeral_extra(4) less_numeral_extra(3))
       (metis N_g1 N_g0 One_nat_def lessThan_iff less_le_not_le mod_less)
next
  case 3 thus ?case by (nonempty_Int_by_common_element \<open>putsdown 0 0\<close>)
                       (\<epsilon>_sets_simp, metis N_g0 lessThan_iff zero_less_Suc)
next
  case 4 thus ?case by (nonempty_Int_by_common_element \<open>putsdown 0 (N - 1)\<close>)
                       (\<epsilon>_sets_simp, metis N_g0 One_nat_def Suc_1 Suc_diff_1 diff_less
                                           gr0_conv_Suc lessThan_iff mod_self n_not_Suc_n)
next
  case 5 thus ?case using 5(4)[rule_format, of 0] by simp
qed




subsubsection \<open>3.3 Conclusion\<close>


\<comment> \<open>E. corollary that Dining is DF\<close>
corollary deadlock_free_DINING: "deadlock_free DINING"
  unfolding DINING_is_dining_P_d dining_P_d_def 
  apply (subst P_d_deadlock_free_iff) (*(\<forall>t \<in> \<R>\<^sub>d A s. \<epsilon> A t \<noteq> {})*)
  using inv_DINING inv_implies_DF by force






end 

end