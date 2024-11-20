(*<*)
\<comment>\<open> ********************************************************************
 * Project         : Proc-Omata - Using automata to reason on HOL-CSP processes
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Benoît Ballenghien
 *
 * This file       : Normalization of CSP processes
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


chapter\<open> New version of normalization of CSP Processes \<close>

theory ProcessNormalization
  imports "HOL-CSPM.CSPM" "HOL-CSP.CSP_Induct"
begin

default_sort type






section \<open>Definitions\<close>

subsection \<open>Some notations\<close>

no_notation   floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)

notation Some (\<open>\<lfloor>_\<rfloor>\<close>)
notation  the (\<open>\<lceil>_\<rceil>\<close>)
notation None (\<open>\<diamond>\<close>)



subsection \<open>Non-deterministic and deterministic automata types\<close>

type_synonym ('\<sigma>, 'e) enabl = \<open>'\<sigma> \<Rightarrow> 'e set\<close>
type_synonym ('\<sigma>, 'e, '\<sigma>') trans = \<open>'\<sigma> \<Rightarrow> 'e \<Rightarrow> '\<sigma>'\<close>
type_synonym ('\<sigma>, 'e) trans\<^sub>d  = \<open>('\<sigma>, 'e, '\<sigma> option) trans\<close>
type_synonym ('\<sigma>, 'e) trans\<^sub>n\<^sub>d = \<open>('\<sigma>, 'e, '\<sigma> set) trans\<close>


(*A - Automaton, a record*)
record ('\<sigma>, 'e, '\<sigma>') A =  \<tau> :: \<open>('\<sigma>, 'e, '\<sigma>') trans\<close> (*transition function*)
                         \<S>\<^sub>F :: \<open>'\<sigma> set\<close>              (*set of final states*)
                         \<S>\<^sub>I :: \<open>'\<sigma> set\<close>              (*set of initial states*)

type_synonym ('\<sigma>, 'e) A\<^sub>d = \<open>('\<sigma>, 'e, '\<sigma> option) A\<close>
type_synonym ('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme = \<open>('\<sigma>, 'e, '\<sigma> option, '\<alpha>) A_scheme\<close>
type_synonym ('\<sigma>, 'e) A\<^sub>n\<^sub>d = \<open>('\<sigma>, 'e, '\<sigma> set) A\<close>
type_synonym ('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme = \<open>('\<sigma>, 'e, '\<sigma> set, '\<alpha>) A_scheme\<close>



subsection \<open>Enableness\<close>

\<comment> \<open>Enabled event:  \<tau> A s e \<noteq> \<diamond>  : 
  If there exists a valid state that  state s can transit to through event e 
  (i.e., it does not reach an undefined state),
   then this event e is enabled and belongs to the set \<epsilon>d A s.\<close>
\<comment> \<open>Enableness function \<epsilon>: returns a SET OF ENABLED EVENTS in a specific state s
    This is a mapping from an automaton (A_scheme) to a set of enabled events (('\<sigma>, 'e) enabl). \<close>
\<comment> \<open>\<epsilon>d A s = {e. \<tau> A s e \<noteq> \<diamond>} : All events e such that \<tau> A s e is not undefined, will be included in
 the enabled set \<epsilon>d A s.\<close>
consts \<epsilon> :: \<open>('\<sigma>, 'e, '\<sigma>', '\<alpha>) A_scheme \<Rightarrow> ('\<sigma>, 'e) enabl\<close>
overloading
  \<epsilon>\<^sub>d \<equiv> \<open>\<epsilon> :: ('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e) enabl\<close>
  \<epsilon>\<^sub>n\<^sub>d \<equiv> \<open>\<epsilon> :: ('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e) enabl\<close>
begin
fun  \<epsilon>\<^sub>d :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e) enabl\<close>  where \<open>\<epsilon>\<^sub>d A s = {e. \<tau> A s e \<noteq> \<diamond>}\<close>


fun \<epsilon>\<^sub>n\<^sub>d :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e) enabl\<close> where \<open>\<epsilon>\<^sub>n\<^sub>d A s = {e. \<tau> A s e \<noteq> {}}\<close>

end     

lemmas \<epsilon>_simps[simp del] = \<epsilon>\<^sub>d.simps \<epsilon>\<^sub>n\<^sub>d.simps
(* otherwise \<epsilon> would be systematically simplified in the abbreviations*)



subsection \<open>Reachability\<close>

\<comment> \<open>Reachability refers to ALL THE STATES that CAN BE REACHED in the system starting from an initial state.
    It takes an automaton A and an initial state s to return a set of states \<sigma>.
    Two inductive sets, \<R>d and \<R>nd, are defined to represent the set of reachable states
     in deterministic and non-deterministic systems, respectively.\<close>
inductive_set \<R>\<^sub>d :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma> set\<close> (\<open>\<R>\<^sub>d\<close>)
  for A :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme\<close> and s :: \<open>'\<sigma>\<close>
  where init : \<open>s \<in> \<R>\<^sub>d A s\<close>
  |     step : \<open>t \<in> \<R>\<^sub>d A s \<Longrightarrow> \<lfloor>u\<rfloor> = \<tau> A t e \<Longrightarrow> u \<in> \<R>\<^sub>d A s\<close>
\<comment> \<open>init rule: The initial state s is part of its own reachability set, 
  meaning that a state is always reachable from itself.
  step rule: If state t is reachable from state s, and state t is transited to state u through event e
  by the transition function \<tau> A t e, then state u is also reachable from s.\<close>



inductive_set \<R>\<^sub>n\<^sub>d :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma> set\<close> (\<open>\<R>\<^sub>n\<^sub>d\<close>)
  for A :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close> and s :: \<open>'\<sigma>\<close>
  where init : \<open>s \<in> \<R>\<^sub>n\<^sub>d A s\<close>
  |     step : \<open>t \<in> \<R>\<^sub>n\<^sub>d A s \<Longrightarrow> u \<in> \<tau> A t e \<Longrightarrow> u \<in> \<R>\<^sub>n\<^sub>d A s\<close>


\<comment> \<open>The set of reachable states is transitive. If u can be reached from t, 
and t can be reached from s, then u must also be reachable from s.\<close>
lemma \<R>\<^sub>d_trans: \<open>u \<in> \<R>\<^sub>d A t \<Longrightarrow> t \<in> \<R>\<^sub>d A s \<Longrightarrow> u \<in> \<R>\<^sub>d A s\<close>
  by (induct rule: \<R>\<^sub>d.induct, simp add: \<R>\<^sub>d.init) (meson \<R>\<^sub>d.step)

lemma \<R>\<^sub>n\<^sub>d_trans: \<open>u \<in> \<R>\<^sub>n\<^sub>d A t \<Longrightarrow> t \<in> \<R>\<^sub>n\<^sub>d A s \<Longrightarrow> u \<in> \<R>\<^sub>n\<^sub>d A s\<close>
  by (induct rule: \<R>\<^sub>n\<^sub>d.induct, simp add: \<R>\<^sub>n\<^sub>d.init) (meson \<R>\<^sub>n\<^sub>d.step)



subsection \<open>Morphisms\<close>

text \<open>Our morphisms are defined considering that except from \<^const>\<open>\<tau>\<close> the fields remain unchanged\<close>

definition from_det_to_ndet :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>)
  where \<open>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<equiv> \<lparr>\<tau> = \<lambda>s e. case \<tau> A s e of \<diamond> \<Rightarrow> {} | \<lfloor>t\<rfloor> \<Rightarrow> {t},
                   \<S>\<^sub>F = \<S>\<^sub>F A,
                   \<S>\<^sub>I = \<S>\<^sub>I A,
                   \<dots> = more A\<rparr>\<close>
definition from_ndet_to_det :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>)
  where \<open>\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<equiv> \<lparr>\<tau> = \<lambda>s e. if \<tau> A s e = {} then \<diamond> else \<lfloor>THE t. t \<in> \<tau> A s e\<rfloor>,
                   \<S>\<^sub>F = \<S>\<^sub>F A,
                   \<S>\<^sub>I = \<S>\<^sub>I A,
                   \<dots> = more A\<rparr>\<close>

definition from_s_to_\<sigma>s\<^sub>d :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma> list, 'e, '\<alpha>) A\<^sub>d_scheme\<close> (\<open>\<^sub>d\<lbrakk>_\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>)
  where \<open>\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<equiv> \<lparr>\<tau> = \<lambda>\<sigma>s e. case \<tau> A (hd \<sigma>s) e of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>t\<rfloor> \<Rightarrow> \<lfloor>[t]\<rfloor>,
                    \<S>\<^sub>F = {[s]| s. s \<in> \<S>\<^sub>F A},
                    \<S>\<^sub>I = {[s]| s. s \<in> \<S>\<^sub>I A},
                    \<dots> = more A\<rparr>\<close>
definition from_s_to_\<sigma>s\<^sub>n\<^sub>d :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma> list, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close> (\<open>\<^sub>n\<^sub>d\<lbrakk>_\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>)
  where \<open>\<^sub>n\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<equiv> \<lparr>\<tau> = \<lambda>\<sigma>s e. {[s]| s. s \<in> \<tau> A (hd \<sigma>s) e},
                     \<S>\<^sub>F = {[s]| s. s \<in> \<S>\<^sub>F A},
                     \<S>\<^sub>I = {[s]| s. s \<in> \<S>\<^sub>I A},
                     \<dots> = more A\<rparr>\<close>

definition from_\<sigma>s_to_s\<^sub>d :: \<open>('\<sigma> list, 'e, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme\<close> (\<open>\<^sub>d\<lbrakk>_\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s\<close>)
  where \<open>\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s \<equiv> \<lparr>\<tau> = \<lambda>s e. case \<tau> A [s] e of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>\<sigma>t\<rfloor> \<Rightarrow> \<lfloor>hd \<sigma>t\<rfloor>,
                    \<S>\<^sub>F = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>F A},
                    \<S>\<^sub>I = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>I A},
                    \<dots> = more A\<rparr>\<close>
definition from_\<sigma>s_to_s\<^sub>n\<^sub>d :: \<open>('\<sigma> list, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close> (\<open>\<^sub>n\<^sub>d\<lbrakk>_\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s\<close>)
  where \<open>\<^sub>n\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s \<equiv> \<lparr>\<tau> = \<lambda>s e. {hd \<sigma>t| \<sigma>t. \<sigma>t \<in> \<tau> A [s] e},
                     \<S>\<^sub>F = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>F A},
                     \<S>\<^sub>I = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>I A},
                     \<dots> = more A\<rparr>\<close>

lemmas det_ndet_conv_defs = from_det_to_ndet_def from_ndet_to_det_def
   and     s_\<sigma>s_conv_defs = from_s_to_\<sigma>s\<^sub>d_def from_s_to_\<sigma>s\<^sub>n\<^sub>d_def from_\<sigma>s_to_s\<^sub>d_def from_\<sigma>s_to_s\<^sub>n\<^sub>d_def



subsection \<open>Base maps\<close>

abbreviation \<open>base_map\<^sub>d \<equiv> \<lambda>s e. \<diamond>\<close>
abbreviation \<open>base_map\<^sub>n\<^sub>d \<equiv> \<lambda>s e. {}\<close>



subsection \<open>Product of automata\<close>

subsubsection \<open>Update in a product\<close>

\<comment> \<open>Updates the states of both automata A0 and  A1 simultaneously.
 It applies the function f to update the states of A0 and  A1,
 passing the state transitions A0 s0 e and \<tau>  A1 s1  e, respectively.\<close>
definition update_both  where \<open>update_both  A\<^sub>0 A\<^sub>1 s\<^sub>0 s\<^sub>1 e f \<equiv> f (\<tau> A\<^sub>0 s\<^sub>0 e) (\<tau> A\<^sub>1 s\<^sub>1 e)\<close>
\<comment> \<open>f is not explicitly defined within the definition of update_both; 
  it is a function passed as a parameter.
   When calling update_both, you can provide different functions for f depending on your needs.\<close>


definition update_left  where \<open>update_left  A\<^sub>0 s\<^sub>0 s\<^sub>1 e f g  \<equiv> f (\<tau> A\<^sub>0 s\<^sub>0 e) (g s\<^sub>1)\<close>
\<comment> \<open>Although in update_left the right-hand state s1 is not updated through \<tau>,
   the function g allows you to process s1 as needed. 
  By default, g might simply be an identity function (\<lambda>x. x, which makes no changes to  s1s1),
   but in specific use cases, you can apply g to perform some preprocessing 
  or adjustments to s1s1. This design adds more flexibility and extensibility to update_left.\<close>


definition update_right where \<open>update_right A\<^sub>1 s\<^sub>0 s\<^sub>1 e f g  \<equiv> f (g s\<^sub>0) (\<tau> A\<^sub>1 s\<^sub>1 e)\<close>

lemmas update_defs[simp] = update_both_def update_left_def update_right_def

abbreviation f_up_set where \<open>f_up_set f B C \<equiv> {f s t| s t. (s, t) \<in> B \<times> C}\<close>
\<comment> \<open>it applies f to each pair of s and t from the sets B \<times> C\<close>


abbreviation f_up_opt where \<open>f_up_opt f s t \<equiv> case s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>s'\<rfloor> \<Rightarrow> map_option (f s') t\<close>
\<comment> \<open>first to check if the 1st parameter s has a value, 
  then checks if the 2nd parameter t  has a value. 
  Only if both have values will it return a valid result; 
  otherwise, it returns None.\<close>




subsection \<open>Hypothesis on automata\<close>

(*required hypothesis when we will need continuity*)
abbreviation finite_trans :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>finite_trans A \<equiv> \<forall>s e. finite (\<tau> A s e)\<close>

lemma finite_trans_morphisms_simps[simp]: \<open>finite_trans \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
                                          \<open>finite_trans B \<Longrightarrow> finite_trans \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>
                                          \<open>finite_trans C \<Longrightarrow> finite_trans \<^sub>n\<^sub>d\<lbrakk>C\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s\<close>
  unfolding det_ndet_conv_defs s_\<sigma>s_conv_defs by (simp_all add: option.case_eq_if)


abbreviation card_trans_le1 :: \<open>('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>card_trans_le1 A \<equiv> \<forall>s e. card (\<tau> A s e) \<le> Suc 0\<close>

lemma finite_trans_conj_card_trans_le1_is:
  \<open>finite_trans A \<and> card_trans_le1 A \<longleftrightarrow> (\<forall>s e.  \<tau> A s e = {} \<or> (\<exists>!t. \<tau> A s e = {t}))\<close>
  by (auto, metis card_1_singleton_iff card_mono empty_subsetI insert_subset le_antisym,
      metis finite.simps, metis card_1_singleton_iff card_eq_0_iff le_eq_less_or_eq less_Suc_eq_le)

lemma finite_trans_imp_card_trans_le1_is:
  \<open>finite_trans A \<Longrightarrow> card_trans_le1 A \<longleftrightarrow> (\<forall>s e.  \<tau> A s e = {} \<or> (\<exists>!t. \<tau> A s e = {t}))\<close>
  by (simp add: finite_trans_conj_card_trans_le1_is[symmetric])


(*when this hypothesis is not verified, the product of two deterministic automata should become non deterministic*)
abbreviation det_indep_enabl :: \<open>('\<sigma>\<^sub>0, 'e, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> '\<sigma>\<^sub>0 \<Rightarrow> 'e set \<Rightarrow> ('\<sigma>\<^sub>1, 'e, '\<beta>) A\<^sub>d_scheme \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> bool\<close>
  where \<open>det_indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1 \<equiv> (\<forall>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0. \<forall>t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1. \<epsilon> A\<^sub>0 t\<^sub>0 \<inter> \<epsilon> A\<^sub>1 t\<^sub>1 \<subseteq> E)\<close>


(*finite state implies not enabled hypothesis*)
abbreviation fin_states_not_enabled :: \<open>('\<sigma>, 'e, '\<sigma>', '\<alpha>) A_scheme \<Rightarrow> bool\<close>
  where \<open>fin_states_not_enabled A \<equiv> \<forall>s \<in> \<S>\<^sub>F A. \<epsilon> A s = {}\<close>






section \<open>First properties\<close>

subsection \<open>Enableness \<^const>\<open>\<epsilon>\<close> first equalities\<close>

lemma base_map_\<epsilon>[simp]: \<open>\<epsilon> (\<lparr>\<tau> = base_map\<^sub>d, \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr> :: ('\<sigma>, 'e, '\<alpha>) A\<^sub>d_scheme) s = {}\<close>
                        \<open>\<epsilon> (\<lparr>\<tau> = base_map\<^sub>n\<^sub>d, \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr> :: ('\<sigma>, 'e, '\<alpha>) A\<^sub>n\<^sub>d_scheme) s = {}\<close>
  by (simp_all add: \<epsilon>_simps)

lemma s_\<sigma>s_conv_\<epsilon>[simp]: \<open>\<epsilon> \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s = \<epsilon> A (hd \<sigma>s)\<close> \<open>\<epsilon> \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s = \<epsilon> B (hd \<sigma>s)\<close>
                         \<open>\<epsilon> \<^sub>d\<lbrakk>C\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s s = \<epsilon> C [s]\<close> \<open>\<epsilon> \<^sub>n\<^sub>d\<lbrakk>D\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s s = \<epsilon> D [s]\<close>
  by (simp_all add: s_\<sigma>s_conv_defs \<epsilon>_simps option.case_eq_if)

lemma det_ndet_conv_\<epsilon>[simp]: \<open>\<epsilon> \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d s = \<epsilon> A s\<close> \<open>\<epsilon> \<lbrakk>B\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d s = \<epsilon> B s\<close>
  by (simp_all add: det_ndet_conv_defs \<epsilon>_simps option.case_eq_if)




subsection \<open>Initial states \<^const>\<open>\<S>\<^sub>I\<close> and final states \<^const>\<open>\<S>\<^sub>F\<close> first equalities\<close>

lemma s_\<sigma>s_conv_\<S>\<^sub>I: \<open>\<S>\<^sub>I \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {[s]| s. s \<in> \<S>\<^sub>I A} \<close>    \<open>\<S>\<^sub>I \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {[s]| s. s \<in> \<S>\<^sub>I B}\<close>
                    \<open>\<S>\<^sub>I \<^sub>d\<lbrakk>C\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>I C}\<close> \<open>\<S>\<^sub>I \<^sub>n\<^sub>d\<lbrakk>D\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>I D}\<close>
  by (simp_all add: s_\<sigma>s_conv_defs)

lemma det_ndet_conv_\<S>\<^sub>I: \<open>\<S>\<^sub>I \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = \<S>\<^sub>I A\<close> \<open>\<S>\<^sub>I \<lbrakk>B\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d = \<S>\<^sub>I B\<close>
  by (simp_all add: det_ndet_conv_defs \<epsilon>_simps option.case_eq_if)


lemma s_\<sigma>s_conv_\<S>\<^sub>F: \<open>\<S>\<^sub>F \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {[s]| s. s \<in> \<S>\<^sub>F A} \<close>    \<open>\<S>\<^sub>F \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {[s]| s. s \<in> \<S>\<^sub>F B}\<close>
                    \<open>\<S>\<^sub>F \<^sub>d\<lbrakk>C\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>F C}\<close> \<open>\<S>\<^sub>F \<^sub>n\<^sub>d\<lbrakk>D\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = {hd \<sigma>s| \<sigma>s. \<sigma>s \<in> \<S>\<^sub>F D}\<close>
  by (simp_all add: s_\<sigma>s_conv_defs)

lemma det_ndet_conv_\<S>\<^sub>F: \<open>\<S>\<^sub>F \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = \<S>\<^sub>F A\<close> \<open>\<S>\<^sub>F \<lbrakk>B\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d = \<S>\<^sub>F B\<close>
  by (simp_all add: det_ndet_conv_defs \<epsilon>_simps option.case_eq_if)

(*TODO: make the lemmas for binary_combine, arbitrary_combine, etc. ?*)



subsection \<open>Properties of our morphisms\<close>

method show_eq_A for A uses opt = (cases A, (auto simp add: opt)[1]) (* \<open>(rule ext)+\<close> ?*)

lemma base_map_det_ndet_conv: \<open>\<lbrakk>\<lparr>\<tau> = base_map\<^sub>d, \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr>\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d =
                               \<lparr>\<tau> = base_map\<^sub>n\<^sub>d, \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr>\<close>
                              \<open>\<lbrakk>\<lparr>\<tau> = base_map\<^sub>n\<^sub>d, \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr>\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d =
                               \<lparr>\<tau> = base_map\<^sub>d, \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr>\<close>
  unfolding det_ndet_conv_defs by simp_all


lemma from_det_to_ndet_s_\<sigma>s_conv_commute: \<open>\<^sub>n\<^sub>d\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = \<lbrakk>\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close> \<open>\<^sub>n\<^sub>d\<lbrakk>\<lbrakk>B\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = \<lbrakk>\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
  by (simp add: det_ndet_conv_defs s_\<sigma>s_conv_defs, rule ext,
      auto simp add: option.case_eq_if split: if_splits)+

lemma from_ndet_to_det_s_\<sigma>s_conv_commute:
  \<open>finite_trans A \<Longrightarrow> card_trans_le1 A \<Longrightarrow> \<^sub>d\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = \<lbrakk>\<^sub>n\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>
  \<open>finite_trans B \<Longrightarrow> card_trans_le1 B \<Longrightarrow> \<^sub>d\<lbrakk>\<lbrakk>B\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = \<lbrakk>\<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>
  by (subst (asm) finite_trans_imp_card_trans_le1_is, assumption,
      simp add: det_ndet_conv_defs s_\<sigma>s_conv_defs, intro ext,
      simp, intro allI impI, rule HOL.sym,
      rule the1_equality, metis singleton_iff, metis singleton_iff the_equality)+


lemma behaviour_s_\<sigma>s_conv:
  \<open>\<epsilon> \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s] = \<epsilon> A s\<close> \<open>\<tau> \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s] e = (case \<tau> A s e of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>t\<rfloor> \<Rightarrow> \<lfloor>[t]\<rfloor>)\<close>
  \<open>\<epsilon> \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s] = \<epsilon> B s\<close> \<open>\<tau> \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s] e = {[t] |t. t \<in> \<tau> B s e}\<close>
  \<open>\<epsilon> \<^sub>d\<lbrakk>C\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s s = \<epsilon> C [s]\<close> \<open>\<tau> \<^sub>d\<lbrakk>C\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s s e = (case \<tau> C [s] e of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>\<sigma>t\<rfloor> \<Rightarrow> \<lfloor>hd \<sigma>t\<rfloor>)\<close>
  \<open>\<epsilon> \<^sub>n\<^sub>d\<lbrakk>D\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s s = \<epsilon> D [s]\<close> \<open>\<tau> \<^sub>n\<^sub>d\<lbrakk>D\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s s e = {hd \<sigma>t| \<sigma>t. \<sigma>t \<in> \<tau> D [s] e}\<close>
  by simp_all (simp_all add: s_\<sigma>s_conv_defs)
 

lemma not_None_hypothesis_is_nonempty_hypothesis[simp]: \<open>\<tau> \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d s e \<noteq> {} \<longleftrightarrow> \<tau> A s e \<noteq> \<diamond>\<close>
  by (simp add: \<epsilon>_simps det_ndet_conv_defs option.case_eq_if)



lemma from_det_to_ndet_inv[simp]: \<open>\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d = A\<close>
  by (cases A, simp add: det_ndet_conv_defs, intro ext) (auto simp add: option.case_eq_if)

corollary inj_from_det_to_ndet: \<open>inj (\<lambda>A. \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<close> by (metis from_det_to_ndet_inv injI)


lemma from_ndet_to_det_inv_into[simp]: \<open>finite_trans A \<Longrightarrow> card_trans_le1 A \<Longrightarrow> \<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = A\<close>
  apply (cases A, simp add: det_ndet_conv_defs, intro ext)
  by (auto simp add: option.case_eq_if) (metis card_le_Suc0_iff_eq the_equality)+

corollary inj_on_from_ndet_to_det:  \<open>inj_on (\<lambda>A. \<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d) {A. finite_trans A \<and> card_trans_le1 A}\<close>
  by (metis (mono_tags, lifting) from_ndet_to_det_inv_into inj_on_def mem_Collect_eq)

corollary range_from_det_to_ndet: \<open>range (\<lambda>A. \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) = {A. finite_trans A \<and> card_trans_le1 A}\<close>
  unfolding image_def apply auto
  by (simp add: from_det_to_ndet_def option.case_eq_if) (metis from_ndet_to_det_inv_into)


theorem bij_betw_from_ndet_to_det: \<open>bij_betw (\<lambda>A. \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) UNIV {A. finite_trans A \<and> card_trans_le1 A}\<close>
  using inj_from_det_to_ndet bij_betw_def range_from_det_to_ndet by blast



lemma from_s_to_\<sigma>s_inv[simp]: \<open>\<^sub>d\<lbrakk>\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = A\<close> \<open>\<^sub>n\<^sub>d\<lbrakk>\<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s = B\<close>
  by (cases A, simp add: s_\<sigma>s_conv_defs, intro conjI ext;
      simp add: option.case_eq_if set_eq_iff; metis list.sel(1))
     (cases B, simp add: s_\<sigma>s_conv_defs, intro conjI ext;
      simp add: option.case_eq_if set_eq_iff; metis list.sel(1))

corollary inj_from_s_to_\<sigma>s: \<open>inj (\<lambda>A. \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s)\<close> \<open>inj (\<lambda>A. \<^sub>n\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s)\<close>
  by (metis from_s_to_\<sigma>s_inv(1) injI) (metis from_s_to_\<sigma>s_inv(2) injI)


lemma from_\<sigma>s_to_s_inv_into[simp]:
  \<open>\<forall>\<sigma>s e. \<tau> A \<sigma>s e = \<tau> A [hd \<sigma>s] e \<and> (e \<in> \<epsilon> A \<sigma>s \<longrightarrow> length \<lceil>\<tau> A \<sigma>s e\<rceil> = 1) \<and> 
          (\<sigma>s \<in> \<S>\<^sub>F A \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I A \<longrightarrow> length \<sigma>s = 1) \<Longrightarrow> \<^sub>d\<lbrakk>\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = A\<close>
  \<open>\<forall>\<sigma>s e. \<tau> B \<sigma>s e = \<tau> B [hd \<sigma>s] e \<and> (\<forall>\<sigma>t \<in> \<tau> B \<sigma>s e. length \<sigma>t = 1) \<and>
          (\<sigma>s \<in> \<S>\<^sub>F B \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I B \<longrightarrow> length \<sigma>s = 1) \<Longrightarrow> \<^sub>n\<^sub>d\<lbrakk>\<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = B\<close>
   apply (cases A, simp add: s_\<sigma>s_conv_defs, intro conjI ext;
          simp add: option.case_eq_if set_eq_iff \<epsilon>_simps)
  subgoal by (metis One_nat_def add_diff_cancel_left' bot_nat_0.not_eq_extremum length_0_conv
              length_tl list.expand list.sel(1, 3) not_Cons_self2 option.sel plus_1_eq_Suc zero_less_one)
  subgoal by (metis One_nat_def add_diff_cancel_left' length_0_conv length_tl list.collapse plus_1_eq_Suc zero_neq_one)
  subgoal by (metis One_nat_def add_diff_cancel_left' length_0_conv length_tl list.collapse plus_1_eq_Suc zero_neq_one)
  apply (cases B, simp add: s_\<sigma>s_conv_defs, intro conjI ext;
         simp add: option.case_eq_if set_eq_iff \<epsilon>_simps)
  subgoal by (metis length_0_conv length_Suc_conv list.sel(1))
  subgoal by (metis One_nat_def add_diff_cancel_left' length_0_conv length_tl list.collapse plus_1_eq_Suc zero_neq_one)
  subgoal by (metis One_nat_def add_diff_cancel_left' length_0_conv length_tl list.collapse plus_1_eq_Suc zero_neq_one)
  done

corollary inj_on_from_\<sigma>s_to_s:
  \<open>inj_on (\<lambda>A. \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s) {A. \<forall>\<sigma>s e. \<tau> A \<sigma>s e = \<tau> A [hd \<sigma>s] e \<and> (e \<in> \<epsilon> A \<sigma>s \<longrightarrow> length \<lceil>\<tau> A \<sigma>s e\<rceil> = 1) \<and> 
                                   (\<sigma>s \<in> \<S>\<^sub>F A \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I A \<longrightarrow> length \<sigma>s = 1)}\<close>
  \<open>inj_on (\<lambda>B. \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>s) {B. \<forall>\<sigma>s e. \<tau> B \<sigma>s e = \<tau> B [hd \<sigma>s] e \<and> (\<forall>\<sigma>t \<in> \<tau> B \<sigma>s e. length \<sigma>t = 1) \<and> 
                                   (\<sigma>s \<in> \<S>\<^sub>F B \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I B \<longrightarrow> length \<sigma>s = 1)}\<close>
  by (rule inj_onI; insert from_\<sigma>s_to_s_inv_into(1) | insert from_\<sigma>s_to_s_inv_into(2), fastforce)+

corollary range_from_s_to_\<sigma>s:
  \<open>range (\<lambda>A. \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s) = {A. \<forall>\<sigma>s e. \<tau> A \<sigma>s e = \<tau> A [hd \<sigma>s] e \<and> (e \<in> \<epsilon> A \<sigma>s \<longrightarrow> length \<lceil>\<tau> A \<sigma>s e\<rceil> = 1) \<and> 
                                    (\<sigma>s \<in> \<S>\<^sub>F A \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I A \<longrightarrow> length \<sigma>s = 1)}\<close>
  \<open>range (\<lambda>B. \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s) = {B. \<forall>\<sigma>s e. \<tau> B \<sigma>s e = \<tau> B [hd \<sigma>s] e \<and> (\<forall>\<sigma>t \<in> \<tau> B \<sigma>s e. length \<sigma>t = 1) \<and> 
                                    (\<sigma>s \<in> \<S>\<^sub>F B \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I B \<longrightarrow> length \<sigma>s = 1)}\<close>
  unfolding image_def apply auto
  apply (auto simp add: s_\<sigma>s_conv_defs option.case_eq_if \<epsilon>_simps split: if_splits)[4]
  apply (metis One_nat_def from_\<sigma>s_to_s_inv_into(1))
  apply (auto simp add: s_\<sigma>s_conv_defs option.case_eq_if \<epsilon>_simps split: if_splits)[5]
  by (metis One_nat_def from_\<sigma>s_to_s_inv_into(2))


theorem bij_betw_from_s_to_\<sigma>s: 
  \<open>bij_betw (\<lambda>A. \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s) UNIV {A. \<forall>\<sigma>s e. \<tau> A \<sigma>s e = \<tau> A [hd \<sigma>s] e \<and> (e \<in> \<epsilon> A \<sigma>s \<longrightarrow> length \<lceil>\<tau> A \<sigma>s e\<rceil> = 1) \<and> 
                                          (\<sigma>s \<in> \<S>\<^sub>F A \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I A \<longrightarrow> length \<sigma>s = 1)}\<close>
  \<open>bij_betw (\<lambda>B. \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s) UNIV {B. \<forall>\<sigma>s e. \<tau> B \<sigma>s e = \<tau> B [hd \<sigma>s] e \<and> (\<forall>\<sigma>t \<in> \<tau> B \<sigma>s e. length \<sigma>t = 1) \<and> 
                                          (\<sigma>s \<in> \<S>\<^sub>F B \<longrightarrow> length \<sigma>s = 1) \<and> (\<sigma>s \<in> \<S>\<^sub>I B \<longrightarrow> length \<sigma>s = 1)}\<close>
  using inj_from_s_to_\<sigma>s bij_betw_def range_from_s_to_\<sigma>s by blast+



subsection \<open>Reachability results (for \<^const>\<open>\<R>\<^sub>d\<close> and \<^const>\<open>\<R>\<^sub>n\<^sub>d\<close>)\<close>

lemma \<R>_base_map[simp]: \<open>\<R>\<^sub>d  \<lparr>\<tau> = base_map\<^sub>d,  \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr> = (\<lambda>s. {s})\<close>
                         \<open>\<R>\<^sub>n\<^sub>d \<lparr>\<tau> = base_map\<^sub>n\<^sub>d, \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr> = (\<lambda>s. {s})\<close>
  by (rule ext, safe, subst (asm) \<R>\<^sub>d.simps \<R>\<^sub>n\<^sub>d.simps, simp_all add: \<R>\<^sub>d.init \<R>\<^sub>n\<^sub>d.init)+


theorem \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d: \<open>\<R>\<^sub>n\<^sub>d \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d s = \<R>\<^sub>d A s\<close>
proof safe
  show \<open>x \<in> \<R>\<^sub>n\<^sub>d \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d s \<Longrightarrow> x \<in> \<R>\<^sub>d A s\<close> for x
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, fact \<R>\<^sub>d.init, erule \<R>\<^sub>d.step)
       (simp add: from_det_to_ndet_def option.case_eq_if split: if_split_asm)
next
  show \<open>x \<in> \<R>\<^sub>d A s \<Longrightarrow> x \<in> \<R>\<^sub>n\<^sub>d \<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d s\<close> for x
    by (induct rule: \<R>\<^sub>d.induct, fact \<R>\<^sub>n\<^sub>d.init)
       (metis \<R>\<^sub>n\<^sub>d.step det_ndet_conv_defs(1) option.case(2) 
              option.set_intros option.simps(15) select_convs(1))
qed


(*TODO: see where this can be useful*)
lemma bij_betw_\<R>\<^sub>n\<^sub>d_if_same_\<tau>: \<open>bij_betw f (\<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0) (\<R>\<^sub>n\<^sub>d B\<^sub>1 (f s\<^sub>0))\<close>
  if \<open>inj_on f (\<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0)\<close> and \<open>\<forall>e. \<forall>s \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0. \<tau> B\<^sub>1 (f s) e = f ` \<tau> B\<^sub>0 s e\<close>
proof (rule bij_betw_imageI, fact that(1), auto simp add: image_def, goal_cases)
  show \<open>s \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<Longrightarrow> f s \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 (f s\<^sub>0)\<close> for s
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, simp add: \<R>\<^sub>n\<^sub>d.init, metis \<R>\<^sub>n\<^sub>d.step that(2) image_eqI)
next
  show \<open>s \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 (f s\<^sub>0) \<Longrightarrow> \<exists>t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0. s = f t\<close> for s
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, metis \<R>\<^sub>n\<^sub>d.simps, metis (mono_tags, lifting) \<R>\<^sub>n\<^sub>d.step that(2) image_iff)
qed

lemma bij_betw_\<R>\<^sub>d_if_same_\<tau>: \<open>bij_betw f (\<R>\<^sub>d A\<^sub>0 s\<^sub>0) (\<R>\<^sub>d A\<^sub>1 (f s\<^sub>0))\<close>
  if \<open>inj_on f (\<R>\<^sub>d A\<^sub>0 s\<^sub>0)\<close> and \<open>\<forall>e. \<forall>s \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0. \<tau> A\<^sub>1 (f s) e = map_option f (\<tau> A\<^sub>0 s e)\<close>
  apply (subst (1 2) \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d[symmetric], rule bij_betw_\<R>\<^sub>n\<^sub>d_if_same_\<tau>)
  by (simp_all add: \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d that(1))
     (simp add: det_ndet_conv_defs that(2) option.case_eq_if map_option_case)

lemmas same_\<tau>_implies_same_\<R>\<^sub>n\<^sub>d = bij_betw_\<R>\<^sub>n\<^sub>d_if_same_\<tau>[where f = id, simplified bij_betw_def, simplified]
   and same_\<tau>_implies_same_\<R>\<^sub>d = bij_betw_\<R>\<^sub>d_if_same_\<tau>[where f = id, simplified bij_betw_def option.map_id, simplified] 
 

method \<R>_subset_method uses defs opt induct init simps = 
  induct rule: induct, auto simp add: init defs \<epsilon>_simps split: if_splits,
  (metis (no_types, opaque_lifting) simps)+

method \<R>\<^sub>d_subset_method uses defs opt =
  \<R>_subset_method defs: defs opt: opt induct: \<R>\<^sub>d.induct init: \<R>\<^sub>d.init simps: \<R>\<^sub>d.simps

method \<R>\<^sub>n\<^sub>d_subset_method uses defs opt =
  \<R>_subset_method defs: defs opt: opt induct: \<R>\<^sub>n\<^sub>d.induct init: \<R>\<^sub>n\<^sub>d.init simps: \<R>\<^sub>n\<^sub>d.simps


lemma \<R>\<^sub>n\<^sub>d_from_s_to_\<sigma>s_description: \<open>\<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s] = {[t]| t. t \<in> \<R>\<^sub>n\<^sub>d B s}\<close>
proof safe
  show \<open>x \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s] \<Longrightarrow> \<exists>t. x = [t] \<and> t \<in> \<R>\<^sub>n\<^sub>d B s\<close> for x
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, auto simp add: \<R>\<^sub>n\<^sub>d.init behaviour_s_\<sigma>s_conv(4), metis \<R>\<^sub>n\<^sub>d.step)
next
  show \<open>t \<in> \<R>\<^sub>n\<^sub>d B s \<Longrightarrow> [t] \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s]\<close> for t
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, simp_all add: \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step behaviour_s_\<sigma>s_conv(4))
qed


lemma \<R>\<^sub>d_from_s_to_\<sigma>s_description: \<open>\<R>\<^sub>d \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [s] = {[t]| t. t \<in> \<R>\<^sub>d A s}\<close>
  by (subst \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d[symmetric] from_det_to_ndet_s_\<sigma>s_conv_commute(1)[symmetric] 
            \<R>\<^sub>n\<^sub>d_from_s_to_\<sigma>s_description)+ rule




lemma length_\<R>\<^sub>d_from_s_to_\<sigma>s: \<open>\<sigma>t \<in> \<R>\<^sub>d \<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s \<Longrightarrow> \<sigma>t = \<sigma>s \<or> length \<sigma>t = 1\<close>  
  and length_\<R>\<^sub>n\<^sub>d_from_s_to_\<sigma>s: \<open>\<sigma>t \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s \<Longrightarrow> \<sigma>t = \<sigma>s \<or> length \<sigma>t = 1\<close>
  apply (simp_all add: s_\<sigma>s_conv_defs)
  by (induct rule: \<R>\<^sub>d.induct, simp, simp add: option.case_eq_if split: if_splits)
     (induct rule: \<R>\<^sub>n\<^sub>d.induct, simp, auto)



section \<open>Normalization\<close> 

subsection \<open>Non-deterministic case\<close>

text \<open>First version, without final state notion\<close>

abbreviation P_nd_step :: \<open>[('\<sigma>, 'e) enabl, ('\<sigma>, 'e) trans\<^sub>n\<^sub>d, '\<sigma> \<Rightarrow> 'e process, '\<sigma>] \<Rightarrow> 'e process\<close>
  where \<open>P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A X s \<equiv> \<box> e \<in> \<epsilon>\<^sub>A s \<rightarrow> \<Sqinter> s' \<in> \<tau>\<^sub>A s e. X s'\<close>

abbreviation \<open>P_nd A \<equiv> \<mu> X. P_nd_step (\<epsilon> A) (\<tau> A) X\<close>
notation P_nd (\<open>P\<lbrakk>_\<rbrakk>\<^sub>n\<^sub>d\<close> 1000)


(*TODO: see if we can remove finite hypothesis (probably not possible),
  or at least have a finite hpothesis over reachable states*)
lemma P_nd_step_cont[simp]: \<open>(\<forall>s e. finite (\<tau>\<^sub>A s e)) \<Longrightarrow> cont (P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A)\<close>
  by (simp add: cont_fun)

lemmas P_nd_step_cont_bis = P_nd_step_cont[of \<open>\<tau> A\<close> \<open>\<epsilon> A\<close>] for A

lemma P_nd_rec: \<open>finite_trans A \<Longrightarrow> P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d = (\<lambda>s. P_nd_step (\<epsilon> A) (\<tau> A) P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s)\<close>
  by (rule cont_process_rec, rule) simp


lemma P_nd_\<S>\<^sub>F_useless: \<open>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d = P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>n\<^sub>d\<close> if \<open>finite_trans A\<close>
proof -
  have f1: \<open>\<epsilon> (A\<lparr>\<S>\<^sub>F := {}\<rparr>) = \<epsilon> A\<close> by (auto simp add: \<epsilon>_simps)
  have \<open>\<forall>s. P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>n\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>n\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P_nd_rec) (simp_all add: f1 that) 
  also have \<open>\<forall>s. P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>n\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P_nd_rec) (simp_all add: f1 that)
  ultimately show ?thesis by (intro ext FD_antisym) blast+
qed



text \<open>New version with final state notion where we just SKIP\<close>

abbreviation P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step ::
  \<open>[('\<sigma>, 'e) enabl, ('\<sigma>, 'e) trans\<^sub>n\<^sub>d, '\<sigma> set, '\<sigma> \<Rightarrow> 'e process, '\<sigma>] \<Rightarrow> 'e process\<close>
  where \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<S>\<^sub>F\<^sub>A X s \<equiv> if s \<in> \<S>\<^sub>F\<^sub>A then SKIP else P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A X s\<close>

abbreviation \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd A \<equiv> \<mu> X. (\<lambda> s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step (\<epsilon> A) (\<tau> A) (\<S>\<^sub>F A) X s)\<close> 
notation P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd (\<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>_\<rbrakk>\<^sub>n\<^sub>d\<close> 1000)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step_cont[simp]: \<open>(\<forall>s e. finite (\<tau>\<^sub>A s e)) \<Longrightarrow> cont (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<S>\<^sub>F\<^sub>A)\<close>
  by (simp add: cont_fun)

lemmas P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step_cont_bis = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step_cont[of \<open>\<tau> A\<close> \<open>\<S>\<^sub>F A\<close> \<open>\<epsilon> A\<close>] for A

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec: \<open>finite_trans A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d = (\<lambda>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_step (\<epsilon> A) (\<tau> A) (\<S>\<^sub>F A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s)\<close>
  by (rule cont_process_rec, rule) simp



text \<open>Correspondance when \<^term>\<open>\<S>\<^sub>F A = {}\<close>\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_empty_\<S>\<^sub>F[simp]: \<open>\<S>\<^sub>F A = {} \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d = P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d\<close> by simp

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_empty_\<S>\<^sub>F_bis: \<open>finite_trans A \<Longrightarrow> P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>n\<^sub>d\<close>
   by (simp add: P_nd_\<S>\<^sub>F_useless)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_empty_\<S>\<^sub>F_inter_\<R>\<^sub>n\<^sub>d:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s = P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s\<close> if \<open>finite_trans A\<close> and \<open>\<S>\<^sub>F A \<inter> \<R>\<^sub>n\<^sub>d A s = {}\<close>
proof -
  have \<open>\<forall>t. t \<in> \<R>\<^sub>n\<^sub>d A s \<longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d t \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d t\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>t. t \<in> \<R>\<^sub>n\<^sub>d A s \<longrightarrow> x t \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d t\<close>],
           auto simp add: cont_fun cont2mono that(1))
    using that(2) apply blast
    apply (subst P_nd_rec[OF that(1)])
    by (meson mono_Mprefix_FD \<R>\<^sub>n\<^sub>d.step mono_MultiNdet_FD that(1))

  also have \<open>\<forall>t. t \<in> \<R>\<^sub>n\<^sub>d A s \<longrightarrow> P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d t \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d t\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>t. t \<in> \<R>\<^sub>n\<^sub>d A s \<longrightarrow> x t \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d t\<close>],
           simp add: cont_fun cont2mono that(1), simp)
    apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec[OF that(1)], auto simp add: that(1))
    using that(2) apply blast
    by (meson mono_Mprefix_FD \<R>\<^sub>n\<^sub>d.step mono_MultiNdet_FD that(1))
    
  ultimately show ?thesis by (meson FD_antisym \<R>\<^sub>n\<^sub>d.simps)
qed
 

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec_notin_\<S>\<^sub>F:
  \<open>s \<notin> \<S>\<^sub>F A \<Longrightarrow> finite_trans A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s = P_nd_step (\<epsilon> A) (\<tau> A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec, assumption) (simp add: Det_STOP)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec_in_\<S>\<^sub>F: \<open>s \<in> \<S>\<^sub>F A \<Longrightarrow> finite_trans A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d s = SKIP\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec, assumption, simp)
  


subsection \<open>Deterministic case\<close>

text \<open>First version, without final state notion\<close>

abbreviation P_d_step :: \<open>[('\<sigma>, 'e) enabl, ('\<sigma>, 'e) trans\<^sub>d, '\<sigma> \<Rightarrow> 'e process, '\<sigma>] \<Rightarrow> 'e process\<close>
  where \<open>P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A X s \<equiv> \<box> e \<in> \<epsilon>\<^sub>A s \<rightarrow> X \<lceil>\<tau>\<^sub>A s e\<rceil>\<close>
\<comment> \<open>this is to turn one-time transition of automaton to be recursive\<close>


\<comment> \<open>Definition 4 Deterministic Proc-Omata\<close>
abbreviation \<open>P_d A \<equiv> \<mu> X. P_d_step (\<epsilon> A) (\<tau> A) X\<close>
notation P_d (\<open>P\<lbrakk>_\<rbrakk>\<^sub>d\<close> 1000)
\<comment> \<open>function P\<lbrakk>A\<rbrakk>d calls P_d_step, and the latter requires 4 parameters.
   However, in P_d A, only \<epsilon> A and \<tau> A are passed as parameters to P_d_step,
   and X is automatically generated (as 3rd parameter) through recursion (\<mu> X),
   representing the mapping that recursively calls itself.
  The 4th parameter of P_d_step, 's', is not passed in the definition of P_d A. 
  The state s is only passed when the process is actually invoked. 
  In other words, when you use P_d A, you will pass a specific state s. 
  For example, when you call P_d A s, s is passed as the fourth parameter to P_d_step.\<close>




lemma P_d_step_cont[simp]: \<open>cont (P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A)\<close>
  by (simp add: cont_fun)

lemmas P_d_step_cont_bis = P_d_step_cont[of \<open>\<epsilon> A\<close> \<open>\<tau> A\<close>] for A
\<comment> \<open>This is a specific instantiation of P_d_step_cont,
   where the general \<epsilon>A and \<tau>A are replaced with \<epsilon> A and \<tau> A, 
   which are the specific enabling function and state transition function of the automaton A.\<close>


\<comment> \<open>Sect 3.3 Proposition 2 \<close>
lemma P_d_rec: \<open>P\<lbrakk>A\<rbrakk>\<^sub>d = (\<lambda>s. P_d_step (\<epsilon> A) (\<tau> A) P\<lbrakk>A\<rbrakk>\<^sub>d s)\<close>
  by (rule cont_process_rec, rule) simp
\<comment> \<open>LHS is actually a function that takes the state s as a parameter, with the type \<sigma> \<Rightarrow> 'e process,
     meaning it is a "mapping from state to process." It is an implicit recursive function. 
    The RHS shows a Lambda expression that accepts the state s and passes s to P_d_step, 
    making it an explicit recursive function.\<close>

lemma P_d_\<S>\<^sub>F_useless: \<open>P\<lbrakk>A\<rbrakk>\<^sub>d = P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>d\<close>
proof -
  have f1: \<open>\<epsilon> (A\<lparr>\<S>\<^sub>F := {}\<rparr>) = \<epsilon> A\<close> by (auto simp add: \<epsilon>_simps)
  have \<open>\<forall>s. P\<lbrakk>A\<rbrakk>\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P_d_rec) (simp add: f1) 
  also have \<open>\<forall>s. P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P_d_rec) (simp add: f1)
  ultimately show ?thesis by (intro ext FD_antisym) blast+
qed



text \<open>New version with final state notion where we just SKIP\<close>

abbreviation P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step ::
  \<open>[('\<sigma>, 'e) enabl, ('\<sigma>, 'e) trans\<^sub>d, '\<sigma> set, '\<sigma> \<Rightarrow> 'e process, '\<sigma>] \<Rightarrow> 'e process\<close>
  where \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<S>\<^sub>F\<^sub>A X s \<equiv> if s \<in> \<S>\<^sub>F\<^sub>A then SKIP else P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A X s\<close>

abbreviation \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d A \<equiv> \<mu> X. (\<lambda> s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step (\<epsilon> A) (\<tau> A) (\<S>\<^sub>F A) X s)\<close> 
notation P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d (\<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>_\<rbrakk>\<^sub>d\<close> 1000)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step_cont[simp]: \<open>cont (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<S>\<^sub>F\<^sub>A)\<close>
  by (simp add: cont_fun)

lemmas P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step_cont_bis = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step_cont[of \<open>\<S>\<^sub>F A\<close> \<open>\<epsilon> A\<close> \<open>\<tau> A\<close>] for A

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec: \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d = (\<lambda>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_step (\<epsilon> A) (\<tau> A) (\<S>\<^sub>F A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s)\<close>
  by (rule cont_process_rec, rule) simp



text \<open>Correspondance when \<^term>\<open>\<S>\<^sub>F A = {}\<close>\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_empty_\<S>\<^sub>F[simp]: \<open>\<S>\<^sub>F A = {} \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d = P\<lbrakk>A\<rbrakk>\<^sub>d\<close> by simp

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_empty_\<S>\<^sub>F_bis: \<open>P\<lbrakk>A\<rbrakk>\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<lparr>\<S>\<^sub>F := {}\<rparr>\<rbrakk>\<^sub>d\<close> by (simp_all add: P_d_\<S>\<^sub>F_useless)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_empty_\<S>\<^sub>F_inter_\<R>\<^sub>n\<^sub>d: \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s = P\<lbrakk>A\<rbrakk>\<^sub>d s\<close> if \<open>\<S>\<^sub>F A \<inter> \<R>\<^sub>d A s = {}\<close>
proof -
  have \<open>\<forall>t. t \<in> \<R>\<^sub>d A s \<longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d t \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>d t\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>t. t \<in> \<R>\<^sub>d A s \<longrightarrow> x t \<sqsubseteq>\<^sub>F\<^sub>D P\<lbrakk>A\<rbrakk>\<^sub>d t\<close>],
           auto simp add: cont_fun cont2mono)
    using that(1) apply blast
    by (subst P_d_rec) (simp add: \<R>\<^sub>d.intros(2) \<epsilon>_simps(1))

  also have \<open>\<forall>t. t \<in> \<R>\<^sub>d A s \<longrightarrow> P\<lbrakk>A\<rbrakk>\<^sub>d t \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d t\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>t. t \<in> \<R>\<^sub>d A s \<longrightarrow> x t \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d t\<close>],
           simp add: cont_fun cont2mono, simp)
    apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec, auto simp add: that)
    using that apply blast
    by (simp add: \<R>\<^sub>d.intros(2) \<epsilon>_simps(1))
    
  ultimately show ?thesis by (meson FD_antisym \<R>\<^sub>d.simps)
qed
 

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec_notin_\<S>\<^sub>F: \<open>s \<notin> \<S>\<^sub>F A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s = P_d_step (\<epsilon> A) (\<tau> A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec) (simp add: Det_STOP)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec_in_\<S>\<^sub>F: \<open>s \<in> \<S>\<^sub>F A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s = SKIP\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec, simp)



subsection \<open>Link between \<^term>\<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d\<close> and \<^term>\<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>n\<^sub>d\<close>\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_is_some_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd: \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>n\<^sub>d\<close>
proof -
  have \<open>\<forall>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>n\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>n\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec) (auto simp add: det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)
  also have \<open>\<forall>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>n\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec) (auto simp add: det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)
  ultimately show ?thesis by (intro ext FD_antisym) blast+
qed


corollary P_d_is_some_P_nd: \<open>P\<lbrakk>A\<rbrakk>\<^sub>d = P\<lbrakk>\<lbrakk>A\<rbrakk>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rbrakk>\<^sub>n\<^sub>d\<close>
  apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_empty_\<S>\<^sub>F_bis, subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_empty_\<S>\<^sub>F_bis, simp)
  apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_is_some_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd)
  by (simp add: det_ndet_conv_defs)



subsection \<open>Demonstrate equality between normal processes\<close>

subsubsection \<open>This is the easiest method we can think about\<close>

lemma       P_dI: \<open>\<forall> s e. \<tau> A\<^sub>0 s e = \<tau> A\<^sub>1 s e \<Longrightarrow> P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d = P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d\<close>
  and      P_ndI: \<open>\<forall> s e. \<tau> B\<^sub>0 s e = \<tau> B\<^sub>1 s e \<Longrightarrow> P\<lbrakk>B\<^sub>0\<rbrakk>\<^sub>n\<^sub>d = P\<lbrakk>B\<^sub>1\<rbrakk>\<^sub>n\<^sub>d\<close>
  and  P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_dI: \<open>\<S>\<^sub>F A\<^sub>0 = \<S>\<^sub>F A\<^sub>1 \<Longrightarrow> \<forall> s e. \<tau> A\<^sub>0 s e = \<tau> A\<^sub>1 s e \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d\<close>
  and P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI: \<open>finite_trans B\<^sub>0 \<Longrightarrow> finite_trans B\<^sub>1 \<Longrightarrow> \<S>\<^sub>F B\<^sub>0 = \<S>\<^sub>F B\<^sub>1 \<Longrightarrow> 
                   \<forall> s e. \<tau> B\<^sub>0 s e = \<tau> B\<^sub>1 s e \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>0\<rbrakk>\<^sub>n\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>1\<rbrakk>\<^sub>n\<^sub>d\<close>
proof (simp_all add: \<epsilon>_simps)[2]
  assume a1: \<open>\<S>\<^sub>F A\<^sub>0 = \<S>\<^sub>F A\<^sub>1\<close> and a2: \<open>\<forall>s e. \<tau> A\<^sub>0 s e = \<tau> A\<^sub>1 s e\<close>
  have \<open>\<forall>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec) (auto simp add: \<epsilon>_simps a1 a2)
  also have \<open>\<forall>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_rec) (auto simp add: \<epsilon>_simps a1 a2)
  ultimately show \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d\<close> by (intro ext FD_antisym) blast+
next
  assume finite_trans: \<open>finite_trans B\<^sub>0\<close> \<open>finite_trans B\<^sub>1\<close>
     and a1: \<open>\<S>\<^sub>F B\<^sub>0 = \<S>\<^sub>F B\<^sub>1\<close> and a2: \<open>\<forall>s e. \<tau> B\<^sub>0 s e = \<tau> B\<^sub>1 s e\<close>
  have \<open>\<forall>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>1\<rbrakk>\<^sub>n\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>1\<rbrakk>\<^sub>n\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec) (auto simp add: \<epsilon>_simps a1 a2 finite_trans)
  also have \<open>\<forall>s. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>1\<rbrakk>\<^sub>n\<^sub>d s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s\<close>
    apply (induct rule: fix_ind[of \<open>\<lambda>x. \<forall>s. x s \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s\<close>],
           simp add: cont2mono cont_fun, simp)
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec) (auto simp add: \<epsilon>_simps a1 a2 finite_trans)
  ultimately show \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>0\<rbrakk>\<^sub>n\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<^sub>1\<rbrakk>\<^sub>n\<^sub>d\<close> by (intro ext FD_antisym) blast+
qed
   


subsubsection \<open>We establish now a much more powerful theorem.\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong:
  assumes     inj_on_f : \<open>inj_on f (\<R>\<^sub>n\<^sub>d A\<^sub>0 s)\<close>
      and finite_trans : \<open>finite_trans A\<^sub>0\<close> \<open>finite_trans A\<^sub>1\<close>
      and     eq_trans : \<open>\<forall>e. \<forall>s' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s. \<tau> A\<^sub>1 (f s') e = f ` (\<tau> A\<^sub>0 s' e)\<close>
      and       eq_fin : \<open>\<R>\<^sub>n\<^sub>d A\<^sub>1 (f s) = f ` \<R>\<^sub>n\<^sub>d A\<^sub>0 s \<Longrightarrow> \<R>\<^sub>n\<^sub>d A\<^sub>1 (f s) \<inter> \<S>\<^sub>F A\<^sub>1 = f ` (\<R>\<^sub>n\<^sub>d A\<^sub>0 s \<inter> \<S>\<^sub>F A\<^sub>0)\<close>
   
    shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>n\<^sub>d (f s)\<close>
proof -
  have eq_enabl: \<open>s' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s \<Longrightarrow> \<epsilon> A\<^sub>0 s' = \<epsilon> A\<^sub>1 (f s')\<close> for s'
    using eq_trans by (auto simp add: \<epsilon>_simps)
  note bij_betw_f = bij_betw_\<R>\<^sub>n\<^sub>d_if_same_\<tau>[OF inj_on_f eq_trans]

  have \<open>\<forall>s'. s' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s \<longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>n\<^sub>d (f s') \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s'\<close>
    proof (induct rule: fix_ind_k[of \<open>\<lambda>x. \<forall>s'. s' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s \<longrightarrow> x (f s') \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s'\<close> 1],
           simp add: cont_fun monofunI, simp)
      case (step x)
      note step' = step[rule_format, of 0,  simplified]
      show ?case
        apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec[OF finite_trans(1)], simp add: finite_trans(2), safe)
          apply (subgoal_tac False, blast)
          apply (metis Int_iff bij_betw_def bij_betw_f eq_fin imageI inf_le1 inj_on_image_mem_iff)
         apply (metis Int_iff bij_betw_def bij_betw_f eq_fin imageI)
        apply (subst eq_enabl, assumption)
        apply (rule mono_Mprefix_FD[rule_format])
        apply (rule trans_FD[OF _ mono_MultiNdet_FD[rule_format, OF _ step']])
          apply (subst inj_on_mapping_over_MultiNdet[where f = \<open>f\<close>])
            apply (simp add: finite_trans(1))
           apply (meson \<R>\<^sub>n\<^sub>d.step inj_on_def inj_on_f)
          apply (simp add: eq_trans f_inv_into_f finite_trans(1))
         apply (simp add: finite_trans(1))
        by (meson \<R>\<^sub>n\<^sub>d.step)
    qed
  
  also have \<open>\<forall>s'. s' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s \<longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s' \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>n\<^sub>d (f s')\<close>
    proof (induct rule: fix_ind_k[of \<open>\<lambda>x. \<forall>s'. s' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s \<longrightarrow> x s' \<sqsubseteq>\<^sub>F\<^sub>D P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>n\<^sub>d (f s')\<close> 1],
           simp add: cont_fun monofunI, simp)
      case (step x)
      note step' = step[rule_format, of 0, simplified]
      show ?case
        apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_rec[OF finite_trans(2)], simp add: finite_trans(1), safe)
          apply (metis (no_types, opaque_lifting) Int_iff bij_betw_def bij_betw_f eq_fin imageI)
         apply (subgoal_tac False, blast)
         apply (metis Int_iff bij_betw_def bij_betw_f eq_fin imageI inf_le1 inj_on_image_mem_iff)
        apply (subst eq_enabl, assumption)
        apply (rule mono_Mprefix_FD[rule_format])
        apply (rule trans_FD[OF mono_MultiNdet_FD[rule_format, OF _ step']])
          apply (simp add: finite_trans(1))
         apply (meson \<R>\<^sub>n\<^sub>d.step)
        apply (subst inj_on_mapping_over_MultiNdet[where f = \<open>f\<close>])
          apply (simp add: finite_trans(1))
         apply (meson \<R>\<^sub>n\<^sub>d.step inj_on_def inj_on_f)
        by (simp add: eq_trans f_inv_into_f finite_trans(1))
    qed
  ultimately show ?thesis by (meson FD_antisym \<R>\<^sub>n\<^sub>d.init)
qed


(*move this*)
lemma  \<R>\<^sub>d_\<S>\<^sub>F_useless: \<open>\<R>\<^sub>d (A\<lparr>\<S>\<^sub>F := {}\<rparr>) s = \<R>\<^sub>d A s\<close>
  and \<R>\<^sub>n\<^sub>d_\<S>\<^sub>F_useless: \<open>\<R>\<^sub>n\<^sub>d (B\<lparr>\<S>\<^sub>F := {}\<rparr>) s = \<R>\<^sub>n\<^sub>d B s\<close>  
  by (safe, (erule \<R>\<^sub>d.induct, simp_all add: \<R>\<^sub>d.init \<R>\<^sub>d.step)+,
            (erule \<R>\<^sub>n\<^sub>d.induct, simp_all add: \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step)+)


theorem P_ndI_strong:
  assumes     inj_on_f : \<open>inj_on f (\<R>\<^sub>n\<^sub>d A\<^sub>0 s)\<close>
      and finite_trans : \<open>finite_trans A\<^sub>0\<close> \<open>finite_trans A\<^sub>1\<close>
      and     eq_trans : \<open>\<forall>e. \<forall> s' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s. \<tau> A\<^sub>1 (f s') e = f ` (\<tau> A\<^sub>0 s' e)\<close>
    shows \<open>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>n\<^sub>d s = P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>n\<^sub>d (f s)\<close>
  apply (subst (1 2) P_nd_\<S>\<^sub>F_useless, (fact finite_trans)+)
  apply (subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_empty_\<S>\<^sub>F[symmetric], simp, simp)
  by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong) (simp_all add: \<R>\<^sub>n\<^sub>d_\<S>\<^sub>F_useless inj_on_f finite_trans eq_trans)
  


theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_dI_strong:
  \<open>\<lbrakk>inj_on f (\<R>\<^sub>d A\<^sub>0 s); \<forall>e. \<forall>t \<in> \<R>\<^sub>d A\<^sub>0 s. \<tau> A\<^sub>1 (f t) e = map_option f (\<tau> A\<^sub>0 t e);
    \<R>\<^sub>d A\<^sub>1 (f s) = f ` \<R>\<^sub>d A\<^sub>0 s \<Longrightarrow> \<R>\<^sub>d A\<^sub>1 (f s) \<inter> \<S>\<^sub>F A\<^sub>1 = f ` (\<R>\<^sub>d A\<^sub>0 s \<inter> \<S>\<^sub>F A\<^sub>0)\<rbrakk> \<Longrightarrow>
   P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d (f s)\<close>
  apply ((subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_is_some_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd), rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong)
  by (simp_all add: \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d) (auto simp add: det_ndet_conv_defs option.case_eq_if) 

theorem P_dI_strong:
  \<open>inj_on f (\<R>\<^sub>d A\<^sub>0 s) \<Longrightarrow> \<forall>e. \<forall>t \<in> \<R>\<^sub>d A\<^sub>0 s. \<tau> A\<^sub>1 (f t) e = map_option f (\<tau> A\<^sub>0 t e) \<Longrightarrow>
   P\<lbrakk>A\<^sub>0\<rbrakk>\<^sub>d s = P\<lbrakk>A\<^sub>1\<rbrakk>\<^sub>d (f s)\<close>
  apply ((subst (1 2) P_d_is_some_P_nd), rule P_ndI_strong)
  by (simp_all add: \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d) (auto simp add: det_ndet_conv_defs option.case_eq_if)


lemmas P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong_id = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong[where f = id, simplified]
   and      P_ndI_strong_id =      P_ndI_strong[where f = id, simplified]
   and  P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_dI_strong_id =  P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_dI_strong[where f = id, simplified]
   and       P_dI_strong_id =       P_dI_strong[where f = id, simplified]



(*TODO: uniformiser les noms*)
corollary from_s_to_\<sigma>s_eq_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P: \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>A\<rbrakk>\<^sub>d s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>d [s]\<close>
                                  \<open>finite_trans B \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>B\<rbrakk>\<^sub>n\<^sub>d s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<lbrakk>\<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>n\<^sub>d [s]\<close>
   apply (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_dI_strong, simp add: inj_on_def, simp add: s_\<sigma>s_conv_defs map_option_case)
   apply (simp add: \<R>\<^sub>d_from_s_to_\<sigma>s_description, subst s_\<sigma>s_conv_defs, simp add: Setcompr_eq_image)
   apply (rule image_Int[symmetric], simp add: inj_on_def)
  apply (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong, simp add: inj_on_def,
         simp, simp, simp add: Setcompr_eq_image behaviour_s_\<sigma>s_conv(4))
  apply (simp add: \<R>\<^sub>n\<^sub>d_from_s_to_\<sigma>s_description, subst s_\<sigma>s_conv_defs, simp add: Setcompr_eq_image)
  by (rule image_Int[symmetric], simp add: inj_on_def)


corollary from_s_to_\<sigma>s_eq_P: \<open>P\<lbrakk>A\<rbrakk>\<^sub>d s = P\<lbrakk>\<^sub>d\<lbrakk>A\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>d [s]\<close>
                             \<open>finite_trans B \<Longrightarrow> P\<lbrakk>B\<rbrakk>\<^sub>n\<^sub>d s = P\<lbrakk>\<^sub>n\<^sub>d\<lbrakk>B\<rbrakk>\<^sub>s\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rbrakk>\<^sub>n\<^sub>d [s]\<close>
   apply (subst (1 2) P_d_\<S>\<^sub>F_useless, subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_empty_\<S>\<^sub>F[symmetric], simp, simp)
   apply (subst from_s_to_\<sigma>s_eq_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P(1), rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_dI_strong;
          simp add: s_\<sigma>s_conv_defs map_option_case option.case_eq_if)
  apply (subst (1 2) P_nd_\<S>\<^sub>F_useless, simp, assumption,
         subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd_empty_\<S>\<^sub>F[symmetric], simp, simp)
  by (subst from_s_to_\<sigma>s_eq_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P(2), simp, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong, simp_all add: s_\<sigma>s_conv_defs)



text \<open>Behaviour of normalisations. We will use the following methods in Combining theories\<close>

method P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_when_indep_method uses indep R_d_subset R_nd_subset trans_result defs = 
  subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_d_is_some_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_nd, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P_ndI_strong_id[rule_format], simp_all,
  subst (asm) \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d, drule set_mp[OF R_d_subset, rotated],
  (simp add: indep)?, (insert trans_result indep)[1], fastforce,
  rule arg_cong2[where f = \<open>(\<inter>)\<close>], solves simp, simp add: det_ndet_conv_defs defs

method P_when_indep_method uses indep R_d_subset trans_result = 
  subst P_d_is_some_P_nd, rule P_ndI_strong_id[rule_format], simp_all, 
  subst (asm) \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d, drule set_mp[OF R_d_subset, rotated], (simp add: indep)?, (*for arbitrary*)
  (insert trans_result indep)[1], fastforce




(* TODO: reorganize this file, and find a place for the things below *)
\<comment> \<open> this function is the concrete construction of transition function \<tau>\<close>
fun recursive_modifier_fun\<^sub>d :: \<open>[('\<sigma> \<times> 'e) \<Rightarrow> '\<sigma> option, (('\<sigma> \<times> 'e) \<times> '\<sigma> option) list] \<Rightarrow> ('\<sigma> \<times> 'e) \<Rightarrow> '\<sigma> option\<close>
  where \<open>recursive_modifier_fun\<^sub>d f [] = f\<close> (* in recursive_constructor_A\<^sub>d, f = (\<lambda>(s, e). \<diamond>) *)
  |     \<open>recursive_modifier_fun\<^sub>d f (((s, e), t) # \<G>\<^sub>A) = recursive_modifier_fun\<^sub>d (f((s, e) := t)) \<G>\<^sub>A\<close>
\<comment> \<open>in the type : the 1st ('\<sigma> \<times> 'e) \<Rightarrow> '\<sigma> option is the INITIAL \<tau> i.e., f
   (('\<sigma> \<times> 'e) \<times> '\<sigma> option) list is the list of all the concrete transitions in the labelled transit system
     ('\<sigma> \<times> 'e) is the current state and the event to trigger transition
    '\<sigma> option is the updated state\<close>
\<comment> \<open>:= operator is specifically used for updating functions or records.
  It provides a convenient way to locally modify the OUTPUT for a specific INPUT, 
  while keeping the output for other inputs unchanged.\<close>

abbreviation recursive_constructor_A\<^sub>d :: \<open>(('\<sigma> \<times> 'e) \<times> '\<sigma> option) list \<Rightarrow> '\<sigma> set \<Rightarrow> '\<sigma> set \<Rightarrow> ('\<sigma>, 'e) A\<^sub>d\<close>
  where \<open>recursive_constructor_A\<^sub>d \<G>\<^sub>A \<S>\<^sub>F\<^sub>A \<S>\<^sub>I\<^sub>A \<equiv> \<lparr>\<tau> = curry (recursive_modifier_fun\<^sub>d (\<lambda>(s, e). \<diamond>) \<G>\<^sub>A), \<S>\<^sub>F = \<S>\<^sub>F\<^sub>A, \<S>\<^sub>I = \<S>\<^sub>I\<^sub>A\<rparr>\<close>
\<comment> \<open>operator curry transforms a function that takes multiple arguments as a tuple 
    into a sequence of functions that each take one argument.
    The Isabelle definition curry = (\<lambda>c x y. c (x, y)) takes a function c
     that expects a tuple (x, y) and converts it into a function 
    that can be called with x and y separately.\<close>
\<comment> \<open>curry is needed here because the type of \<tau> in Ad is '\<sigma> \<Rightarrow> 'e \<Rightarrow> '\<sigma>, 
    so we need to apply curry to decompose the tuple ('\<sigma> \<times> 'e) \<close>

lemma \<epsilon>_det_breaker: \<open>\<epsilon> \<lparr>\<tau> = curry (g((t::'\<sigma>, e) \<mapsto> u::'\<sigma>)), \<S>\<^sub>F = some_\<S>\<^sub>F, \<S>\<^sub>I = some_\<S>\<^sub>I, \<dots> = some\<rparr> s = 
                      (if s = t then {e} \<union> \<epsilon> \<lparr>\<tau> = curry g, \<S>\<^sub>F = {}, \<S>\<^sub>I = {}\<rparr> t else \<epsilon> \<lparr>\<tau> = curry g, \<S>\<^sub>F = {}, \<S>\<^sub>I = {}\<rparr> s)\<close>
  by (auto simp add: \<epsilon>_simps split: if_splits)

method \<epsilon>_det_calc = ((subst recursive_modifier_fun\<^sub>d.simps)+)?, ((subst \<epsilon>_det_breaker)+, (simp cong: if_cong))+

method \<tau>_det_calc = ((subst recursive_modifier_fun\<^sub>d.simps)+)?, simp cong: if_cong




end 