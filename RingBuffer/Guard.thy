
theory Guard
  imports "HOL-CSP_OpSem.OpSemLocale"
begin


definition Guard :: \<open>bool \<Rightarrow> 'e process \<Rightarrow> 'e process\<close> (infixl \<open>\<^bold>&\<close> 81)
  where \<open>b \<^bold>& P \<equiv> if b then P else STOP\<close>

lemma Guard_cont [simp] : \<open>cont P \<Longrightarrow> cont (\<lambda>x. b \<^bold>& P x)\<close>
  by (simp add: Guard_def)


lemma Guard_True [simp] : \<open>True \<^bold>& P = P\<close>
  by (simp add: Guard_def)

lemma Guard_False [simp] : \<open>False \<^bold>& P = STOP\<close>
  by (simp add: Guard_def)

lemma Guard_STOP [simp] : \<open>b \<^bold>& STOP = STOP\<close>
  by (simp add: Guard_def)


lemma Guard_Ndet : \<open>b \<^bold>& (P \<sqinter> Q) = b \<^bold>& P \<sqinter> b \<^bold>& Q\<close>
  by (simp add: Guard_def Ndet_id)

lemma Guard_Det : \<open>b \<^bold>& (P \<box> Q) = b \<^bold>& P \<box> b \<^bold>& Q\<close>
  by (simp add: Guard_def Det_id)

(* 
lemma Det_Guard : \<open>(b \<^bold>& P) \<box> Q = (if b then P \<box> Q else Q)\<close>
  by (simp add: Guard_def Det_STOP Det_commute)

 *)

lemma Guard_Sliding : \<open>b \<^bold>& (P \<rhd> Q) = b \<^bold>& P \<rhd> b \<^bold>& Q\<close>
  by (simp add: Guard_def Sliding_id)

lemma Guard_Seq : \<open>b \<^bold>& (P \<^bold>; Q) = b \<^bold>& P \<^bold>; b \<^bold>& Q\<close>
  by (simp add: Guard_def STOP_Seq)

lemma Guard_Sync : \<open>b \<^bold>& (P \<lbrakk>S\<rbrakk> Q) = b \<^bold>& P \<lbrakk>S\<rbrakk> b \<^bold>& Q\<close>
  by (simp add: Guard_def Sync_STOP_STOP)


lemma Guard_Mprefix : \<open>b \<^bold>& (\<box>a\<in>A \<rightarrow> P a) = (\<box>a\<in>{a. a \<in> A \<and> b} \<rightarrow> P a)\<close>
  by (simp add: Guard_def Mprefix_STOP)

lemma Guard_Mndetprefix : \<open>b \<^bold>& (\<sqinter>a\<in>A \<rightarrow> P a) = (\<sqinter>a\<in>{a. a \<in> A \<and> b} \<rightarrow> P a)\<close>
  by (simp add: Guard_def Mndetprefix_STOP)


lemma Guard_Interrupt : \<open>b \<^bold>& (P \<triangle> Q) = b \<^bold>& P \<triangle> b \<^bold>& Q\<close>
  by (simp add: Guard_def Interrupt_STOP_neutral(2))


lemma Guard_Throw : \<open>b \<^bold>& (P \<Theta> a\<in>A. Q a) = b \<^bold>& P \<Theta> a\<in>A. b \<^bold>& Q a\<close>
  by (simp add: Guard_def Throw_STOP)

lemma Guard_Hiding : \<open>b \<^bold>& (P \ S) = b \<^bold>& P \ S\<close>
  by (simp add: Guard_def Hiding_set_STOP)

lemma Guard_Renaming : \<open>b \<^bold>& Renaming P f = Renaming (b \<^bold>& P) f\<close>
  by (simp add: Guard_def Renaming_STOP)


lemma initials_Guard : \<open>(b \<^bold>& P)\<^sup>0 = (if b then P\<^sup>0 else {})\<close>
  by (simp add: Guard_def initials_STOP)


lemma (in After) After_Guard : \<open>b \<^bold>& P after e = (if b then P after e else \<Psi> STOP e)\<close>
  by (simp add : Guard_def After_STOP)

lemma (in AfterExt) After_Guard : \<open>b \<^bold>& P after\<^sub>\<checkmark> e = (if b then P after\<^sub>\<checkmark> e else case e of ev x \<Rightarrow> \<Psi> STOP x | \<checkmark> \<Rightarrow> \<Omega> STOP)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP Guard_def)

lemma (in OpSemTransitions) \<tau>_trans_Guard :
  \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> b \<Longrightarrow> b \<^bold>& P \<leadsto>\<^sub>\<tau> b \<^bold>& P'\<close> by simp


end