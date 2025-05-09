theory RS_Deadlock_Freeness
  imports "HOL-CSP_RS" "HOL-CSP_OpSem.OpSem_Deadlock_Results" Guard
begin


(* TODO: change the context in OpSem, no assumption is needed for the following lemmas *)
lemma not_le_F_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>F P)\<close>
  by (fact AfterExt.not_le_F_adm)

lemma not_le_T_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>T P)\<close>
  by (fact AfterExt.not_le_T_adm)

lemma not_le_D_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>D P)\<close>
  by (fact AfterExt.not_le_D_adm)

lemma not_le_FD_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>F\<^sub>D P)\<close>
  by (fact AfterExt.not_le_FD_adm)

lemma not_le_DT_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>D\<^sub>T P)\<close>
  by (fact AfterExt.not_le_DT_adm)


(* TODO: move this if Guard goes to HOL-CSP *)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Guard :
  \<open>b \<^bold>& P \<down> n = (if n = 0 then \<bottom> else b \<^bold>& (P \<down> n))\<close>
  by (simp add: Guard_def)

lemma Guard_non_destuctive : \<open>non_destructive (\<lambda>P. b \<^bold>& P)\<close>
  by (simp add: Guard_def non_destructiveI)

lemma Guard_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp] :
  \<open>non_destructive f \<Longrightarrow> non_destructive (\<lambda>x. b \<^bold>& f x)\<close>
  \<open>constructive f \<Longrightarrow> constructive (\<lambda>x. b \<^bold>& f x)\<close>
  by (auto intro!: non_destructiveI constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Guard dest!: non_destructiveD constructiveD)









lemma \<open>deadlock_free P \<Longrightarrow> deadlock_free (P \<^bold>; Q)\<close>
  by (metis deadlock_free_implies_lifelock_free lifelock_free_is_non_terminating non_terminating_Seq)


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Seq :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<^bold>; Q)\<close> if df_assms : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q\<close>
proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right, intro ballI impI)
  show \<open>t \<in> \<T> (P \<^bold>; Q) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<^bold>; Q)\<close> for t
  proof (induct t rule: rev_induct)
    from df_assms show \<open>([], UNIV) \<notin> \<F> (P \<^bold>; Q)\<close>
      by (simp add: F_Seq deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right)
  next
    from df_assms(1) have \<open>\<D> P = {}\<close>
      by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free)
    fix t e assume hyp : \<open>t \<in> \<T> (P \<^bold>; Q) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<^bold>; Q)\<close>
    assume \<open>t @ [e] \<in> \<T> (P \<^bold>; Q)\<close> \<open>tF (t @ [e])\<close>
    from this(1) consider \<open>t @ [e] \<in> \<T> P\<close> \<open>tF (t @ [e])\<close>
      | u r v where \<open>t @ [e] = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>v \<in> \<T> Q\<close>
      by (auto simp add: T_Seq \<open>\<D> P = {}\<close>)
    thus \<open>(t @ [e], UNIV) \<notin> \<F> (P \<^bold>; Q)\<close>
    proof cases
      show \<open>t @ [e] \<in> \<T> P \<Longrightarrow> tF (t @ [e]) \<Longrightarrow> (t @ [e], UNIV) \<notin> \<F> (P \<^bold>; Q)\<close>
        by (simp add: F_Seq \<open>\<D> P = {}\<close>)
          (metis F_T deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right
            df_assms tickFree_Cons_iff tickFree_Nil tickFree_append_iff)
    next
      show \<open>t @ [e] = u @ v \<Longrightarrow> u @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> v \<in> \<T> Q \<Longrightarrow>
            (t @ [e], UNIV) \<notin> \<F> (P \<^bold>; Q)\<close> for u r v
        by (simp add: F_Seq \<open>\<D> P = {}\<close>)
          (metis F_T \<open>tF (t @ [e])\<close> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right df_assms tickFree_append_iff)
    qed
  qed
qed



lemma deadlock_free_Seq :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P \<^bold>; Q)\<close>
  \<comment> \<open>Same issue here, we do not need the context of AfterExt.
      Fix this someday, not really mattering for now.\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
      deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Seq deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free ticks_of_Seq)



lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Interrupt :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<triangle> Q)\<close> if df_assms : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q\<close>
proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right, intro ballI impI)
  show \<open>t \<in> \<T> (P \<triangle> Q) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<triangle> Q)\<close> for t
  proof (induct t rule: rev_induct)
    from df_assms show \<open>([], UNIV) \<notin> \<F> (P \<triangle> Q)\<close>
      by (auto simp add: F_Interrupt deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right)
  next
    from df_assms have \<open>\<D> P = {}\<close> \<open>\<D> Q = {}\<close>
      by (simp_all add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free)
    fix t e assume hyp : \<open>t \<in> \<T> (P \<triangle> Q) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<triangle> Q)\<close>
    assume \<open>t @ [e] \<in> \<T> (P \<triangle> Q)\<close> \<open>tF (t @ [e])\<close>
    from this(1) consider \<open>t @ [e] \<in> \<T> P\<close>
      | u v where \<open>t @ [e] = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>v \<in> \<T> Q\<close>
      by (auto simp add: T_Interrupt)
    thus \<open>(t @ [e], UNIV) \<notin> \<F> (P \<triangle> Q)\<close>
    proof cases
      from \<open>tF (t @ [e])\<close> df_assms(1) show \<open>t @ [e] \<in> \<T> P \<Longrightarrow> (t @ [e], UNIV) \<notin> \<F> (P \<triangle> Q)\<close>
        by (auto simp add: F_Interrupt \<open>\<D> P = {}\<close> \<open>\<D> Q = {}\<close> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right)
          (metis F_T \<open>tF (t @ [e])\<close> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right df_assms(2) tickFree_append_iff)
    next
      from \<open>tF (t @ [e])\<close> df_assms(1)
      show \<open>t @ [e] = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> tF u \<Longrightarrow> v \<in> \<T> Q \<Longrightarrow>
            (t @ [e], UNIV) \<notin> \<F> (P \<triangle> Q)\<close> for u v
        by (auto simp add: F_Interrupt \<open>\<D> P = {}\<close> \<open>\<D> Q = {}\<close> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right)
          (metis non_tickFree_tick tickFree_append_iff,
            metis F_T \<open>tF (t @ [e])\<close>,
            metis F_T deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right that(2) tickFree_append_iff)
    qed
  qed
qed


lemma deadlock_free_Interrupt :
  \<open>deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P \<triangle> Q)\<close>
  by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
      deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Interrupt sup_bot.right_neutral ticks_of_Interrupt)



lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Throw :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<Theta> a \<in> A. Q a)\<close>
  if df_assms : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Q a)\<close>
proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right, intro ballI impI)
  show \<open>t \<in> \<T> (P \<Theta> a \<in> A. Q a) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<Theta> a \<in> A. Q a)\<close> for t
  proof (induct t rule: rev_induct)
    from df_assms(1) show \<open>([], UNIV) \<notin> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: F_Throw deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right)
  next
    from df_assms have \<open>\<D> P = {}\<close> by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free)
    fix t e assume hyp : \<open>t \<in> \<T> (P \<Theta> a \<in> A. Q a) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<Theta> a \<in> A. Q a)\<close>
    assume \<open>t @ [e] \<in> \<T> (P \<Theta> a \<in> A. Q a)\<close> \<open>tF (t @ [e])\<close>
    thus \<open>(t @ [e], UNIV) \<notin> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: T_Throw \<open>\<D> P = {}\<close> F_Throw)
        (metis F_T \<open>tF (t @ [e])\<close> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right df_assms
          tickFree_Cons_iff tickFree_append_iff)
  qed
qed

lemma deadlock_free_Throw :
  \<open>deadlock_free (P \<Theta> a \<in> A. Q a)\<close>
  if df_assms : \<open>deadlock_free P\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> deadlock_free (Q a)\<close>
proof (unfold AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, rule conjI)
  have \<open>\<checkmark>s(P \<Theta> a \<in> A. Q a) \<subseteq> \<checkmark>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<checkmark>s(Q a))\<close> by (fact ticks_Throw_subset)
  also have \<open>\<checkmark>s(P) = {}\<close>
    by (metis AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S df_assms(1))
  also have \<open>(\<Union>a\<in>A \<inter> \<alpha>(P). \<checkmark>s(Q a)) = {}\<close>
    using AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S df_assms(2) by fast
  finally show \<open>\<checkmark>s(P \<Theta> a \<in> A. Q a) = {}\<close> by simp
next
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<Theta> a \<in> A. Q a)\<close>
    by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Throw deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S df_assms)
qed





text \<open>Configuration of introduction rules.\<close>

(* TODO: modify in CSPM_Deadlock_Results *)
lemma deadlock_free_GlobalDet :
  \<open>\<lbrakk>A \<noteq> {}; \<And>a. a \<in> A \<Longrightarrow> deadlock_free (P a)\<rbrakk> \<Longrightarrow> deadlock_free (\<box>a \<in> A. P a)\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalDet:
  \<open>\<lbrakk>A \<noteq> {}; \<And>a. a \<in> A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a)\<rbrakk> \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<box>a \<in> A. P a)\<close>
  by (metis GlobalNdet_FD_GlobalDet deadlock_free_GlobalNdet_iff deadlock_free_def trans_FD)
    (metis GlobalNdet_FD_GlobalDet deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet_iff trans_FD)

named_theorems deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset

find_theorems deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S

thm deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write0_iff


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write0 : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (a \<rightarrow> P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write0_iff)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nonempty_SKIPS : \<open>R \<noteq> {} \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (SKIPS R)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIPS)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (c\<^bold>!a \<rightarrow> P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write_iff)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Ndet:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<sqinter> Q)\<close>
  by (simp_all add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Ndet_iff)


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a)) \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Mprefix A P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix_iff)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a)) \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (GlobalNdet A P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet_iff)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mndetprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a)) \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Mndetprefix A P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mndetprefix_iff)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_read :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> c ` A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ((P \<circ> inv_into A c) a)) \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (read c A P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_read_iff)


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_ndet_write_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (ndet_write c A P) \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>a\<in>c ` A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ((P \<circ> inv_into A c) a))\<close>
  by (simp add: ndet_write_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mndetprefix_iff)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_ndet_write :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> c ` A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ((P \<circ> inv_into A c) a)) \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (ndet_write c A P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_ndet_write_iff)


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Sliding :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<rhd> Q)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Ndet Sliding_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det)


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Guard : \<open>b \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (b \<^bold>& P)\<close>
  by simp


find_theorems deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Guard





declare deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIP                           [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_STOP                       [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write0                         [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nonempty_SKIPS                 [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write                          [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Renaming [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Ndet                           [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det                            [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Sliding                        [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Interrupt                      [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Seq                            [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix                        [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet                     [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mndetprefix                    [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_read                           [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_ndet_write                     [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalDet                      [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Throw                          [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Guard                          [deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset]

thm deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_introset





(* TODO: modify in CSPM_Deadlock_Results *)

named_theorems deadlock_free_introset


lemma deadlock_free_write0 : \<open>deadlock_free P \<Longrightarrow> deadlock_free (a \<rightarrow> P)\<close>
  by (simp add: deadlock_free_write0_iff)

lemma deadlock_free_write : \<open>deadlock_free P \<Longrightarrow> deadlock_free (c\<^bold>!a \<rightarrow> P)\<close>
  by (simp add: deadlock_free_write_iff)



lemma deadlock_free_Ndet:
  \<open>deadlock_free    P \<Longrightarrow> deadlock_free    Q \<Longrightarrow> deadlock_free    (P \<sqinter> Q)\<close>
  by (simp_all add: deadlock_free_Ndet_iff)


lemma deadlock_free_Mprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> deadlock_free (P a)) \<Longrightarrow> deadlock_free (Mprefix A P)\<close>
  by (simp add: deadlock_free_Mprefix_iff)

lemma deadlock_free_GlobalNdet :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> deadlock_free (P a)) \<Longrightarrow> deadlock_free (GlobalNdet A P)\<close>
  by (simp add: deadlock_free_GlobalNdet_iff)

lemma deadlock_free_Mndetprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> deadlock_free (P a)) \<Longrightarrow> deadlock_free (Mndetprefix A P)\<close>
  by (simp add: deadlock_free_Mndetprefix_iff)

lemma deadlock_free_read :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> c ` A \<Longrightarrow> deadlock_free ((P \<circ> inv_into A c) a)) \<Longrightarrow> deadlock_free (read c A P)\<close>
  by (simp add: deadlock_free_read_iff)


lemma deadlock_free_ndet_write_iff :
  \<open>deadlock_free (ndet_write c A P) \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>a\<in>c ` A. deadlock_free ((P \<circ> inv_into A c) a))\<close>
  by (simp add: ndet_write_def deadlock_free_Mndetprefix_iff)

lemma deadlock_free_ndet_write :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> c ` A \<Longrightarrow> deadlock_free ((P \<circ> inv_into A c) a)) \<Longrightarrow> deadlock_free (ndet_write c A P)\<close>
  by (simp add: deadlock_free_ndet_write_iff)


lemma deadlock_free_Sliding :
  \<open>deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P \<rhd> Q)\<close>
  by (simp add: deadlock_free_Ndet Sliding_def deadlock_free_Det)

lemma deadlock_free_Guard : \<open>b \<Longrightarrow> deadlock_free P \<Longrightarrow> deadlock_free (b \<^bold>& P)\<close>
  by simp






declare non_deadlock_free_SKIP                   [deadlock_free_introset]
        non_deadlock_free_STOP                   [deadlock_free_introset]
        deadlock_free_write0                     [deadlock_free_introset]
        non_deadlock_free_SKIPS                  [deadlock_free_introset]
        deadlock_free_write                      [deadlock_free_introset]
        deadlock_free_imp_deadlock_free_Renaming [deadlock_free_introset]
        deadlock_free_Ndet                       [deadlock_free_introset]
        deadlock_free_Det                        [deadlock_free_introset]
        deadlock_free_Sliding                    [deadlock_free_introset]
        deadlock_free_Interrupt                  [deadlock_free_introset]
        deadlock_free_Seq                        [deadlock_free_introset]
        deadlock_free_Mprefix                    [deadlock_free_introset]
        deadlock_free_GlobalNdet                 [deadlock_free_introset]
        deadlock_free_Mndetprefix                [deadlock_free_introset]
        deadlock_free_read                       [deadlock_free_introset]
        deadlock_free_ndet_write                 [deadlock_free_introset]
        deadlock_free_GlobalDet                  [deadlock_free_introset]
        deadlock_free_Throw                      [deadlock_free_introset]
        deadlock_free_Guard                      [deadlock_free_introset]


thm deadlock_free_introset


thm deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
text \<open>This rule is of course also important.\<close>






text \<open>The strategy is illustrated below.\<close>


lemma constructive_deadlock_free :
  assumes \<open>P = f P\<close>
      and \<open>constructive f\<close>
      and \<open>\<And>X. deadlock_free X \<Longrightarrow> deadlock_free (f X)\<close>
    shows \<open>deadlock_free P\<close>
proof -
  have \<open>P = (\<upsilon> X. f X)\<close>
    by (metis \<open>P = f P\<close> \<open>constructive f\<close> restriction_fix_unique)
  also have \<open>deadlock_free (\<upsilon> X. f X)\<close>
  proof (induct rule: restriction_fix_ind)
    show \<open>constructive f\<close> by (fact \<open>constructive f\<close>)
  next
    show \<open>adm\<^sub>\<down> deadlock_free\<close> unfolding deadlock_free_def by simp
  next
    show \<open>deadlock_free (DF UNIV)\<close> by (simp add: deadlock_free_def)
  next
    show \<open>\<And>X. deadlock_free X \<Longrightarrow> deadlock_free (f X)\<close> by (fact assms(3))
  qed
  finally show \<open>deadlock_free P\<close> .
qed


lemma constructive_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  assumes \<open>P = f P\<close>
      and \<open>constructive f\<close>
      and \<open>\<And>X. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S X \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f X)\<close>
    shows \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
proof -
  have \<open>P = (\<upsilon> X. f X)\<close>
    by (metis \<open>P = f P\<close> \<open>constructive f\<close> restriction_fix_unique)
  also have \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<upsilon> X. f X)\<close>
  proof (induct rule: restriction_fix_ind)
    show \<open>constructive f\<close> by (fact \<open>constructive f\<close>)
  next
    show \<open>adm\<^sub>\<down> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close> unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def by simp
  next
    show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close> by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)
  next
    show \<open>\<And>X. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S X \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f X)\<close> by (fact assms(3))
  qed
  finally show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> .
qed 















end