(* Same that DeadlockFreedom, but for deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, 28 May 2025*)

theory DeadlockSKIPSFreedom
  imports DeadlockFreedom
begin

(*
default_sort type
no_notation floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)
*)




(*The failure set of a process P that iterates i times over Mndetprefix 
A = {}, then no events can be chosen
 - iterating 0 time, Failures =  \<F> P
 - iterating >0 times, Failures = {(s, X). s = []}
A \<noteq> {},
  - iterating n<i times, Failures = (s, X) and 
    s consists only of events from A and
    at least one event is executable
  - after completing i times, Failures = (s @ t, X) and
    s has exactly i steps, and
    Failures depends on \<F> P
*)
thm F_SKIPS[no_vars]


corollary T_iterate_Mndetprefix_UNIV :
  \<open>\<T> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P) =
   {s. tickFree s \<and> length s < i} \<union>
   {s @ t |s t. tickFree s \<and> length s = i \<and> t \<in> \<T> P}\<close>
  by (simp add: T_iterate_Mndetprefix tickFree_iff_set_range_ev)

corollary D_iterate_Mndetprefix_UNIV :
  \<open>\<D> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P) =
   {s @ t |s t. tickFree s \<and> length s = i \<and> t \<in> \<D> P}\<close>
  by (simp add: D_iterate_Mndetprefix tickFree_iff_set_range_ev)



lemma iterate_Mndetprefix_SKIPS_is :
  \<open>iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> SKIPS R)\<cdot>P =
   (if i = 0 then P else
    (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) \<sqinter>
    (\<sqinter> j \<in> {..<i}. (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R))))\<close>
proof (induct i)
  case 0 show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases i)
    show \<open>i = 0 \<Longrightarrow> ?case\<close> by (simp add: lessThan_Suc)
  next
    have * : \<open>nat.pred ` {0<..<Suc i'} = {..<i'}\<close> for i'
      apply auto
       apply (metis less_Suc0 nat.collapse not_less_eq)
      by (metis Suc_less_eq greaterThanLessThan_iff imageI nat.sel(2) zero_less_Suc)
    have ** : \<open>inj_on nat.pred {0<..<Suc i'}\<close> for i'
      by (metis greaterThanLessThan_iff inj_on_inverseI less_nat_zero_code nat.exhaust_sel)
    have \<open>x \<in> {..<Suc i'} \<Longrightarrow> inv_into {0<..<Suc (Suc i')} nat.pred x = Suc x\<close> for i' x
      by (rule inv_into_f_eq[OF **]) auto
    hence *** : \<open>\<sqinter>x\<in>{..<Suc i'}. iterate (inv_into {0<..<Suc (Suc i')} nat.pred x)\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R) =
                 \<sqinter>x\<in>{..<Suc i'}. iterate (Suc x)\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> for i'
      by (metis (no_types, lifting) mono_GlobalNdet_eq)
    have $ : \<open>\<sqinter>a\<in>A \<rightarrow> \<sqinter>j\<in>{..<Suc i'}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R) =
              \<sqinter>j\<in>{0<..<Suc (Suc i')}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> for i'
    apply (subst inj_on_mapping_over_GlobalNdet[OF **])
      apply (subst *, subst ***)
      apply simp
      apply (cases \<open>A = {}\<close>)
      apply simp
      by (simp add: Mndetprefix_distrib_GlobalNdet lessThan_Suc)
    have $$ : \<open>SKIPS R = \<sqinter>j\<in>{0}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> by simp
    have $$$ : \<open>(\<sqinter>a\<in>A \<rightarrow> \<sqinter>j\<in>{..<Suc i'}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)) \<sqinter> SKIPS R =
                \<sqinter>j\<in>{..<Suc (Suc i')}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> for i'
      apply (subst $, subst $$, subst GlobalNdet_factorization_union, auto)
      by (metis One_nat_def atLeast0LessThan atLeast0_lessThan_Suc_eq_insert_0 atLeastLessThanSuc_atLeastAtMost atLeastSucLessThan_greaterThanLessThan
          image_Suc_lessThan)

    show ?case if \<open>i = Suc i'\<close> for i'
      apply (unfold iterate_Suc Suc.hyps)
      apply (simp add: \<open>i = Suc i'\<close> Mndetprefix_distrib_Ndet)
      apply (subst Ndet_assoc[symmetric], subst $$$) ..
  qed
qed



(* TODO: maybe a version of the following result in the general case ? *)

lemma F_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV :
  \<open>\<F> (\<sqinter> j \<in> {..<i}. (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>(UNIV :: 'a set) \<rightarrow> X)\<cdot>(SKIPS (UNIV :: 'r set)))) =
   (if i = 0 then {(t, X). t = []} else
    {(t, X). tF t \<and> length t < i - 1 \<and> (\<exists>a. ev a \<notin> X)} \<union>
    {(t, X) |t X. tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)} \<union>
    {(t @ [\<checkmark>(r)], X) |t r X. tF t \<and> length t < i})\<close>
proof -
  define S  where \<open>S  \<equiv> \<lambda>j. \<F> (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>(UNIV :: 'a set) \<rightarrow> X)\<cdot>(SKIPS (UNIV :: 'r set)))\<close>
  define S1 where \<open>S1 \<equiv> \<lambda>j. {(t :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, X :: ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k). tF t \<and> length t < j \<and> (\<exists>a. ev a \<notin> X)}\<close>
  define S2 where \<open>S2 \<equiv> \<lambda>j. {(t :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, X :: ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) |t X. tF t \<and> length t = j \<and> (\<exists>r. \<checkmark>(r) \<notin> X)}\<close>
  define S3 where \<open>S3 \<equiv> \<lambda>j. {(t @ [\<checkmark>(r)] :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, X :: ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) |t r X. tF t \<and> length t = j}\<close>
  have \<open>S j = S1 j \<union> S2 j \<union> S3 j\<close> for j
    by (auto simp add: F_iterate_Mndetprefix_UNIV F_SKIPS S_def S1_def S2_def S3_def)
    
  hence \<open>(\<Union>j \<in> {..<i}. S j) =
         (\<Union>j \<in> {..<i}. S1 j) \<union> (\<Union>j \<in> {..<i}. S2 j) \<union> (\<Union>j \<in> {..<i}. S3 j)\<close> by auto
  also have \<open>(\<Union>j \<in> {..<i}. S1 j) = {(t, X). tF t \<and> length t < i - 1 \<and> (\<exists>a. ev a \<notin> X)}\<close>
    by (force simp add: S1_def)
  also have \<open>(\<Union>j \<in> {..<i}. S2 j) = {(t, X) |t X. tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)}\<close>
    by (auto simp add: S2_def)
  also have \<open>(\<Union>j \<in> {..<i}. S3 j) = {(t @ [\<checkmark>(r)], X) |t r X. tF t \<and> length t < i}\<close>
    by (auto simp add: S3_def)
  finally show ?thesis
    apply (cases i, simp_all add: F_STOP F_GlobalNdet S_def)
    using S_def lessThan_Suc by auto
qed





lemma T_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV :
  \<open>\<T> (\<sqinter> j \<in> {..<i}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) =
   {[]} \<union> {t. tF t \<and> length t < i} \<union> {t @ [\<checkmark>(r)] |t r. tF t \<and> length t < i}\<close>
proof -
  have * : \<open>\<And>P. \<T> P = {t. \<exists>X. (t, X) \<in> \<F> P}\<close>
    using F_T T_F_spec by blast
  show ?thesis
    by (auto simp add: "*" F_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV)
qed



lemma D_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV :
  \<open>\<D> (\<sqinter> j \<in> {..<i}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) = {}\<close>
proof -
  have \<open>\<D> (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) = {}\<close> for j
    by (induct j) (simp_all add: D_SKIPS D_Mndetprefix')
  thus \<open>\<D> (\<sqinter> j \<in> {..<i}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) = {}\<close>
    by (auto simp add: D_GlobalNdet)
qed


(* 
  

lemma F_iterate_Mndetprefix :
  \<open>\<F> (iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> SKIPS R)\<cdot>P) =
   (if A = {} then if i = 0 then \<F> P else if R = {} then {(s, X). s = []} else {(s, X). s = []} \<union> {(s, X). \<exists>r\<in>R. s = [\<checkmark>(r)]}
    else
   {(s, X). set s \<subseteq> ev ` A \<and> length s < i \<and> (\<exists>a \<in> A. ev a \<notin> X)} \<union>
   {(s @ t, X)| s t X. set s \<subseteq> ev ` A \<and> length s = i \<and> (t, X) \<in> \<F> P})\<close>
  (is \<open>?lhs P i = (if A = {} then if i = 0 then \<F> P else if R = {} then {(s, X). s = []} else {(s, X). s = []} \<union> {(s, X). \<exists>r\<in>R. s = [\<checkmark>(r)]} else
                   ?rhs1 P i \<union> ?rhs2 P i)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs P i = (if i = 0 then \<F> P else {(s, X). s = []})\<close>
    by (cases i) (simp_all add: F_STOP)
next
  show \<open>?lhs P i = ?rhs1 P i \<union> ?rhs2 P i\<close> if \<open>A \<noteq> {}\<close>
  proof (induct i arbitrary: P)
    show \<open>?lhs P 0 = ?rhs1 P 0 \<union> ?rhs2 P 0\<close> for P by simp
  next
    fix i P assume * : \<open>?lhs P i = ?rhs1 P i \<union> ?rhs2 P i\<close> for P
    let ?tmp = \<open>{(s, X). set s \<subseteq> ev ` A \<and> length s = i \<and> (\<exists>a \<in> A. ev a \<notin> X)}\<close>
    have \<open>?lhs P (Suc i) = ?lhs (\<sqinter>a\<in>A \<rightarrow> P) i\<close>
      by (simp del: iterate_Suc add: iterate_Suc2)
    also from "*" have \<open>\<dots> = ?rhs1 (\<sqinter>a\<in>A \<rightarrow> P) i \<union> ?rhs2 (\<sqinter>a\<in>A \<rightarrow> P) i\<close> .
    also have \<open>\<dots> = ?rhs1 P (Suc i) \<union> ?rhs2 P (Suc i)\<close>
    proof -
      have \<open>?rhs2 (\<sqinter>a\<in>A \<rightarrow> P) i = ?rhs2 P (Suc i) \<union> ?tmp\<close>
      proof (intro subset_antisym subsetI)
        fix s_X assume \<open>s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close>
        then obtain t u X
          where ** : \<open>s_X = (t @ u, X)\<close> \<open>set t \<subseteq> ev ` A\<close>
                    \<open>length t = i\<close> \<open>(u, X) \<in> \<F> (\<sqinter>a \<in> A \<rightarrow> P)\<close> by blast
        from "**"(4) consider a where \<open>a \<in> A\<close> \<open>u = []\<close> \<open>ev a \<notin> X\<close>
          | a u' where \<open>a \<in> A\<close> \<open>u = ev a # u'\<close> \<open>(u', X) \<in> \<F> P\<close>
          by (auto simp add: F_Mndetprefix write0_def F_Mprefix \<open>A \<noteq> {}\<close>)
        thus \<open>s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close>
        proof cases
          show \<open>a \<in> A \<Longrightarrow> u = [] \<Longrightarrow> ev a \<notin> X \<Longrightarrow> s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close> for a
            using "**"(2) by (auto simp add: "**"(1, 3) subset_iff)
        next
          fix a u' assume \<open>a \<in> A\<close> \<open>u = ev a # u'\<close> \<open>(u', X) \<in> \<F> P\<close>
          hence \<open>set (t @ [ev a]) \<subseteq> ev ` A\<close> \<open>length (t @ [ev a]) = Suc i\<close>
                \<open>s_X = ((t @ [ev a]) @ u', X)\<close>
            by (simp_all add: "**"(1, 2, 3))
          with \<open>(u', X) \<in> \<F> P\<close> show \<open>s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close> by blast
        qed
      next
        fix s_X assume \<open>s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close>
        then consider t u X where \<open>s_X = (t @ u, X)\<close> \<open>set t \<subseteq> ev ` A\<close> \<open>length t = Suc i\<close> \<open>(u, X) \<in> \<F> P\<close>
          | s X a where \<open>s_X = (s, X)\<close> \<open>a \<in> A\<close> \<open>set s \<subseteq> ev ` A\<close> \<open>length s = i\<close> \<open>ev a \<notin> X\<close> by auto
        thus \<open>s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close>
        proof cases
          fix t u X assume ** : \<open>s_X = (t @ u, X)\<close> \<open>set t \<subseteq> ev ` A\<close> \<open>length t = Suc i\<close> \<open>(u, X) \<in> \<F> P\<close>
          from "**"(2, 3) obtain a t' where \<open>a \<in> A\<close> \<open>t = t' @ [ev a]\<close> \<open>set t' \<subseteq> ev ` A\<close> \<open>length t' = i\<close>
            by (cases t rule: rev_cases) auto
          moreover from this(2) "**"(1) have \<open>s_X = (t' @ ev a # u, X)\<close> by simp
          moreover have \<open>(ev a # u, X) \<in> \<F> (\<sqinter>a\<in>A \<rightarrow> P)\<close>
            by (simp add: F_Mndetprefix write0_def F_Mprefix \<open>A \<noteq> {}\<close> "**"(4) \<open>a \<in> A\<close>)
          ultimately show \<open>s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close> by blast
        next
          show \<open>\<lbrakk>s_X = (s, X); a \<in> A; set s \<subseteq> ev ` A; length s = i; ev a \<notin> X\<rbrakk>
                \<Longrightarrow> s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close> for s X a
            by (auto simp add: F_Mndetprefix write0_def F_Mprefix)
        qed
      qed
      moreover have \<open>?rhs1 (\<sqinter>a\<in>A \<rightarrow> P) i \<union> ?tmp = ?rhs1 P (Suc i)\<close>by auto
      ultimately show \<open>?rhs1 (\<sqinter>a\<in>A \<rightarrow> P) i \<union> ?rhs2 (\<sqinter>a\<in>A \<rightarrow> P) i =
                       ?rhs1 P (Suc i) \<union> ?rhs2 P (Suc i)\<close> by auto
    qed
    finally show \<open>?lhs P (Suc i) = ?rhs1 P (Suc i) \<union> ?rhs2 P (Suc i)\<close> .
  qed
qed



corollary T_iterate_Mndetprefix :
  \<open>\<T> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) =
   (if A = {} then if i = 0 then \<T> P else {[]}
    else {s. set s \<subseteq> ev ` A \<and> length s < i} \<union>
         {s @ t| s t. set s \<subseteq> ev ` A \<and> length s = i \<and> t \<in> \<T> P})\<close>
  unfolding set_eq_iff
  by (auto simp add: F_iterate_Mndetprefix T_F_spec[symmetric])


lemma D_iterate_Mndetprefix :
  \<open>\<D> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) =
   (if A = {} then if i = 0 then \<D> P else {}
    else {s @ t| s t. set s \<subseteq> ev ` A \<and> length s = i \<and> t \<in> \<D> P})\<close>
  (is \<open>?lhs P i = (if A = {} then if i = 0 then \<D> P else {} else ?rhs P i)\<close>)
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs P i = (if i = 0 then \<D> P else {})\<close>
    by (cases i) (simp_all add: D_STOP)
next
  show \<open>?lhs P i = ?rhs P i\<close> if \<open>A \<noteq> {}\<close>
  proof (induct i arbitrary: P)
    show \<open>?lhs P 0 = ?rhs P 0\<close> for P by simp
  next
    fix i P assume * : \<open>?lhs P i = ?rhs P i\<close> for P
    have \<open>?lhs P (Suc i) = ?lhs (\<sqinter>a \<in> A \<rightarrow> P) i\<close>
      by (simp del: iterate_Suc add: iterate_Suc2)
    also from "*" have \<open>\<dots> = ?rhs (\<sqinter>a \<in> A \<rightarrow> P) i\<close> .
    also have \<open>\<dots> = ?rhs P (Suc i)\<close>
    proof safe
      fix s t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>set s \<subseteq> ev ` A\<close> \<open>t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close> \<open>i = length s\<close>
      from \<open>t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close>
      obtain a t' where \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>t' \<in> \<D> P\<close>
        by (auto simp add: D_Mndetprefix write0_def D_Mprefix \<open>A \<noteq> {}\<close>)
      from this(1, 2) have \<open>s @ t = (s @ [ev a]) @ t'\<close> \<open>set (s @ [ev a]) \<subseteq> ev ` A\<close>
                           \<open>length (s @ [ev a]) = Suc (length s)\<close>
        by (simp_all add: \<open>set s \<subseteq> ev ` A\<close>)
      with \<open>t' \<in> \<D> P\<close> show \<open>\<exists>s' t'. s @ t = s' @ t' \<and> set s' \<subseteq> ev ` A \<and>
                                     length s' = Suc (length s) \<and> t' \<in> \<D> P\<close> by blast
    next
      fix s t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
      assume \<open>set s \<subseteq> ev ` A\<close> \<open>length s = Suc i\<close> \<open>t \<in> \<D> P\<close>
      from this(1, 2) obtain a s'
        where \<open>a \<in> A\<close> \<open>s = s' @ [ev a]\<close> \<open>set s' \<subseteq> ev ` A\<close> \<open>length s' = i\<close>
        by (cases s rule: rev_cases) auto
      from this(1, 2) \<open>t \<in> \<D> P\<close> have \<open>s @ t = s' @ ev a # t\<close> \<open>ev a # t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close>
        by (simp_all add: D_Mndetprefix write0_def D_Mprefix \<open>A \<noteq> {}\<close>)
      with \<open>set s' \<subseteq> ev ` A\<close> \<open>length s' = i\<close> 
      show \<open>\<exists>s' t'. s @ t = s' @ t' \<and> set s' \<subseteq> ev ` A \<and>
                    length s' = i \<and> t' \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close> by blast
    qed
    finally show \<open>?lhs P (Suc i) = ?rhs P (Suc i)\<close> .
  qed
qed


lemma tickFree_iff_set_range_ev : \<open>tickFree s \<longleftrightarrow> set s \<subseteq> range ev\<close>
  by (metis (no_types, lifting) Hiding_tickFree empty_filter_conv image_mono list.set_map subset_code(1)
      tickFree_iff_is_map_ev top_greatest)

text\<open>when A = UNIV, the failure set of a process P that iterates i times over Mndetprefix on A\<close>
corollary F_iterate_Mndetprefix_UNIV :
  \<open>\<F> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P) =
   {(s, X). tickFree s \<and> length s < i \<and> (\<exists>a. ev a \<notin> X)} \<union>
   {(s @ t, X) |s t X. tickFree s \<and> length s = i \<and> (t, X) \<in> \<F> P}\<close>
  by (simp add: F_iterate_Mndetprefix tickFree_iff_set_range_ev)

corollary T_iterate_Mndetprefix_UNIV :
  \<open>\<T> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P) =
   {s. tickFree s \<and> length s < i} \<union>
   {s @ t |s t. tickFree s \<and> length s = i \<and> t \<in> \<T> P}\<close>
  by (simp add: T_iterate_Mndetprefix tickFree_iff_set_range_ev)

corollary D_iterate_Mndetprefix_UNIV :
  \<open>\<D> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P) =
   {s @ t |s t. tickFree s \<and> length s = i \<and> t \<in> \<D> P}\<close>
  by (simp add: D_iterate_Mndetprefix tickFree_iff_set_range_ev)





 *)






text\<open>this extends iterate i indefinitely, allowing P to be prefixed by an arbitrary but finite number (>0) of Mndetprefix, with the number of iterations being Ndet\<close>
definition GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>)\<close> [1000] 999)
  where \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<equiv> \<sqinter>i \<in> {0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P\<close>


text \<open>This new operator, which uses the * syntax, says that we can perform 0 or more events and then behave as P. These two operators  ought to be linked together with some lemmas. 24Jan25\<close>
definition GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close> [1000] 999)
  where \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<equiv> \<sqinter>i \<in> UNIV. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P\<close>
  (* UNIV = {0..} *)


lemma GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_is_Ndet_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations : \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = P \<sqinter> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close>
proof -
  have \<open>UNIV = insert (0 :: nat) {0<..}\<close> by fast
  have \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = \<sqinter> i\<in>UNIV. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow>  X) \<sqinter> SKIPS UNIV)\<cdot>P\<close>
    by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def)
  also have \<open>\<dots> = iterate 0\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P \<sqinter>
                  (\<sqinter> i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P)\<close>
    apply (subst \<open>UNIV = insert (0 :: nat) {0<..}\<close>)
    apply (subst GlobalNdet_distrib_unit)
    by simp_all
  also have \<open>iterate 0\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P = P\<close> by simp
  also have \<open>(\<sqinter> i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P) = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close>
    by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def)
  finally show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = P \<sqinter> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close> .
qed


lemma GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_Mndetprefix : \<open>((\<sqinter>a\<in>UNIV \<rightarrow> P) \<sqinter> SKIPS UNIV)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close>
proof -
  have \<open>((\<sqinter>a\<in>UNIV \<rightarrow> P) \<sqinter> SKIPS UNIV)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> =
        \<sqinter>i\<in>UNIV. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>((\<sqinter>a\<in>UNIV \<rightarrow> P) \<sqinter> SKIPS UNIV)\<close>
    by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def)
  also have \<open>\<dots> = \<sqinter> i\<in>UNIV. iterate (Suc i)\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P\<close>
    by (rule mono_GlobalNdet_eq) (simp del: iterate_Suc add: iterate_Suc2)
  also have \<open>\<dots> = \<sqinter> i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P\<close>
    by (auto simp add: inj_on_mapping_over_GlobalNdet[of Suc UNIV, simplified]
        greaterThan_0 intro: mono_GlobalNdet_eq)
  also have \<open>\<dots> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close> by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def)
  finally show \<open>((\<sqinter>a\<in>UNIV \<rightarrow> P) \<sqinter> SKIPS UNIV)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close> .
qed



lemma GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations' :
  \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> = (\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>) \<sqinter> SKIPS UNIV\<close>
proof (unfold GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def)
  have * : \<open>{0<..} = {Suc 0<..} \<union> {Suc 0}\<close> by auto
  have ** : \<open>Suc ` {0<..} = {Suc 0<..}\<close>
    by (metis atLeast_Suc_greaterThan image_add_atLeast plus_1_eq_Suc)
  have *** : \<open>i \<in> {Suc 0<..} \<Longrightarrow> inv_into {0<..} Suc i = nat.pred i\<close> for i
    by (metis "**" f_inv_into_f nat.sel(2))
  have **** : \<open>Suc 0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P =
                             (\<sqinter>a\<in>UNIV \<rightarrow> iterate (nat.pred i)\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P) \<sqinter> SKIPS UNIV\<close> for i
    by (cases i) simp_all
  have \<open>\<sqinter>i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P =
        (\<sqinter>i\<in>{Suc 0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P) \<sqinter> ((\<sqinter>a\<in>UNIV \<rightarrow> P) \<sqinter> SKIPS UNIV)\<close>
    by (subst "*", subst GlobalNdet_factorization_union[symmetric]) simp_all
  also have \<open>\<sqinter>i\<in>{Suc 0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P = \<sqinter>i\<in>{0<..}. iterate (Suc i)\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P\<close>
    apply (subst inj_on_mapping_over_GlobalNdet[of Suc \<open>{0<..}\<close>])
     apply (solves simp)
    apply (simp add: "**")
    apply (rule mono_GlobalNdet_eq)
    by (simp add: "***" "****")
    

  also have \<open>\<dots> \<sqinter> ((\<sqinter>a\<in>UNIV \<rightarrow> P) \<sqinter> SKIPS UNIV) =
             (\<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>i\<in>UNIV. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P) \<sqinter> SKIPS UNIV\<close>
  (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec, safe)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (simp add: D_Ndet D_GlobalNdet D_Mndetprefix' iterate_Mndetprefix_SKIPS_is
          D_iterate_Mndetprefix_UNIV D_SKIPS) blast
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (auto simp add: D_Ndet D_GlobalNdet D_Mndetprefix' iterate_Mndetprefix_SKIPS_is
          D_iterate_Mndetprefix_UNIV D_SKIPS split: if_split_asm)
  next
    show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
      apply (cases t; cases \<open>tl t\<close>, simp_all add: F_Ndet F_GlobalNdet F_Mndetprefix' iterate_Mndetprefix_SKIPS_is
          F_iterate_Mndetprefix_UNIV F_SKIPS split: if_split_asm)
          apply blast
         apply blast apply blast
         apply (metis One_nat_def append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust insertI1 last_snoc lessThan_Suc zero_neq_one)
        apply blast defer apply blast 
      apply safe
      using lessThan_0 apply auto[1]
                          apply simp_all
      apply (simp_all add: lessThan_Suc)
      apply (metis Zero_not_Suc lessI) 
                      apply (metis gr_implies_not_zero) 
      using is_ev_def apply (blast+)[5]
      apply (metis Suc_lessD bot.extremum_strict)
      apply (metis Suc_lessD bot.extremum_strict)
      apply blast
             apply (meson is_ev_def tickFree_Cons_iff)
      apply (metis Zero_not_Suc append.right_neutral insertI1 lessThan_Suc lessThan_empty_iff tickFree_Cons_iff)
      apply (metis bot.extremum_strict)
      apply force
         apply (metis front_tickFree_Cons_iff front_tickFree_append is_ev_def list.distinct(1))
        apply (simp add: Cons_eq_append_conv)
        apply safe
         apply (metis insertI1 lessThan_Suc lessThan_empty_iff list.size(3) n_not_Suc_n tickFree_Nil)
        apply (metis Zero_not_Suc insertI1 lessThan_Suc lessThan_empty_iff tickFree_Cons_iff)
       apply (metis less_zeroE)
      by auto
  next
    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
      apply (simp add: F_Ndet F_GlobalNdet F_Mndetprefix' iterate_Mndetprefix_SKIPS_is
          F_iterate_Mndetprefix_UNIV F_SKIPS lessThan_empty_iff split: if_split_asm)
       
          apply auto
      apply (metis append.right_neutral event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) greaterThan_def insertI1 length_Cons lessThan_Suc mem_Collect_eq
          tickFree_Cons_iff zero_less_Suc) 
      by (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) greaterThan_0 lessThan_iff less_Suc_eq rangeI tickFree_Cons_iff)
  qed

  finally show \<open>\<sqinter>i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P =
        (\<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>i\<in>UNIV. iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P) \<sqinter> SKIPS UNIV\<close> .
qed




text\<open>Benoit 30Jan, changed from \<open>\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c*  \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> to  \<longleftrightarrow>\<close>

lemma one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_FD_iff_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_FD :
  \<open>(\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>) \<sqinter> SKIPS UNIV  \<sqsubseteq>\<^sub>F\<^sub>D Q \<longleftrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations')



text \<open>This law would allow us to break down the proof into an initial event step, followed by an arbitrary number  of steps. Then we could try and prove laws like the one below.
This means that if Q can do some number of events and then behave as P, then Q prefixed by a   can also do some number of steps and then behave as P. It seems to be intuitively true, but we  can't prove it. It would however avoid needing to pick the number of steps to make before recursing, which would facilitate fully automated proof.\<close>
lemma eat_lemma: \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close> if \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
proof (rule trans_FD)
  show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> Q\<close>
    apply (subst GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_is_Ndet_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations)
    by (metis (no_types, lifting) GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'
        Ndet_FD_self_right Ndet_commute dual_order.trans mono_Mndetprefix_FD that)
  next
  show \<open>(\<sqinter>a\<in>UNIV \<rightarrow> Q) \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close>
    by (simp add: prefix_proving_Mndetprefix_UNIV_ref(3))
qed



lemma GlobalNdet_reduce_prefix:
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q"
  by (metis GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations' Ndet_FD_self_left assms prefix_proving_Mndetprefix_UNIV_ref(3) trans_FD)

lemma GlobalNdet_reduce_read:
  assumes "inj a" "\<And> v. P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q v"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D a\<^bold>?x \<rightarrow> Q x"
  by (metis (no_types, lifting) FD_iff_eq_Ndet GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations' Ndet_FD_self_left assms(1,2) empty_not_UNIV
      mono_Ndet_FD order_antisym_conv read_proving_Mndetprefix_UNIV_ref)

lemma GlobalNdet_reduce_write:
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D a\<^bold>!v \<rightarrow> Q"
  by (simp add: GlobalNdet_reduce_prefix assms write_is_write0)


lemma GlobalNdet_Skip: "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Skip"
  by (metis GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_is_Ndet_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'
      Ndet_FD_self_right SKIPS_singl_is_SKIP UNIV_unit trans_FD)



lemma iterate_F_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_F :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F Q\<close>
  by (unfold GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def)
    (meson GlobalNdet_refine_F greaterThan_iff trans_F)

lemma iterate_T_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_T :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>T Q\<close>
  by (unfold GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def)
     (meson GlobalNdet_refine_F greaterThan_iff leF_imp_leT trans_T)

lemma iterate_D_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_D :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>D Q\<close>
  by (unfold GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def)
     (meson GlobalNdet_refine_FD greaterThan_iff leFD_imp_leD trans_D)

lemma iterate_FD_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_FD :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (metis iterate_D_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_D
            iterate_F_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_F
              leFD_imp_leD leFD_imp_leF leF_leD_imp_leFD)

lemma iterate_DT_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_DT :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (metis iterate_D_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_D
            iterate_T_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_T
            leDT_imp_leD leDT_imp_leT leD_leT_imp_leDT)


thm GlobalNdet_iterations_F_imp_deadlock_free
lemma GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_F_imp_deadlock_free :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> if \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F P\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
(* proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right, intro ballI impI)
  show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F P \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> P\<close> for t
  proof (induct t arbitrary: P rule: rev_induct)
    case Nil
    from Nil.prems(1) show ?case
      by (subst (asm) GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations')
        (auto simp add: failure_refine_def F_Ndet F_Mndetprefix' F_SKIPS subset_iff)
  next
    case (snoc e t)
    from \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F P\<close> have \<open>(\<sqinter>a \<in> UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F (\<sqinter>a \<in> UNIV \<rightarrow> P) \<sqinter> SKIPS UNIV\<close>
      by (simp add: mono_Mndetprefix_F mono_Ndet_F)
    show ?case
      
      
    fix X t assume \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> P\<close>
    show \<open>\<close>
     apply simp_all
    sledgehammer
proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct arbitrary: P rule: cont_fix_ind)
  show \<open>cont (\<lambda>x. (\<sqinter>a\<in>UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV)\<close> by simp
next
  show \<open>adm (\<lambda>a. \<forall>P. P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F P \<longrightarrow> a \<sqsubseteq>\<^sub>F P)\<close> by simp
next
  show \<open>\<And>P. \<bottom> \<sqsubseteq>\<^sub>F P\<close> by simp
next
  fix X P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assume hyp : \<open>\<And>P. P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F P \<Longrightarrow> X \<sqsubseteq>\<^sub>F P\<close> \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F P\<close>
  thm GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_Mndetprefix
  show \<open>(\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F P\<close>
    find_theorems \<open>?P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close> *)
proof -
  have \<open>\<F> P \<subseteq> \<F> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>)\<close> by (meson failure_refine_def \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F P\<close>)
  find_theorems \<F> \<open>?P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close>
  find_theorems \<open>iterate ?i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<cdot>?P\<close>
  moreover have \<open>\<dots> = (\<Union>i\<in>{0<..}. {(s, X). tF s \<and> length s < i \<and> (\<exists>a. ev a \<notin> X)} \<union> {(s @ t, X) |s t X. tF s \<and> length s = i \<and> (t, X) \<in> \<F> P} \<union>
        {(t, X). tF t \<and> length t < i - 1 \<and> (\<exists>a. ev a \<notin> X)} \<union> {(t, X). tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)} \<union>
         {(t @ [\<checkmark>(r)], X) | t r X. tF t \<and> length t < i})\<close>
    find_theorems iterate name: "then"
    by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def F_GlobalNdet)
      (simp add: iterate_Mndetprefix_SKIPS_is F_Ndet
        F_iterate_Mndetprefix_UNIV F_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV Un_assoc)
  moreover have \<open>\<dots> = (\<Union>i\<in>{0<..}. {(s, X). tF s \<and> length s < i \<and> (\<exists>a. ev a \<notin> X)} \<union> {(s @ t, X) |s t X. tF s \<and> length s = i \<and> (t, X) \<in> \<F> P} \<union>
         {(t, X). tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)} \<union>
         {(t @ [\<checkmark>(r)], X) | t r X. tF t \<and> length t < i})\<close>
    apply safe apply simp_all
    by blast+
  
  moreover have \<open>tF t \<Longrightarrow> (t, UNIV) \<in> \<dots> \<Longrightarrow> False\<close> for t
  proof (induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons e t)
    from Cons.prems obtain u v i a
      where \<open>e = ev a\<close> \<open>ev a # t = u @ v\<close> \<open>tF u\<close> \<open>length u = i\<close> \<open>(v, UNIV) \<in> \<F> P\<close> \<open>0 < i\<close>
      apply (cases t, simp_all)
    apply (metis Cons.prems(1) Zero_not_Suc event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) f_inv_into_f greaterThan_0 length_greater_0_conv
        list.size(3) non_tickFree_tick)
      by (metis Cons.prems(1) greaterThan_iff is_ev_def non_tickFree_tick tickFree_append_iff)
    hence \<open>(t, UNIV) \<in> (\<Union>i\<in>{0<..}.
          {a. case a of (s, X) \<Rightarrow> tF s \<and> length s < i \<and> (\<exists>a. ev a \<notin> X)} \<union>
          {(s @ t, X) |s t X. tF s \<and> length s = i \<and> (t, X) \<in> \<F> P} \<union>
          {a. case a of (t, X) \<Rightarrow> tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)} \<union>
          {(t @ [\<checkmark>(r)], X) |t r X. tF t \<and> length t < i})\<close>
      apply (cases u, simp_all)
      by (metis (lifting) Cons.hyps Cons.prems(1) Suc_pred append_self_conv2 calculation(1,2,3) greaterThan_0 in_mono
          length_greater_0_conv rangeI tickFree_Cons_iff)
    with Cons.hyps Cons.prems(1) tickFree_Cons_iff show False by blast
  qed
  ultimately show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
    by (metis (lifting) deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right in_mono)
qed

lemma GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_FD_imp_deadlock_free :
  \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_F_imp_deadlock_free leFD_imp_leF)

(* text \<open>This would be a useful lemma to have, because it would allow us to have an operator that simply does n event steps.  SKIP updated to Skip 25Feb\<close>
lemma iterate_is_iterate_SKIP_Seq :  \<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P = iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>Skip \<^bold>; P\<close>
proof (induct i)
  show \<open>iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P =
        iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>Skip \<^bold>; P\<close> by simp
next
  fix i assume hyp : \<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P = iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>Skip \<^bold>; P\<close>
  show \<open>iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P =
        iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>Skip \<^bold>; P\<close>
    by (auto simp add: Mndetprefix_Seq intro: mono_Mndetprefix_eq hyp)
qed *)




text\<open>Benoit 30Jan\<close>
lemma GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations' : \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>\<close>
proof -
  have \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close>
  proof (unfold refine_defs, safe)
    show \<open>t \<in> \<D> ((P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>) \<Longrightarrow> t \<in> \<D> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close> for t
    apply (simp add: D_Ndet GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def
        D_GlobalNdet iterate_Mndetprefix_SKIPS_is D_iterate_Mndetprefix_UNIV D_SKIPS split: if_split_asm)
      by (metis append.assoc append_Nil length_0_conv less_numeral_extra(3) tickFree_append_iff)
  next
    show \<open>(t, X) \<in> \<F> ((P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>) \<Longrightarrow> (t, X) \<in> \<F> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close> for t X
      apply (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_def F_GlobalNdet
          iterate_Mndetprefix_SKIPS_is F_iterate_Mndetprefix_UNIV F_Ndet F_SKIPS lessThan_empty_iff split: if_split_asm)
      apply (simp add: greaterThan_0 lessThan_Suc)
      apply (elim exE disjE)
          apply auto[1]
         defer
      apply auto[1]
        apply ((metis Zero_not_Suc insertI1 lessThan_Suc)+)[2]
      apply (elim conjE exE)
      apply (elim disjE)
      apply simp_all
      
        defer
        apply blast
       apply safe
                          apply simp_all
      apply (blast+)[6]
      apply (metis add_Suc append.assoc length_append old.nat.distinct(1) tickFree_append_iff)
      apply force
      apply (metis append.assoc append_is_Nil_conv length_0_conv tickFree_append_iff)
                        apply auto[1]
      apply (metis Suc_neq_Zero append_Nil2 lessI lessThan_iff)
      apply (blast+)[13]
      apply (metis append_assoc append_is_Nil_conv length_0_conv tickFree_append_iff)
      apply (metis Zero_not_Suc lessI)
      apply (metis Zero_not_Suc append.right_neutral insertI1 lessThan_Suc tickFree_append_iff)
      apply (metis Zero_not_Suc append.assoc insertI1 lessThan_Suc tickFree_append_iff)
      .
  qed
  have \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqinter> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close>
    by (fact GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_is_Ndet_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations)
  also have \<open>\<dots> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>\<close>
    by (metis FD_iff_eq_Ndet \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>\<close>)
  finally show \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>\<close> .
qed


lemma GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations :
  \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> = (\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark>) \<sqinter> SKIPS UNIV\<close>
  by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_is_one_step_ahead_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'
                GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_Mndetprefix
                GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations')



section\<open>NEW lemmas to be added into HOL-CSP library\<close>
subsection\<open>natural deduction\<close>
(* TODO: rename the lemmas below appropriately *)
lemma eat_read_lemma: 
  assumes "inj c" "\<And> v. P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q v"
  shows \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?v \<rightarrow> Q v\<close>
proof (rule trans_FD)
  show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>\<close>
    by (simp add: Mndetprefix_GlobalNdet eat_lemma mono_GlobalNdet_FD_const)
next
  show "\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>?v \<rightarrow> Q v)"
    apply (rule read_proving_Mndetprefix_UNIV_ref)
      apply (simp_all add: assms)
    done
qed

lemma read_prefix_proving_Mndetprefix_ref :
  assumes "inj c"  "\<And> v. a \<in> UNIV \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q v "
  shows  \<open> (\<sqinter>a \<in> UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>) \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?v \<rightarrow> Q v\<close>
  by (simp add: assms(1,2) read_proving_Mndetprefix_UNIV_ref)

lemma proc_plus_prefix_ref: \<open> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> P\<close>
  apply (unfold write0_def)
  apply (rule trans_FD[OF _ iterate_FD_imp_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_FD[of \<open>Suc 0\<close> \<open>P\<close>]])
  apply simp_all 
  by (metis Ndet_FD_self_left dual_order.eq_iff empty_not_insert
      prefix_proving_Mndetprefix_ref(2) subset_UNIV trans_FD)

lemma proc_plus_read_prefix_ref: 
  assumes "inj c"  "\<And> v. P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q v "
  shows  \<open>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?v \<rightarrow> Q v\<close>
  by (metis DeadlockSKIPSFreedom.eat_read_lemma
      GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_is_Ndet_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations Ndet_FD_self_right assms(1,2)
      trans_FD)


lemma no_step_refine: "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P"
  by (simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_is_Ndet_GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations Ndet_FD_self_left)



text\<open>df_step_intro is not applicable to index/parametrized process\<close>
lemma df_step_intro:
  assumes P_def: "P = Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q"
  shows "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P"
  apply (rule GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_FD_imp_deadlock_free)
  apply (subst P_def)  back (* also works: apply (subst (2) P_def) *)
  apply (simp add: assms(2))
  done


text\<open>This version is for parametrized process\<close>
lemma df_step_param_intro:
  assumes P_def: "\<And> x. P x = Q x" "\<And> x. (GlobalNdet UNIV P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q x"
  shows "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. P n)"
  apply (rule GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations_FD_imp_deadlock_free)
  apply (subst P_def)  back
  apply (simp add: assms(2) mono_GlobalNdet_FD_const)
  done


lemma prefix_recursive_ddlf(*was named ex1_m'*):
  assumes P_def: \<open>P = (a \<rightarrow> P)\<close>
  shows \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (meson assms deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S prefix_recursive_ddlf)




subsection\<open>extchoice\<close>
text\<open>this is added for P = d\<rightarrow>( (a \<rightarrow> b \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P)) pattern: prefix of external choice\<close>
lemma ndet_prefix_ext_choice:
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D R"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> R"
  by (metis mono_Det_FD Det_id assms(1) assms(2))




subsection\<open>guard extchoice generalization\<close>

named_theorems normalisation

lemma GlobalDet_preguard_bis [normalisation] :\<open>\<box>i \<in> I. b i \<^bold>& P i = \<box>i \<in> {i \<in> I. b i}. P i\<close>
proof -
  have \<open>{i \<in> I. b i} \<union> {i \<in> I. \<not> b i} = I\<close> by blast
  hence \<open>\<box> i\<in>I. b i \<^bold>& P i = (\<box>i \<in> {i \<in> I. b i}. b i \<^bold>& P i) \<box> (\<box>i \<in> {i \<in> I. \<not> b i}. b i \<^bold>& P i)\<close>
    by (simp add: GlobalDet_factorization_union)
  also have \<open>\<box>i \<in> {i \<in> I. b i}. b i \<^bold>& P i = \<box>i \<in> {i \<in> I. b i}. P i\<close>
    by (auto intro: mono_GlobalDet_eq)
  also have \<open>\<box>i \<in> {i \<in> I. \<not> b i}. b i \<^bold>& P i = STOP\<close>
    by (simp add: GlobalDet_is_STOP_iff)
  finally show \<open>\<box>i \<in> I. b i \<^bold>& P i = \<box>i \<in> {i \<in> I. b i}. P i\<close> by simp
qed


lemma generalized_refine_guarded_extchoice [normalisation]:
  assumes (* "finite I" *) \<open>\<exists>i\<in>I. b(i)\<close> \<open>\<And> i. \<lbrakk> i \<in> I; b(i) \<rbrakk> \<Longrightarrow> \<sqinter>a \<in> UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D P(i)\<close>
  shows \<open>\<sqinter>a \<in> UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D \<box> i\<in>I. b(i) \<^bold>& P(i)\<close>
  proof (unfold GlobalDet_preguard_bis)
  have \<open>\<box>i \<in> {i \<in> I. b i}. \<sqinter>a \<in> UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D \<box>i \<in> {i \<in> I. b i}. P i\<close>
    by (auto intro: mono_GlobalDet_FD assms(2))
  also have \<open>\<box>i \<in> {i \<in> I. b i}. \<sqinter>a \<in> UNIV \<rightarrow> X = \<sqinter>a \<in> UNIV \<rightarrow> X\<close>
    apply (rule GlobalDet_id)
    using \<open>\<exists>i\<in>I. b(i)\<close> by blast
  finally show \<open>\<sqinter>a \<in> UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D \<box>i \<in> {i \<in> I. b i}. P i\<close> .
qed

lemma generalized_refine_guarded_extchoice_star [normalisation]:
  assumes \<open>\<exists>i\<in>I. b(i)\<close> \<open>\<And> i. \<lbrakk> i \<in> I; b(i) \<rbrakk> \<Longrightarrow> \<sqinter>a \<in> UNIV \<rightarrow> X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P(i)\<close>
  shows \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D \<box> i\<in>I. b(i) \<^bold>& P(i)\<close>
proof (rule trans_FD)
  show \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>\<close>
    by (simp add: Mndetprefix_GlobalNdet eat_lemma mono_GlobalNdet_FD_const)
next
  show "\<sqinter>a\<in>UNIV \<rightarrow> X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D \<box>i\<in>I. b i \<^bold>& P i"
    apply (rule generalized_refine_guarded_extchoice)
    apply (simp_all add: assms)
    done
qed


lemma bi_extchoice_norm [normalisation]:
"b \<^bold>& P \<box> c \<^bold>& Q = \<box> i\<in>{0..1::nat}. (if i = 0 then b else c) \<^bold>&(if i = 0 then P else Q)"
  apply (simp add: GlobalDet_distrib_unit_bis)
  by (smt (verit, ccfv_threshold) Det_commute GlobalDet_factorization_union GlobalDet_unit 
        atLeast0_atMost_Suc atLeastAtMost_singleton insert_is_Un
      old.nat.distinct(1))




text\<open>to push an binary operator term\<open>(\<box>)\<close> into generalized extchoice, this proof does not use induction \<close>
lemma biextchoic_normalization [normalisation]:
  "(\<box> i\<in>{0..n::nat}. b(i) \<^bold>& P(i)) \<box> c \<^bold>& Q 
   = (\<box> i\<in>{0..n+1}. (if i \<le> n then b(i) else c) \<^bold>& (if i \<le> n then P(i) else Q))"
 (is "?lhs = ?rhs")
proof -
  have 1:"{0..Suc n} = insert (Suc n) {0..n}"
    by (simp add: atLeast0_atMost_Suc)
  have "?rhs = 
        c \<^bold>& Q \<box> (\<box>i\<in>{0..n}. (if i \<le> n then b i else c) \<^bold>& (if i \<le> n then P i else Q))"
    by (simp add: 1 GlobalDet_distrib_unit)
  also have "... = (\<box>i\<in>{0..n}. (if i \<le> n then b i else c) \<^bold>& (if i \<le> n then P i else Q)) \<box> c \<^bold>& Q"
    by (meson Det_commute)
  also have "... = (\<box>i\<in>{0..n}. (b i) \<^bold>& (P i)) \<box> c \<^bold>& Q"
  proof -
    have "(\<box>i\<in>{0..n}. (if i \<le> n then b i else c) \<^bold>& (if i \<le> n then P i else Q)) = (\<box>i\<in>{0..n}. (b i) \<^bold>& (P i))"
      by (rule mono_GlobalDet_eq, simp)
    thus ?thesis by simp
  qed
  finally show ?thesis ..
qed



text\<open>for P that has no guard (i.e., guard = True)\<close>
lemma biextchoic_normalization_nguard:
  "(\<box> i\<in>{0..n::nat}. b(i) \<^bold>& P(i)) \<box> Q 
   = (\<box> i\<in>{0..n+1}. (if i \<le> n then b(i) else True) \<^bold>& (if i \<le> n then P(i) else Q))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<box> i\<in>{0..n::nat}. b(i) \<^bold>& P(i)) \<box> True \<^bold>& Q" by simp
  also have "... = ?rhs"
    using biextchoic_normalization by blast
  finally show ?thesis .
qed



lemma biextchoic_normalization_nguard_prefix[normalisation]:
  "(\<box> i\<in>{0..n::nat}. b(i) \<^bold>& P(i)) \<box> (a \<rightarrow> Q) 
   = (\<box> i\<in>{0..n+1}. (if i \<le> n then b(i) else True) \<^bold>& (if i \<le> n then P(i) else a \<rightarrow> Q))"
  (is "?lhs = ?rhs")
  using biextchoic_normalization_nguard by blast


lemma GlobalNdet_refine_no_step [normalisation]: "a \<in> A \<Longrightarrow> (GlobalNdet A P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P a"
  by (meson GlobalNdet_refine_FD UNIV_I no_step_refine trans_FD)

subsection\<open>interrupt\<close>
text\<open>For the pattern in Trans : SSTOP@term{\<triangle>}, we need a lemma to deal with ddlf \<close>

lemma interrupt_ref:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P" and "Q = a \<rightarrow> Q"
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D  Q \<triangle> P"
proof (unfold refine_defs, safe)
  show \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close> for t Y
  proof (induct t)
    from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D  P\<close> show \<open>([], Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> ([], Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
      apply (subst (asm) \<open>Q = a \<rightarrow> Q\<close>)
      apply (simp add: refine_defs write0_projs F_Interrupt GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def F_GlobalNdet F_iterate_Mndetprefix_UNIV subset_iff)
      by (metis is_processT6_TR is_processT8 self_append_conv2)
  next
    fix e t Y assume hyp : \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
    assume \<open>(e # t, Y) \<in> \<F> (Q \<triangle> P)\<close>
    hence \<open>(e # t, Y) \<in> \<F> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    then consider \<open>(e # t, Y) \<in> \<F> P\<close> | \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      by (auto simp add: Interrupt_write0 F_Det F_write0)
    thus \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
    proof cases
      assume \<open>(e # t, Y) \<in> \<F> P\<close>
      with \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
        by (simp add: refine_defs subset_iff)
    next
      assume \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      from this(2)[THEN hyp] have \<open>(t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close> .
      thus \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
        find_theorems iterate name: "is"
        apply (simp add: \<open>e = ev a\<close> GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def F_GlobalNdet F_iterate_Mndetprefix_UNIV iterate_Mndetprefix_SKIPS_is F_Ndet F_SKIPS split: if_split_asm)
       
        apply safe
        apply (simp_all add: lessThan_empty_iff)
        apply (metis Zero_not_Suc append_Cons append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons non_tickFree_imp_not_Nil
            tickFree_Cons_iff)
        apply (metis Zero_not_Suc append_Cons append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons tickFree_Cons_iff
            tickFree_Nil)
        apply (metis append_self_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Suc_conv list.size(3) n_not_Suc_n
            non_tickFree_imp_not_Nil tickFree_Cons_iff)
        apply (metis gt_ex less_nat_zero_code)
        apply (metis (no_types, opaque_lifting) append_eq_Cons_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Suc_conv
            nat.distinct(1) tickFree_Cons_iff)
        apply (metis less_Suc_eq not_less0)
              apply (metis Suc_neq_Zero is_ev_def lessThan_iff less_Suc_eq self_append_conv tickFree_Cons_iff)
        apply (metis Zero_not_Suc append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) lessI lessThan_iff tickFree_Cons_iff)
        apply (metis Zero_not_Suc lessI)
        apply (metis Zero_not_Suc append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons tickFree_Cons_iff)
        apply blast
        apply (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) lessThan_iff less_Suc_eq old.nat.distinct(2) self_append_conv
            tickFree_Cons_iff)
        apply (metis Zero_not_Suc append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) insertI1 lessThan_Suc tickFree_Cons_iff)
        .
    qed
  qed
next
  show \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close> for t
  proof (induct t)
    from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>[] \<in> \<D> (Q \<triangle> P) \<Longrightarrow> [] \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
      by (simp add: refine_defs subset_iff D_Interrupt GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def D_GlobalNdet D_iterate_Mndetprefix_UNIV)
        (metis Nil_notin_D_Mprefix assms(2) write0_def)
  next
    fix e t assume hyp : \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
    assume \<open>e # t \<in> \<D> (Q \<triangle> P)\<close>
    hence \<open>e # t \<in> \<D> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    hence \<open>e # t \<in> \<D> P \<or> t \<in> \<D> (Q \<triangle> P)\<close>
      by (auto simp add: D_Interrupt write0_projs)
    thus \<open>e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
    proof (elim disjE)
      from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark> \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>e # t \<in> \<D> P \<Longrightarrow> e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
        by (simp add: refine_defs subset_iff)
    next
      show \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<^sup>\<checkmark>)\<close>
        apply (frule hyp)
        apply (auto simp add: GlobalNdet\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterations'_def D_GlobalNdet D_iterate_Mndetprefix_UNIV iterate_Mndetprefix_SKIPS_is D_Ndet D_SKIPS split: if_split_asm)
        apply (metis (no_types, lifting) D_imp_front_tickFree Nil_is_append_conv \<open>e # t \<in> \<D> (Q \<triangle> P)\<close> append_Cons
            front_tickFree_Cons_iff length_0_conv list.distinct(1) tickFree_Cons_iff)
        by (metis BOT_iff_Nil_D D_imp_front_tickFree Zero_not_Suc \<open>e # t \<in> \<D> ((a \<rightarrow> Q) \<triangle> P)\<close> append_Cons append_Nil
            assms(2) front_tickFree_Cons_iff length_Cons tickFree_Cons_iff tickFree_Nil)+
    qed
  qed
qed


lemma "c\<^bold>?v \<rightarrow> ((g1 \<^bold>& P )\<box>(g2 \<^bold>& Q)) = (g1 \<^bold>&(c\<^bold>?v \<rightarrow>  P ))\<box> (g2 \<^bold>& (c\<^bold>?v \<rightarrow>  Q)) "
  oops

end