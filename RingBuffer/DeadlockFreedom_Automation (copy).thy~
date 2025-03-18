\<comment>\<open> ********************************************************************
 * This file is to automate the verification of deadlock freedom.
 * This version combines the lemmas in DeadlockFreenessStuff by Benoit and lemmas in Bounded_Buffer_211124_ddf_automation_incomplete by Simon.
 * 03 Feb 2025

*******************************************************************\<close>
theory DeadlockFreedom_Automation
  imports "HOL-CSP_OpSem.OpSem_Deadlock_Results" Guard
begin

(**)

lemma prefix_proving_Mndetprefix_ref :
  \<open>A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter>a \<in> A \<rightarrow> Q a)\<close>
  \<open>A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (\<box>a \<in> A \<rightarrow> Q a)\<close>
  \<open>a \<in> B \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> R\<close>
  apply (metis Mndetprefix_FD_subset mono_Mndetprefix_FD order_trans)
  apply (metis Mndetprefix_FD_Mprefix Mndetprefix_FD_subset mono_Mndetprefix_FD order.trans)
  by (meson Mndetprefix_FD_write0 dual_order.trans mono_write0_FD)

thm Mndetprefix_def

lemma read_proving_Mndetprefix_ref :
  \<open>inj_on c A \<Longrightarrow> c ` A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P (c a) \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>?a \<in> A \<rightarrow> Q a)\<close>
  and write_proving_Mndetprefix_ref : \<open>c a \<in> B \<Longrightarrow> P (c a) \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>!a \<rightarrow> R)\<close>
  by (unfold read_def, rule prefix_proving_Mndetprefix_ref(2), auto)[1]
     (metis prefix_proving_Mndetprefix_ref(3) write0_def write_def)
 

lemmas prefix_proving_Mndetprefix_UNIV_ref = prefix_proving_Mndetprefix_ref[where B = UNIV, simplified]
   and read_proving_Mndetprefix_UNIV_ref = read_proving_Mndetprefix_ref[where B = UNIV, simplified]
   and write_proving_Mndetprefix_UNIV_ref = write_proving_Mndetprefix_ref[where B = UNIV, simplified]


(*if P's nondetprefix process is refined by Q AND R, then it is also refined by Q \<sqinter> R, Q \<box> R, Q  R*)
lemma binops_proving_Mndetprefix_ref :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> (\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D Q \<sqinter> R\<close>
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> (\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> R\<close>
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> (\<sqinter>a \<in> A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D Q \<rhd> R\<close>
  apply (simp add: FD_iff_eq_Ndet Ndet_assoc)
  apply (simp add: FD_iff_eq_Ndet Ndet_distrib_Det_left)
  by (metis Sliding_id mono_Sliding_FD)


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
lemma F_iterate_Mndetprefix :
  \<open>\<F> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) =
   (if A = {} then if i = 0 then \<F> P else {(s, X). s = []} else
   {(s, X). set s \<subseteq> ev ` A \<and> length s < i \<and> (\<exists>a \<in> A. ev a \<notin> X)} \<union>
   {(s @ t, X)| s t X. set s \<subseteq> ev ` A \<and> length s = i \<and> (t, X) \<in> \<F> P})\<close>
  (is \<open>?lhs P i = (if A = {} then if i = 0 then \<F> P else {(s, X). s = []} else
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
          by (simp add: F_Mndetprefix write0_def F_Mprefix \<open>A \<noteq> {}\<close>) (metis list.collapse)
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
      fix s t assume \<open>set s \<subseteq> ev ` A\<close> \<open>t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close> \<open>i = length s\<close>
      from \<open>t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close>
      obtain a t' where \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>t' \<in> \<D> P\<close>
        by (simp add: D_Mndetprefix write0_def D_Mprefix \<open>A \<noteq> {}\<close>)
           (metis list.collapse)
      from this(1, 2) have \<open>s @ t = (s @ [ev a]) @ t'\<close> \<open>set (s @ [ev a]) \<subseteq> ev ` A\<close>
                           \<open>length (s @ [ev a]) = Suc (length s)\<close>
        by (simp_all add: \<open>set s \<subseteq> ev ` A\<close>)
      with \<open>t' \<in> \<D> P\<close> show \<open>\<exists>s' t'. s @ t = s' @ t' \<and> set s' \<subseteq> ev ` A \<and>
                                     length s' = Suc (length s) \<and> t' \<in> \<D> P\<close> by blast
    next
      fix s t 
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

(*when A = UNIV, the failure set of a process P that iterates i times over Mndetprefix on A*)
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


(* TODO : find a better name *)

text \<open> York: I've change the notation for the GlobalNdet_iteration operator to use a "+" instead of a "*". This is because   the requirement is that the process can do some number of steps n > 0 before becoming P. This kind of "at least 1"   behaviour is normally given by a "+" rather than "*". 24Jan25\<close>

definition GlobalNdet_iterations :: \<open>'a process \<Rightarrow> 'a process\<close> (\<open>(_\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<close> [1000] 999)
  where \<open>GlobalNdet_iterations P \<equiv> \<sqinter>i \<in> {0<..}. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P\<close>
(*this extends iterate i indefinitely, allowing P to be prefixed by an arbitrary but finite number (>0) of Mndetprefix, with the number of iterations being Ndet*)


text \<open>York:  This new operator, which uses the * syntax, says that we can perform 0 events and then behave as P. These two operators  ought to be linked together with some lemmas. 24Jan25\<close>

definition GlobalNdet_iterations' :: \<open>'a process \<Rightarrow> 'a process\<close> (\<open>(_\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> [1000] 999)
  where \<open>GlobalNdet_iterations' P \<equiv> \<sqinter>i \<in> UNIV. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P\<close>
  (* UNIV = {0..} *)

text \<open>York:  The below is a lemma  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F \<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c* we think should be true, but we can't prove it as yet 4Jan25 \<close>

text\<open>Benoit 30Jan\<close>
lemma GlobalNdet_iterations'_is_Ndet_GlobalNdet_iterations : \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = P \<sqinter> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close>
proof -
  have \<open>UNIV = insert (0 :: nat) {0<..}\<close> by fast
  have \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = \<sqinter> i\<in>UNIV. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P\<close>
    by (simp add: GlobalNdet_iterations'_def)
  also have \<open>\<dots> = iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P \<sqinter>
                  (\<sqinter> i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P)\<close>
    apply (subst \<open>UNIV = insert (0 :: nat) {0<..}\<close>)
    apply (subst GlobalNdet_distrib_unit)
    by simp_all
  also have \<open>iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P = P\<close> by simp
  also have \<open>(\<sqinter> i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P) = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close>
    by (simp add: GlobalNdet_iterations_def)
  finally show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = P \<sqinter> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close> .
qed

text\<open>Benoit 30Jan\<close>
lemma GlobalNdet_iterations'_Mndetprefix :  \<open>(\<sqinter>a\<in>UNIV \<rightarrow>  P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close>
proof -
  have \<open>(\<sqinter>a\<in>UNIV \<rightarrow>  P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = (\<sqinter> i\<in>UNIV. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>(\<sqinter>a\<in>UNIV \<rightarrow>  P))\<close>
    by (simp add: GlobalNdet_iterations'_def)
  also have \<open>\<dots> = \<sqinter> i\<in>UNIV. iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P\<close>
    by (rule mono_GlobalNdet_eq) (simp del: iterate_Suc add: iterate_Suc2)
  also have \<open>\<dots> = \<sqinter> i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P\<close>
    by (simp add: inj_on_mapping_over_GlobalNdet[of Suc UNIV, simplified]
                  greaterThan_0 mono_GlobalNdet_eq)
  also have \<open>\<dots> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close> by (simp add: GlobalNdet_iterations_def)
  finally show \<open>(\<sqinter>a\<in>UNIV \<rightarrow>  P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close> .
qed

text\<open>Benoit 30Jan, the original lemma is  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F \<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c*\<close>
lemma GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations' : \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ = \<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<close>
proof (subst Process_eq_spec, safe)
  show \<open>t \<in> \<D> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+) \<Longrightarrow> t \<in> \<D> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t
    apply (simp add: D_Mndetprefix write0_def D_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (cases t, simp_all add:  D_GlobalNdet D_iterate_Mndetprefix_UNIV)
    by (metis event.exhaust greaterThan_iff hd_append2 length_greater_0_conv
              list.sel(1, 3) list.set_sel(1) tickFree_def tickFree_tl tl_append_if)
next
  show \<open>t \<in> \<D> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*) \<Longrightarrow> t \<in> \<D> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<close> for t
    apply (simp add: D_Mndetprefix write0_def D_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (cases t, simp_all add:  D_GlobalNdet D_iterate_Mndetprefix_UNIV)
    by (metis append_Cons event.simps(3) greaterThan_iff length_greater_0_conv list.simps(3) tickFree_Cons_iff)
next
  show \<open>(t, X) \<in> \<F> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+) \<Longrightarrow> (t, X) \<in> \<F> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t X
    apply (simp add: F_Mndetprefix write0_def F_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (simp add: F_GlobalNdet F_iterate_Mndetprefix_UNIV)
    apply (cases t, simp_all)
    by (metis bot_nat_0.not_eq_extremum event.exhaust greaterThan_iff hd_append2 less_iff_Suc_add
              list.sel(1, 3) list.set_sel(1) list.size(3) tickFree_def tickFree_tl tl_append_if)
next
  show \<open>(t, X) \<in> \<F> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*) \<Longrightarrow> (t, X) \<in> \<F> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<close> for t X
    apply (simp add: F_Mndetprefix write0_def F_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (simp add: F_GlobalNdet F_iterate_Mndetprefix_UNIV)
    apply (cases t, simp_all add: gt_ex)
    by (metis append_Cons event.simps(3) greaterThan_0 length_Cons lessI range_eqI tickFree_Cons_iff)
qed




text \<open> York: This would allow us to prove the following lemma:24Jan25 \<close>

text\<open>Benoit 30Jan, changed from \<open>\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c*  \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> to  \<longleftrightarrow>\<close>

lemma one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD :
  \<open>\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*  \<sqsubseteq>\<^sub>F\<^sub>D Q \<longleftrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (simp add: GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations')

text \<open>York: This law would allow us to break down the proof into an initial event step, followed by an arbitrary number  of steps. Then we could try and prove laws like the one below.
This means that if Q can do some number of events and then behave as P, then Q prefixed by a   can also do some number of steps and then behave as P. It seems to be intuitively true, but we  can't prove it. It would however avoid needing to pick the number of steps to make before
  recursing, which would facilitate fully automated proof.24Jan25
proved by Benoit 30Jan\<close>

lemma eat_lemma: \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close> if \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
proof (rule trans_FD)
  show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> Q\<close>
    apply (subst GlobalNdet_iterations'_is_Ndet_GlobalNdet_iterations)
    apply (rule mono_Ndet_FD_right)
    apply (subst GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations')
    by (intro mono_Mndetprefix_FD ballI \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>)
next
  show \<open>(\<sqinter>a\<in>UNIV \<rightarrow> Q) \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close>
    by (simp add: prefix_proving_Mndetprefix_UNIV_ref(3))
qed




lemma iterate_F_imp_GlobalNdet_iterations_F :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F Q\<close>
  by (unfold GlobalNdet_iterations_def)
     (meson GlobalNdet_refine_F greaterThan_iff trans_F)

lemma iterate_T_imp_GlobalNdet_iterations_T :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>T Q\<close>
  by (unfold GlobalNdet_iterations_def)
     (meson GlobalNdet_refine_F greaterThan_iff leF_imp_leT trans_T)

lemma iterate_D_imp_GlobalNdet_iterations_D :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>D Q\<close>
  by (unfold GlobalNdet_iterations_def)
     (meson GlobalNdet_refine_FD greaterThan_iff leFD_imp_leD trans_D)

lemma iterate_FD_imp_GlobalNdet_iterations_FD :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (metis iterate_D_imp_GlobalNdet_iterations_D
            iterate_F_imp_GlobalNdet_iterations_F
              leFD_imp_leD leFD_imp_leF leF_leD_imp_leFD)

lemma iterate_DT_imp_GlobalNdet_iterations_DT :
  \<open>0 < i \<Longrightarrow> iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (metis iterate_D_imp_GlobalNdet_iterations_D
            iterate_T_imp_GlobalNdet_iterations_T
            leDT_imp_leD leDT_imp_leT leD_leT_imp_leDT)



lemma GlobalNdet_iterations_F_imp_deadlock_free : \<open>deadlock_free P\<close> if \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F P\<close>
proof -
  have \<open>\<F> P \<subseteq> \<F> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<close> by (meson failure_refine_def \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F P\<close>)
  also have \<open>\<dots> = (\<Union>i\<in>{0<..}. {(s, X). tickFree s \<and> length s < i \<and> (\<exists>a. ev a \<notin> X)} \<union>
                               {(s @ t, X)| s t X. tickFree s \<and> length s = i \<and> (t, X) \<in> \<F> P})\<close>
    by (simp add: GlobalNdet_iterations_def F_GlobalNdet F_iterate_Mndetprefix_UNIV)
  moreover have \<open>\<dots> = (\<Union>i. {(s, X). tickFree s \<and> length s < Suc i \<and> (\<exists>a. ev a \<notin> X)} \<union>
                       {(s @ t, X)| s t X. tickFree s \<and> length s = Suc i \<and> (t, X) \<in> \<F> P})\<close>
    find_theorems \<open>(\<Union>i \<in> ?S. ?f i) = (\<Union>i \<in> ?S'. ?f' i)\<close>
    (* TODO : find a better proof *)
    by safe (auto, metis length_greater_0_conv less_imp_Suc_add)
  moreover have \<open>(s, range ev) \<in> \<dots> \<Longrightarrow> False\<close> for s
  proof (induct s)
    case Nil
    then show ?case by simp
  next
    case (Cons e s)
    from Cons.prems obtain t u i
      where * : \<open>e # s = t @ u\<close> \<open>tickFree t\<close>
                \<open>length t = Suc i\<close> \<open>(u, range ev) \<in> \<F> P\<close> by blast
    from "*"(1, 2, 3) obtain a t'
      where ** : \<open>e = ev a\<close> \<open>t = ev a # t'\<close> \<open>s = t' @ u\<close> \<open>tickFree t'\<close> \<open>length t' = i\<close>
      by (cases t; simp add: tickFree_def) (use event.exhaust in blast)
    hence \<open>(s, range ev) \<in> (\<Union>i. {a. case a of (s, X) \<Rightarrow> tickFree s \<and> length s < Suc i \<and> (\<exists>a. ev a \<notin> X)} \<union>
            {(s @ t, X) |s t X. tickFree s \<and> length s = Suc i \<and> (t, X) \<in> \<F> P})\<close>
      (* TODO: write a better proof *)
      by simp (metis (no_types, lifting) "*"(4) Cons.hyps Suc_pred calculation length_greater_0_conv self_append_conv2 subset_eq)
    thus False using Cons.hyps by linarith
  qed
  ultimately show \<open>deadlock_free P\<close>
    unfolding AfterExt.deadlock_free_is_right(2)
    by (metis (no_types, lifting) append_single_T_imp_tickFree is_processT5_S7 subsetD)
qed

lemma 

GlobalNdet_iterations_FD_imp_deadlock_free :
  \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> deadlock_free P\<close>
  by (simp add: GlobalNdet_iterations_F_imp_deadlock_free leFD_imp_leF)


text\<open>Benoit 30Jan\<close>
(* this is already proven in the branch of parameterized termination *)
lemma GlobalNdet_Seq : \<open>(\<sqinter> a\<in>A. P a) \<^bold>; Q = \<sqinter> a\<in>A. (P a \<^bold>; Q)\<close>
  apply (cases \<open>A = {}\<close>, simp add: STOP_Seq)
  apply (simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet T_GlobalNdet F_Seq D_Seq)
  by safe blast+

lemma Mndetprefix_Seq : \<open>(\<sqinter>a\<in>A \<rightarrow> P a) \<^bold>; Q = \<sqinter>a\<in>A \<rightarrow> (P a \<^bold>; Q)\<close>
  apply (simp add: Mndetprefix_GlobalNdet GlobalNdet_Seq)
  apply (rule mono_GlobalNdet_eq)
  by (simp add: write0_def Mprefix_Seq)

text \<open> York: This would be a useful lemma to have, because it would allow us to have an operator that simply does n event steps. 24Jan25
 proved by Benoit 30Jan\<close>
lemma iterate_is_iterate_SKIP_Seq :
  \<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P = iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>SKIP \<^bold>; P\<close>
proof (induct i)
  show \<open>iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P = iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>SKIP \<^bold>; P\<close>
    by (simp add: SKIP_Seq)
next
  fix i assume hyp : \<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P = iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>SKIP \<^bold>; P\<close>
  show \<open>iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P = iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>SKIP \<^bold>; P\<close>
    by (auto simp add: Mndetprefix_Seq intro: mono_Mndetprefix_eq hyp)
qed


text\<open>Benoit 30Jan\<close>
lemma GlobalNdet_iterations'_GlobalNdet_iterations' : \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<close>
  apply (simp add: Process_eq_spec GlobalNdet_iterations'_def
                   F_GlobalNdet D_GlobalNdet
                   F_iterate_Mndetprefix_UNIV D_iterate_Mndetprefix_UNIV)
  apply safe
        apply simp_all
        apply blast
       apply blast
      apply (metis append.assoc tickFree_append_iff)
     apply blast
    apply (metis eq_Nil_appendI non_tickFree_implies_nonMt)
   apply (metis append.assoc tickFree_append_iff)
  using tickFree_Nil by blast

text\<open>Benoit 30Jan, the original is lemma \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close>\<close>
lemma GlobalNdet_iterations_GlobalNdet_iterations : \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ = \<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close>
  by (simp add: GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations'
                GlobalNdet_iterations'_Mndetprefix
                GlobalNdet_iterations'_GlobalNdet_iterations')






lemma \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D P\<close> if \<open>P = (a \<rightarrow> P) \<box> (b \<rightarrow> P)\<close>
  apply (rule trans_FD[OF _ iterate_FD_imp_GlobalNdet_iterations_FD[of \<open>Suc 0\<close> \<open>P\<close>]])
    apply simp_all
  apply (subst (2) \<open>P = (a \<rightarrow> P) \<box> (b \<rightarrow> P)\<close>)
  apply (subst Det_id[symmetric])
  apply (rule mono_Det_FD)
  by (simp add: prefix_proving_Mndetprefix_ref(3))+
  

thm mono_Det_FD

lemma \<open> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> P\<close>
  apply (unfold write0_def)
  apply (rule trans_FD[OF _ iterate_FD_imp_GlobalNdet_iterations_FD[of \<open>Suc 0\<close> \<open>P\<close>]])
  by (simp_all add: prefix_proving_Mndetprefix_UNIV_ref(2))
      
lemma \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D P\<close> if \<open>P = (a \<rightarrow> b \<rightarrow> P)\<close>
  apply (rule trans_FD[OF _ iterate_FD_imp_GlobalNdet_iterations_FD[of \<open>Suc (Suc 0)\<close> \<open>P\<close>]])
    apply simp_all
  by (metis idem_FD prefix_proving_Mndetprefix_UNIV_ref(3) that)

thm prefix_proving_Mndetprefix_UNIV_ref(3)




text\<open>York 31Jan25:\<close>

lemma no_step_refine: "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P"
  by (simp add: GlobalNdet_iterations'_is_Ndet_GlobalNdet_iterations)

(*
thm binops_proving_Mndetprefi*
lemma 
  assumes "\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q" "\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D R"
  shows "\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> R"
  by (smt (verit) assms(1) assms(2) binops_proving_Mndetprefix_ref(2))*)

lemma df_step_intro:
  assumes P_def: "P = Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q"
  shows "deadlock_free P"
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (subst P_def) back
  apply (simp add: assms(2))
  done

lemma ndet_prefix_ext_choice:(*this is added for P = d\<rightarrow>( (a \<rightarrow> b \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P)) pattern: prefix of external choice*)
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D R"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> R"
  by (metis CSP.mono_Det_FD Det_id assms(1) assms(2))


lemma guard_choice:(*this is added for P =  (a & \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P) pattern: prefix of external choice*)
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D a \<^bold>&  Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D b \<^bold>&  R"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D a  \<^bold>& Q \<box> b  \<^bold>&  R"
  by (metis CSP.mono_Det_FD Det_id assms(1) assms(2))


text\<open>The mothod\<close>
method deadlock_free uses P_def =
  (rule df_step_intro[OF P_def],
   simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym],
   simp add: prefix_proving_Mndetprefix_UNIV_ref(3) eat_lemma no_step_refine binops_proving_Mndetprefix_ref ndet_prefix_ext_choice)


text\<open>examples\<close>
lemma
  assumes P_def: \<open>P = (a \<rightarrow> b \<rightarrow> c \<rightarrow> d \<rightarrow> P)\<close>
  shows \<open>deadlock_free P\<close>
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  apply (subst P_def) back
  apply (simp add: eat_lemma no_step_refine prefix_proving_Mndetprefix_UNIV_ref(3))
  done

lemma 
  assumes P_def: \<open>P = (a \<rightarrow> b \<rightarrow> c \<rightarrow> d \<rightarrow> P)\<close>
  shows \<open>deadlock_free P\<close>
  by (deadlock_free P_def: P_def)



lemma 
  assumes P_def: \<open>P = (a \<rightarrow> b \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P)\<close>
  shows \<open>deadlock_free P\<close>
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  apply (subst P_def) back
  apply (simp add: binops_proving_Mndetprefix_ref(2) eat_lemma no_step_refine prefix_proving_Mndetprefix_UNIV_ref(3))
  done

lemma 
  assumes P_def': \<open>P = (a \<rightarrow> b \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P)\<close>
  shows \<open>deadlock_free P\<close>
  by (deadlock_free P_def: P_def')




lemma 
  assumes P_def: \<open>P = d\<rightarrow>( (a \<rightarrow> b \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P))\<close>
  shows \<open>deadlock_free P\<close>  
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  apply (subst P_def) back

  apply (simp add: eat_lemma ndet_prefix_ext_choice  no_step_refine prefix_proving_Mndetprefix_UNIV_ref(3))
  done

lemma 
  assumes P_def: \<open>P = d\<rightarrow>( (a \<rightarrow> b \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P))\<close>
  shows \<open>deadlock_free P\<close>
  by (deadlock_free P_def: P_def)





text\<open>lemmas from 'Bounded_Buffer_211124_ddf_automation_incomplete' by Simon\<close>

lemma Mndetprefix_trans_subset_FD : 
  \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> Q a \<sqsubseteq>\<^sub>F\<^sub>D P a) \<Longrightarrow>
   Mndetprefix B Q \<sqsubseteq>\<^sub>F\<^sub>D Mndetprefix A P\<close>
  by (metis CSP.mono_Mndetprefix_FD mono_Mndetprefix_FD_set trans_FD)

lemma Ndet_trans_Det_FD :\<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> R \<sqsubseteq>\<^sub>F\<^sub>D S \<Longrightarrow> P \<sqinter> R \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> S\<close>
  by (meson CSP.mono_Ndet_FD mono_Ndet_Det_FD trans_FD)

find_theorems "(\<box>)" "(\<sqsubseteq>\<^sub>F\<^sub>D)"


lemma DF_guard_extchoice:
  assumes "b \<Longrightarrow> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D Q" "c \<Longrightarrow> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D R" "b \<or> c"
  shows "DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D (b \<^bold>& Q) \<box> (c \<^bold>& R)"
  by (metis Det_STOP Det_commute Guard_False Guard_True assms(1) assms(2) assms(3) deadlock_free_Det deadlock_free_def)

lemma refine_guarded_extchoice:
  assumes "b \<or> c" "b \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D Q" "c \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D R"
  shows "\<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D (b \<^bold>& Q) \<box> (c \<^bold>& R)"
  by (metis Det_STOP Det_commute FD_iff_eq_Ndet Guard_def Ndet_trans_Det_FD assms(1) assms(2) assms(3) idem_FD)

lemma extchoice_preguard: "(b \<or> c) \<^bold>& (b \<^bold>& Q) \<box> (c \<^bold>& R) = (b \<^bold>& Q) \<box> (c \<^bold>& R)"
  by (simp add: Guard_def)

lemma MultiDet_preguard: "finite I \<Longrightarrow> (Sup (b ` I) \<^bold>& (\<^bold>\<box> i\<in>I. b i \<^bold>& P i)) = (\<^bold>\<box> i\<in>I. b i \<^bold>& P i)"
  apply (induct arbitrary: b P rule: finite_induct)
  apply (auto simp add: Guard_def Det_is_STOP_iff MultiDet_is_STOP_iff)
  apply (metis Det_id)
  done

lemma generilized_refine_guarded_extchoice:
  assumes "finite I" "\<exists>i\<in>I. b(i)" "\<And> i. \<lbrakk> i \<in> I; b(i) \<rbrakk> \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D P(i)" 
  shows "\<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D (\<^bold>\<box> i\<in>I. b(i) \<^bold>& P(i))"
using assms proof (induct arbitrary:X rule:finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert x F)
  then show ?case
  proof -
    from insert have 1:"(\<^bold>\<box> i\<in>{x} \<union> F. b i \<^bold>& P i) = (b x \<^bold>& P x) \<box> (Sup (b ` F) \<^bold>& (\<^bold>\<box> i\<in>F. b i \<^bold>& P i))"
      by (smt (verit, ccfv_threshold) Guard_def MultiDet_insert' MultiDet_is_STOP_iff Sup_bool_def True_in_image_Bex insert_is_Un)
    have 2:"\<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D (b x \<^bold>& P x) \<box> (Sup (b ` F) \<^bold>& (\<^bold>\<box> i\<in>F. b i \<^bold>& P i))"
      apply (rule refine_guarded_extchoice, auto simp add: Sup_bool_def insert)
      using Sup_bool_def insert.prems(1) apply blast
      done
    thus ?thesis
      using "1" by fastforce
  qed
qed


text\<open>Examples\<close>
lemma (*is this deadlock free?*)
  assumes P_def: \<open>P = ((x < 0) \<^bold>& (a \<rightarrow> P)) \<box>(( x \<ge> 0) \<^bold>& (b \<rightarrow> P))\<close>
  shows \<open>deadlock_free P\<close>
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  apply (subst P_def) back

  oops

lemma 
  assumes P_def: \<open>P = e\<rightarrow>(((x < 0) \<^bold>& (a \<rightarrow> P)) \<box>(( x \<ge> 0) \<^bold>& (b \<rightarrow> P)))\<close>
  shows \<open>deadlock_free P\<close>

  oops



lemma 
  assumes P_def: \<open>P =( b \<^bold>& P \<box> c \<^bold>& Q)\<close>
  shows \<open>deadlock_free P\<close> 
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym])
  apply (subst P_def) back
  oops




lemma 
  assumes P_def: \<open>P = \<^bold>\<box> i\<in>{0,1,2}. if i = 0 then b \<^bold>& P else if i = 1 then c \<^bold>& Q else d \<^bold>& R\<close>
  shows \<open>deadlock_free P\<close>
  oops



lemma 
  assumes P_def: \<open>P = ((x < 0) \<^bold>& a \<rightarrow> P) \<box>(( x \<ge> 0) \<^bold>& b \<rightarrow> P)\<close>
  shows \<open>deadlock_free P\<close>
  by (deadlock_free P_def: P_def)

term "b \<^bold>& P \<box> c \<^bold>& Q"

term "\<^bold>\<box> i\<in>{0,1}. if i = 0 then b \<^bold>& P else c \<^bold>& Q"

lemma "\<^bold>\<box> i\<in>{0,1}. if i = 0 then P else Q = P \<box> Q"
  apply simp
  oops


term "\<^bold>\<box> i\<in>I. b(i) \<^bold>& P(i)"


end