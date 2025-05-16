\<comment>\<open> **********************************************************************************
 * This file contains theories for automating the verification of deadlock freedom.
 * This version combines the lemmas in Deadlock_Freeness_Stuff by Benoit and new lemmas developed for ddlf proof.
 * 06 May 2025
************************************************************************************\<close>

theory DeadlockFreedom
  imports "HOL-CSP_OpSem.OpSem_Deadlock_Results" "Guard"
begin

(*
default_sort type
no_notation floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)
*)

section\<open>syntax definition added\<close>
no_notation Cons  ("_ \<cdot>/ _" [66,65] 65)

abbreviation "dot"    :: "['a \<Rightarrow> 'b, 'a, 'b process] \<Rightarrow> 'b process"
  where      "dot c a P \<equiv> write c a P"

syntax   "_dot"  :: "[id, logic, 'a process] => 'a process"
                                        ("(3(_\<^bold>._) /\<rightarrow> _)" [0,0,78] 78)

translations
 
  "_dot c p P"     \<rightleftharpoons> "CONST dot c p P"


section\<open>lemmas copied from Deadlock_Freeness_Stuff, notes and some lemma names are added in this version\<close>
lemma prefix_proving_Mndetprefix_ref :
  \<open>A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter>a \<in> A \<rightarrow> Q a)\<close>
  \<open>A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (\<box>a \<in> A \<rightarrow> Q a)\<close>
  \<open>a \<in> B \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> R\<close>
  apply (metis Mndetprefix_FD_subset mono_Mndetprefix_FD order_trans)
  apply (metis Mndetprefix_FD_Mprefix Mndetprefix_FD_subset mono_Mndetprefix_FD order.trans)
  by (meson Mndetprefix_FD_write0 dual_order.trans mono_write0_FD)


lemma read_proving_Mndetprefix_ref :
  \<open>inj_on c A \<Longrightarrow> c ` A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P (c a) \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>?a \<in> A \<rightarrow> Q a)\<close>
  and write_proving_Mndetprefix_ref : \<open>c a \<in> B \<Longrightarrow> P (c a) \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> (\<sqinter>a \<in> B \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>!a \<rightarrow> R)\<close>
  by (unfold read_def, rule prefix_proving_Mndetprefix_ref(2), auto)[1]
     (metis prefix_proving_Mndetprefix_ref(3) write0_def write_def)
 

lemmas prefix_proving_Mndetprefix_UNIV_ref = prefix_proving_Mndetprefix_ref[where B = UNIV, simplified]
   and read_proving_Mndetprefix_UNIV_ref = read_proving_Mndetprefix_ref[where B = UNIV, simplified]
   and write_proving_Mndetprefix_UNIV_ref = write_proving_Mndetprefix_ref[where B = UNIV, simplified]


text\<open>if P's nondetprefix process is refined by Q AND R, then it is also refined by Q \<sqinter> R, Q \<box> R, Q  R\<close>
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


text\<open>this extends iterate i indefinitely, allowing P to be prefixed by an arbitrary but finite number (>0) of Mndetprefix, with the number of iterations being Ndet\<close>
definition GlobalNdet_iterations :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<close> [1000] 999)
  where \<open>GlobalNdet_iterations P \<equiv> \<sqinter>i \<in> {0<..}. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P\<close>


text \<open>This new operator, which uses the * syntax, says that we can perform 0 or more events and then behave as P. These two operators  ought to be linked together with some lemmas. 24Jan25\<close>
definition GlobalNdet_iterations' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> [1000] 999)
  where \<open>GlobalNdet_iterations' P \<equiv> \<sqinter>i \<in> UNIV. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P\<close>
  (* UNIV = {0..} *)


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


lemma GlobalNdet_iterations'_Mndetprefix : \<open>(\<sqinter>a\<in>UNIV \<rightarrow>  P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close>
proof -
  have \<open>(\<sqinter>a\<in>UNIV \<rightarrow>  P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = (\<sqinter> i\<in>UNIV. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>(\<sqinter>a\<in>UNIV \<rightarrow>  P))\<close>
    by (simp add: GlobalNdet_iterations'_def)
  also have \<open>\<dots> = \<sqinter> i\<in>UNIV. iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P\<close>
    by (rule mono_GlobalNdet_eq) (simp del: iterate_Suc add: iterate_Suc2)
  also have \<open>\<dots> = \<sqinter> i\<in>{0<..}. iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P\<close>
    by (auto simp add: inj_on_mapping_over_GlobalNdet[of Suc UNIV, simplified]
        greaterThan_0 intro: mono_GlobalNdet_eq)
  also have \<open>\<dots> = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close> by (simp add: GlobalNdet_iterations_def)
  finally show \<open>(\<sqinter>a\<in>UNIV \<rightarrow>  P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* = P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close> .
qed



lemma GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations' :\<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ = \<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<close>
proof (subst Process_eq_spec, safe)
  show \<open>t \<in> \<D> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+) \<Longrightarrow> t \<in> \<D> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t
    apply (simp add: D_Mndetprefix write0_def D_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (cases t, simp_all add:  D_GlobalNdet D_iterate_Mndetprefix_UNIV greaterThan_0)
    by (metis (no_types, lifting) append_eq_Cons_conv is_ev_def length_greater_0_conv
              tickFree_Cons_iff zero_less_Suc)
next
  show \<open>t \<in> \<D> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*) \<Longrightarrow> t \<in> \<D> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<close> for t
    apply (simp add: D_Mndetprefix write0_def D_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (cases t, simp_all add: D_GlobalNdet D_iterate_Mndetprefix_UNIV greaterThan_0)
    by (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons tickFree_Cons_iff)
next
  show \<open>(t, X) \<in> \<F> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+) \<Longrightarrow> (t, X) \<in> \<F> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t X
    apply (simp add: F_Mndetprefix write0_def F_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (simp add: F_GlobalNdet F_iterate_Mndetprefix_UNIV)
    apply (cases t, simp_all add: greaterThan_0 append_eq_Cons_conv is_ev_def)
    by (smt (verit, best) append_eq_Cons_conv is_ev_def length_greater_0_conv
            tickFree_Cons_iff zero_less_Suc)
next
  show \<open>(t, X) \<in> \<F> (\<sqinter>a\<in>UNIV \<rightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*) \<Longrightarrow> (t, X) \<in> \<F> (P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<close> for t X
    apply (simp add: F_Mndetprefix write0_def F_Mprefix)
    apply (simp add: GlobalNdet_iterations_def GlobalNdet_iterations'_def)
    apply (simp add: F_GlobalNdet F_iterate_Mndetprefix_UNIV)
    apply (cases t, simp_all add: gt_ex greaterThan_0)
    by (meson Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Suc_conv tickFree_Cons_iff)
qed


text\<open>Benoit 30Jan, changed from \<open>\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c*  \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> to  \<longleftrightarrow>\<close>

lemma one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD :
  \<open>\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*  \<sqsubseteq>\<^sub>F\<^sub>D Q \<longleftrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (simp add: GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations')


text \<open>This law would allow us to break down the proof into an initial event step, followed by an arbitrary number  of steps. Then we could try and prove laws like the one below.
This means that if Q can do some number of events and then behave as P, then Q prefixed by a   can also do some number of steps and then behave as P. It seems to be intuitively true, but we  can't prove it. It would however avoid needing to pick the number of steps to make before recursing, which would facilitate fully automated proof.\<close>
lemma eat_lemma: \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close> if \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
proof (rule trans_FD)
  show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> Q\<close>
    apply (subst GlobalNdet_iterations'_is_Ndet_GlobalNdet_iterations)
    by (metis FD_iff_eq_Ndet GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations' Ndet_assoc mono_Mndetprefix_FD that)
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
      by (cases t; simp add: tickFree_def) (metis "*"(2) is_ev_def tickFree_Cons_iff)
    hence \<open>(s, range ev) \<in> (\<Union>i. {a. case a of (s, X) \<Rightarrow> tickFree s \<and> length s < Suc i \<and> (\<exists>a. ev a \<notin> X)} \<union>
            {(s @ t, X) |s t X. tickFree s \<and> length s = Suc i \<and> (t, X) \<in> \<F> P})\<close>
      (* TODO: write a better proof *)
      by simp (metis (no_types, lifting) "*"(4) Cons.hyps Suc_pred calculation length_greater_0_conv self_append_conv2 subset_eq)
    thus False using Cons.hyps by linarith
  qed
  ultimately show \<open>deadlock_free P\<close>
    unfolding AfterExt.deadlock_free_is_right(2)
    by (metis (no_types, lifting) front_tickFree_nonempty_append_imp gr0_conv_Suc is_processT2_TR
        is_processT5_S7 length_0_conv length_Suc_conv less_irrefl subset_iff)
qed


lemma GlobalNdet_iterations_FD_imp_deadlock_free :
  \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+  \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> deadlock_free P\<close>
  by (simp add: GlobalNdet_iterations_F_imp_deadlock_free leFD_imp_leF)

lemma GlobalNdet_iterations_F_imp_deadlock_free_skip : 
  \<open>(P\<sqinter> SKIP() )\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+  \<sqsubseteq>\<^sub>F P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
sorry



lemma GlobalNdet_iterations_FD_imp_deadlock_free_skip :
  \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqinter> SKIP() \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  sorry

text \<open>This would be a useful lemma to have, because it would allow us to have an operator that simply does n event steps.  SKIP updated to Skip 25Feb\<close>
lemma iterate_is_iterate_SKIP_Seq :  \<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P = iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>Skip \<^bold>; P\<close>
proof (induct i)
  show \<open>iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P =
        iterate 0\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>Skip \<^bold>; P\<close> by simp
next
  fix i assume hyp : \<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P = iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>Skip \<^bold>; P\<close>
  show \<open>iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P =
        iterate (Suc i)\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>Skip \<^bold>; P\<close>
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
     apply (metis append_self_conv2 non_tickFree_imp_not_Nil)
   apply (metis append.assoc tickFree_append_iff)
  using tickFree_Nil by blast



lemma GlobalNdet_iterations_GlobalNdet_iterations : \<open>(P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ = \<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+\<close>
  by (simp add: GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations'
                GlobalNdet_iterations'_Mndetprefix
                GlobalNdet_iterations'_GlobalNdet_iterations')



section\<open>NEW lemmas to be added into HOL-CSP library\<close>
subsection\<open>natural deduction\<close>
lemma eat_read_lemma: 
  assumes "inj c" "\<And> v. P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q v"
  shows \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?v \<rightarrow> Q v\<close>
proof (rule trans_FD)
  show \<open>P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<close>
    by (simp add: Mndetprefix_GlobalNdet eat_lemma mono_GlobalNdet_FD_const)
next
  show "\<sqinter>a\<in>UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>?v \<rightarrow> Q v)"
    apply (rule read_proving_Mndetprefix_UNIV_ref)
      apply (simp_all add: assms)
    done
qed

lemma read_prefix_proving_Mndetprefix_ref :
  assumes "inj c"  "\<And> v. a \<in> UNIV \<Longrightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q v "
  shows  \<open> (\<sqinter>a \<in> UNIV \<rightarrow> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*) \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?v \<rightarrow> Q v\<close>
  by (simp add: assms(1,2) read_proving_Mndetprefix_UNIV_ref)

lemma proc_plus_prefix_ref: \<open> P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> P\<close>
  apply (unfold write0_def)
  apply (rule trans_FD[OF _ iterate_FD_imp_GlobalNdet_iterations_FD[of \<open>Suc 0\<close> \<open>P\<close>]])
  by (simp_all add: prefix_proving_Mndetprefix_UNIV_ref(2))

lemma proc_plus_read_prefix_ref: 
  assumes "inj c"  "\<And> v. P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q v "
  shows  \<open>  P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?v \<rightarrow> Q v\<close>
  by (metis (mono_tags, lifting) GlobalNdet_iterations_is_one_step_ahead_GlobalNdet_iterations' Mndetprefix_GlobalNdet assms(1,2)
      dual_order.refl eat_lemma eat_read_lemma empty_not_UNIV mono_GlobalNdet_FD_const trans_FD)


lemma no_step_refine: "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P"
  by (simp add: GlobalNdet_iterations'_is_Ndet_GlobalNdet_iterations Ndet_FD_self_left)



text\<open>df_step_intro is not applicable to index/parametrized process\<close>
lemma df_step_intro:
  assumes P_def: "P = Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q"
  shows "deadlock_free P"
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (subst P_def)  back (* also works: apply (subst (2) P_def) *)
  apply (simp add: assms(2))
  done


text\<open>This version is for parametrized process\<close>
lemma df_step_param_intro:
  assumes P_def: "\<And> x. P x = Q x" "\<And> x. (GlobalNdet UNIV P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q x"
  shows "deadlock_free (\<sqinter> n \<in> UNIV. P n)"
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (subst P_def)  back
  apply (simp add: assms(2) mono_GlobalNdet_FD_const)
  done


lemma df_step_param_intro_skip:
  assumes P_def: "\<And> x. P x = Q x" "\<And> x. (GlobalNdet UNIV P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q x"
  shows "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. P n)"
  sorry
(*  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free_skip)
  apply (subst P_def)  back
  apply (simp add: assms(2) mono_GlobalNdet_FD_const)
  done
*)
lemma prefix_recursive_ddlf(*was named ex1_m'*):
  assumes P_def: \<open>P = (a \<rightarrow> P)\<close>
  shows \<open>deadlock_free P\<close> 
  apply (rule df_step_intro[OF P_def])
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD
[THEN sym])
  by (simp add: eat_lemma no_step_refine prefix_proving_Mndetprefix_UNIV_ref(3))(*through sledgehammer*)


lemma GlobalDet_is_STOP_iff : \<open>\<box>a \<in> A. P a = STOP \<longleftrightarrow> (\<forall>a \<in> A. P a = STOP)\<close>
  by (simp add: STOP_iff_T T_GlobalDet, safe, auto)

subsection\<open>extchoice\<close>
text\<open>this is added for P = d\<rightarrow>( (a \<rightarrow> b \<rightarrow> P) \<box> (b \<rightarrow> c \<rightarrow> P)) pattern: prefix of external choice\<close>
lemma ndet_prefix_ext_choice:
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D R"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> R"
  by (metis mono_Det_FD Det_id assms(1) assms(2))


lemma Ndet_trans_Det_FD :\<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> R \<sqsubseteq>\<^sub>F\<^sub>D S \<Longrightarrow> P \<sqinter> R \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> S\<close>
  by (meson Ndet_FD_Det dual_order.trans mono_Det_FD)


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
  assumes \<open>\<exists>i\<in>I. b(i)\<close> \<open>\<And> i. \<lbrakk> i \<in> I; b(i) \<rbrakk> \<Longrightarrow> \<sqinter>a \<in> UNIV \<rightarrow> X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P(i)\<close>
  shows \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D \<box> i\<in>I. b(i) \<^bold>& P(i)\<close>
proof (rule trans_FD)
  show \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*\<close>
    by (simp add: Mndetprefix_GlobalNdet eat_lemma mono_GlobalNdet_FD_const)
next
  show "\<sqinter>a\<in>UNIV \<rightarrow> X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D \<box>i\<in>I. b i \<^bold>& P i"
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
  have "?lhs = (\<box> i\<in>{0..n::nat}. b(i) \<^bold>& P(i)) \<box> True \<^bold>& Q"
    by (simp add: Guard_True)
  also have "... = ?rhs"
    using biextchoic_normalization by blast
  finally show ?thesis .
qed



lemma biextchoic_normalization_nguard_prefix[normalisation]:
  "(\<box> i\<in>{0..n::nat}. b(i) \<^bold>& P(i)) \<box> (a \<rightarrow> Q) 
   = (\<box> i\<in>{0..n+1}. (if i \<le> n then b(i) else True) \<^bold>& (if i \<le> n then P(i) else a \<rightarrow> Q))"
  (is "?lhs = ?rhs")
  using biextchoic_normalization_nguard by blast


lemma GlobalNdet_refine_no_step [normalisation]: "a \<in> A \<Longrightarrow> (GlobalNdet A P)\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P a"
  by (meson GlobalNdet_refine_FD UNIV_I no_step_refine trans_FD)

subsection\<open>interrupt\<close>
text\<open>For the pattern in Trans : SSTOP@term{\<triangle>}, we need a lemma to deal with ddlf \<close>

lemma interrupt_ref:
  assumes "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P" and "Q = a \<rightarrow> Q"
  shows "X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  Q \<triangle> P"
proof (unfold refine_defs, safe)
  show \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t Y
  proof (induct t)
    from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D  P\<close> show \<open>([], Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> ([], Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
      apply (subst (asm) \<open>Q = a \<rightarrow> Q\<close>)
      apply (simp add: refine_defs write0_projs F_Interrupt GlobalNdet_iterations'_def F_GlobalNdet F_iterate_Mndetprefix_UNIV subset_iff)
      by (metis append_is_Nil_conv is_processT6_TR is_processT8 list.size(3) self_append_conv2)
  next
    fix e t Y assume hyp : \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    assume \<open>(e # t, Y) \<in> \<F> (Q \<triangle> P)\<close>
    hence \<open>(e # t, Y) \<in> \<F> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    then consider \<open>(e # t, Y) \<in> \<F> P\<close> | \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      by (auto simp add: Interrupt_write0 F_Det F_write0)
    thus \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    proof cases
      assume \<open>(e # t, Y) \<in> \<F> P\<close>
      with \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        by (simp add: refine_defs subset_iff)
    next
      assume \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      from this(2)[THEN hyp] have \<open>(t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> .
      thus \<open>(e # t, Y) \<in> \<F> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        apply (auto simp add: \<open>e = ev a\<close> GlobalNdet_iterations'_def F_GlobalNdet F_iterate_Mndetprefix_UNIV)
        by (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.discI(1) tickFree_Cons_iff)
    qed
  qed
next
  show \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close> for t
  proof (induct t)
    from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>[] \<in> \<D> (Q \<triangle> P) \<Longrightarrow> [] \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
      by (simp add: refine_defs subset_iff D_Interrupt GlobalNdet_iterations'_def D_GlobalNdet D_iterate_Mndetprefix_UNIV)
        (metis Nil_is_append_conv Nil_notin_D_Mprefix assms(2) write0_def)
  next
    fix e t assume hyp : \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    assume \<open>e # t \<in> \<D> (Q \<triangle> P)\<close>
    hence \<open>e # t \<in> \<D> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    hence \<open>e # t \<in> \<D> P \<or> t \<in> \<D> (Q \<triangle> P)\<close>
      by (auto simp add: D_Interrupt write0_projs)
    thus \<open>e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
    proof (elim disjE)
      from \<open>X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>e # t \<in> \<D> P \<Longrightarrow> e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        by (simp add: refine_defs subset_iff)
    next
      show \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> e # t \<in> \<D> (X\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>*)\<close>
        by (auto simp add: GlobalNdet_iterations'_def D_GlobalNdet D_iterate_Mndetprefix_UNIV dest!: hyp)
          (metis D_imp_front_tickFree \<open>e # t \<in> \<D> (Q \<triangle> P)\<close> append.left_neutral
            append_Cons front_tickFree_nonempty_append_imp is_processT7)
    qed
  qed
qed

text\<open>Interrupt_Seq proved by Benoit\<close>
(* not used here *)
lemma non_terminating_is_empty_ticks_of : \<open>non_terminating P \<longleftrightarrow> \<checkmark>s(P) = {}\<close>
  by (simp add: non_terminating_is_right tickFree_traces_iff_empty_ticks_of)

\<comment> \<open>Counter example (without parameterized termination)\<close>

lemma \<open>((0 :: nat) \<rightarrow> STOP) \<triangle> Skip \<^bold>; STOP \<noteq> (0 \<rightarrow> STOP) \<triangle> (Skip \<^bold>; STOP)\<close>
      apply simp
  apply (simp add: Process_eq_spec Seq_projs write0_projs Interrupt_projs STOP_projs SKIP_projs)
  apply (simp add: set_eq_iff)
  by (metis insertI1 list.discI tickFree_Nil)

lemma \<open>non_terminating ((0 :: nat) \<rightarrow> STOP)\<close>
  by (simp add: non_terminating_is_empty_ticks_of ticks_of_write0)


\<comment> \<open>Weaker version, but hopefully sufficient\<close>

lemma non_terminating_Interrupt_Seq :
  \<open>(P \<triangle> Q) \<^bold>; R = P \<triangle> (Q \<^bold>; R)\<close> (is \<open>?lhs = ?rhs\<close>)
  if \<open>non_terminating P\<close> and \<open>Q\<^sup>0 \<inter> range tick = {}\<close>
proof -
  have non_ter [simp] : \<open>t @ [\<checkmark>(r)] \<in> \<T> P \<longleftrightarrow> False\<close> for t r
    by (metis \<open>non_terminating P\<close> non_terminating_is_right non_tickFree_tick tickFree_append_iff)
  have not_tick_init : \<open>[\<checkmark>(r)] \<in> \<T> Q \<longleftrightarrow> False\<close> for r
    by (meson disjoint_iff initials_memI rangeI \<open>Q\<^sup>0 \<inter> range tick = {}\<close>)
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then consider \<open>t \<in> \<D> P\<close> | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>v \<in> \<D> Q\<close>
      | u v r u1 u2 where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>u2 \<in> \<T> Q\<close> \<open>v \<in> \<D> R\<close>
      by (auto simp add: D_Seq Interrupt_projs)
    thus \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      show \<open>t \<in> \<D> P \<Longrightarrow> t \<in> \<D> ?rhs\<close> by (simp add: D_Seq D_Interrupt)
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> tF u \<Longrightarrow> v \<in> \<D> Q \<Longrightarrow> t \<in> \<D> ?rhs\<close> for u v
        by (auto simp add: D_Interrupt D_Seq)
    next
      fix u v r u1 u2 assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close>
        \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>u2 \<in> \<T> Q\<close> \<open>v \<in> \<D> R\<close>
      from this(2, 4, 5) obtain u2'
        where \<open>u = u1 @ u2'\<close> \<open>u2 = u2' @ [\<checkmark>(r)]\<close>
        by (metis (no_types) T_nonTickFree_imp_decomp append.assoc
            append1_eq_conv non_tickFree_tick tickFree_append_iff)
      with \<open>tF u1\<close> \<open>u1 \<in> \<T> P\<close> \<open>u2 \<in> \<T> Q\<close> \<open>v \<in> \<D> R\<close> show \<open>t \<in> \<D> ?rhs\<close>
        by (simp add: \<open>t = u @ v\<close> D_Seq D_Interrupt) blast
    qed
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (simp add: Interrupt_projs Seq_projs) (metis append_assoc)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then consider \<open>(t, X \<union> range tick) \<in> \<F> (P \<triangle> Q)\<close> \<open>tF t\<close>
      | u r v where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close> \<open>(v, X) \<in> \<F> R\<close>
      by (auto simp add: Seq_projs)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>(t, X \<union> range tick) \<in> \<F> (P \<triangle> Q)\<close> \<open>tF t\<close>
      with \<open>t \<notin> \<D> ?lhs\<close> consider \<open>(t, X \<union> range tick) \<in> \<F> P\<close> \<open>tF t\<close> \<open>([], X \<union> range tick) \<in> \<F> Q\<close>
        | t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tF t1\<close> \<open>(t2, X \<union> range tick) \<in> \<F> Q\<close> \<open>t2 \<noteq> []\<close>
        by (auto simp add: Interrupt_projs D_Seq)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        show \<open>\<lbrakk>(t, X \<union> range tick) \<in> \<F> P; tF t; ([], X \<union> range tick) \<in> \<F> Q\<rbrakk>
              \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
          by (auto simp add: F_Interrupt F_Seq intro: is_processT4)
      next
        show \<open>\<lbrakk>t = t1 @ t2; t1 \<in> \<T> P; tF t1; (t2, X \<union> range tick) \<in> \<F> Q; t2 \<noteq> []\<rbrakk>
              \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t1 t2
          by (use \<open>tF t\<close> in \<open>auto simp add: F_Interrupt F_Seq\<close>)
      qed
    next
      fix u r v assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close> \<open>(v, X) \<in> \<F> R\<close>
      then obtain u1 u2 where \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>u2 \<in> \<T> Q\<close>
        by (auto simp add: T_Interrupt)
      from \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> obtain u2'
        where \<open>u2 = u2' @ [\<checkmark>(r)]\<close> \<open>u = u1 @ u2'\<close>
        by (metis append.right_neutral append_butlast_last_id
            butlast_append butlast_snoc last_appendR last_snoc non_ter)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
        apply (simp add: F_Interrupt \<open>t = u @ v\<close> Seq_projs)
        by (metis Nil_is_append_conv \<open>(v, X) \<in> \<F> R\<close> \<open>tF u1\<close> \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>u2 \<in> \<T> Q\<close>
            append.right_neutral not_tick_init same_append_eq)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then consider \<open>(t, X) \<in> \<F> P\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> (Q \<^bold>; R)\<close>
      | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> (Q \<^bold>; R)\<close> \<open>v \<noteq> []\<close>
      apply (simp add: Interrupt_projs T_Seq Cons_eq_append_conv)
      by (smt (verit, best) D_T is_processT3_TR_append not_tick_init self_append_conv2)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      show \<open>(t, X) \<in> \<F> P \<Longrightarrow> tF t \<Longrightarrow> ([], X) \<in> \<F> (Q \<^bold>; R) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Seq F_Interrupt)
        by (metis (mono_tags, lifting) F_T append.right_neutral f_inv_into_f is_processT5 non_ter
            not_tick_init)
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> tF u \<Longrightarrow> (v, X) \<in> \<F> (Q \<^bold>; R) \<Longrightarrow> v \<noteq> [] \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        apply (simp add: F_Seq Interrupt_projs)
        by (smt (verit, best) append_assoc)
    qed
  qed
qed



subsection\<open>guard\<close>

lemma guard_pushed_in: \<open>g1 \<^bold>& (g2 \<^bold>& P ) = ( g1 \<and> g2 ) \<^bold>& P\<close>
  by (simp add: Guard_def)

subsection\<open>sequential\<close>

lemma skip_seq:\<open>g1 \<^bold>& (P \<^bold>; (a\<rightarrow> Skip)) \<^bold>; Q = g1 \<^bold>& (P \<^bold>; a\<rightarrow> Q)\<close>
  by (metis Guard_def SKIP_Seq STOP_Seq Seq_assoc write0_Seq)




(*
section\<open>New lemmas, but not used\<close>
lemma Mndetprefix_trans_subset_FD : 
  \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> Q a \<sqsubseteq>\<^sub>F\<^sub>D P a) \<Longrightarrow>
   Mndetprefix B Q \<sqsubseteq>\<^sub>F\<^sub>D Mndetprefix A P\<close>
  by (simp add: prefix_proving_Mndetprefix_ref(1))


lemma DF_guard_extchoice:  assumes "b \<Longrightarrow> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D Q" "c \<Longrightarrow> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D R" "b \<or> c"
  shows "DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D (b \<^bold>& Q) \<box> (c \<^bold>& R)"
  by (metis (full_types) Det_STOP Det_commute Guard_False Guard_True assms deadlock_free_Det deadlock_free_def)



text\<open>20250326: We justified the euqivalence of RoboChart behaviour with the HOL-CSP model with state as paramter. Then, we need to update the proof into parametrized. this example proves a general deadlock free for any n. We do not use @term{\<And> in the conclusion}, instead we use @term{\<sqinter>}\<close>
lemma inc_df_ex_aux:
  assumes P_def: "\<And> i. P(i) = inc \<rightarrow> P (i + 1)"
  shows "deadlock_free (\<sqinter> n \<in> UNIV. P n)"
   (* Apply induction *)
  apply (rule df_step_param_intro[OF P_def])
  apply (simp add: one_step_ahead_GlobalNdet_iterations'_FD_iff_GlobalNdet_iterations_FD[THEN sym] )
  apply (auto intro!:prefix_proving_Mndetprefix_UNIV_ref(3) generalized_refine_guarded_extchoice_star eat_lemma no_step_refine)
  apply (rule order.trans)
  apply (rule no_step_refine)
  apply (meson GlobalNdet_refine_FD UNIV_I no_step_refine order.trans)
  done

lemma inc_df_ex_aux_specific:
  assumes P_def: "\<And> i. P(i) = inc \<rightarrow> P (i + 1)"
  shows "deadlock_free (P 0)"
  by (meson UNIV_I assms deadlock_free_GlobalNdet_iff inc_df_ex_aux)


lemma df_step_param_cont_intro:
  assumes P_def: "\<And> x. P\<cdot>x = Q x" "\<And> x. (GlobalNdet UNIV (\<lambda>x. P\<cdot>x))\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>+ \<sqsubseteq>\<^sub>F\<^sub>D Q x"
  shows "deadlock_free (\<sqinter> n \<in> UNIV. P\<cdot>n)"
  apply (rule GlobalNdet_iterations_FD_imp_deadlock_free)
  apply (subst P_def)  back
  apply (simp add: assms(2) mono_GlobalNdet_FD_const) 
  done


lemma guard_choice:
  assumes "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D (a \<^bold>&  Q)" "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D (b \<^bold>&  R)"
  shows "P\<^sup>p\<^sup>r\<^sup>o\<^sup>c\<^sup>* \<sqsubseteq>\<^sub>F\<^sub>D (a  \<^bold>& Q) \<box> (b  \<^bold>&  R)"
  by (metis mono_Det_FD Det_id assms(1) assms(2))


lemma refine_guarded_extchoice:   
  assumes "b \<or> c" "b \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D Q" "c \<Longrightarrow> \<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D R"
  shows "\<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D (b \<^bold>& Q) \<box> (c \<^bold>& R)"
  by (metis Det_STOP Det_commute FD_iff_eq_Ndet Guard_def Ndet_trans_Det_FD assms idem_FD)


lemma extchoice_preguard: "(b \<or> c) \<^bold>& (b \<^bold>& Q) \<box> (c \<^bold>& R) = (b \<^bold>& Q) \<box> (c \<^bold>& R)"
  by (simp add: Guard_def)



lemma GlobalDet_preguard :
  \<comment>\<open>Without the assumption \<^term>\<open>finite I\<close>.\<close>
  \<open>(Sup (b ` I) \<^bold>& (\<box> i\<in>I. b (i) \<^bold>& (P i))) = \<box> i\<in>I. b i \<^bold>& P i\<close>
  by (auto intro: Process_eq_optimizedI
      simp add: Guard_def GlobalDet_projs STOP_projs
      split: if_split_asm)


lemma MultiDet_preguard: "finite I \<Longrightarrow> (Sup (b ` I) \<^bold>& (\<box> i\<in>I. b (i) \<^bold>& (P i))) = (\<box> i\<in>I. b i \<^bold>& P i)"
  apply (induct arbitrary: b P rule: finite_induct)
   apply (auto simp add: Guard_def Det_is_STOP_iff GlobalDet_is_STOP_iff)
  by (metis (mono_tags, lifting) GlobalDet_factorization_union GlobalDet_unit STOP_Det
      insert_def singleton_conv)

lemma skip_seq2:\<open>g1 \<^bold>& (P \<^bold>; Q \<^bold>; (a\<rightarrow> Skip)) \<^bold>; R = g1 \<^bold>& (P \<^bold>; Q \<^bold>; a\<rightarrow> R)\<close>
  by (metis Guard_def SKIP_Seq STOP_Seq Seq_assoc write0_Seq)
*)

end