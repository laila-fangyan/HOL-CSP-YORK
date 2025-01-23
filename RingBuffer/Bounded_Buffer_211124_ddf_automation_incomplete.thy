\<comment>\<open> ********************************************************************
 * This version is based on 'Bounded_Buffer_120924_ddf_proved_by_Benoit.thy'.
 * effort is given to imporve automation of the DF.
 * 25 Oct 2024, lemma refine_guarded_extchoice proved
 * 15 Nov 2024, lemma generilized_refine_guarded_extchoice proved using MultDet.thy

 ******************************************************************************\<close>
theory Bounded_Buffer_151124_ddf_automation_incomplete
  imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete""HOL-CSPM.MultiDet"
          "HOLCF-Library.List_Cpo" "HOL-CSP_Proc-Omata.CompactificationSync"
          Guard
begin

default_sort type


no_notation floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)

no_notation Cons  ("_ \<cdot>/ _" [66,65] 65)


subsection\<open>The bounded buffer processes definition\<close>

locale BoundedBuffer =
  fixes maxbuff :: nat
  \<comment> \<open>The buffer is bounded in its length: it may hold no more than maxbuff elements\<close>
  assumes maxbuff_g0 [simp] : \<open>maxbuff > 0\<close>  

begin


\<comment> \<open>The process Buffer has two channels: input and output.\<close>
datatype ringbuf_event = rd "nat \<times> int" | wrt "nat \<times> int" | input int | "output" int


\<comment> \<open>A simple bounded reactive FIFO buffer 'BBuf' that is used to store natural numbers.\<close>
\<comment> \<open>There are two state variables:  the buffer size sz the contents of the buffer buff. 
These two are presented as parameters.\<close>
fixrec BBuf :: \<open>nat \<rightarrow> int list \<rightarrow> ringbuf_event process\<close> where
  [simp del]: \<open>BBuf\<cdot>sz\<cdot>buff = (sz < maxbuff) \<^bold>& (input\<^bold>?x \<rightarrow> BBuf\<cdot>(sz+1)\<cdot>(buff @ [x]))  \<box>
                  (sz > 0) \<^bold>& (output\<^bold>!(hd buff) \<rightarrow> BBuf\<cdot>(sz-1)\<cdot>(tl buff)) \<close>
\<comment> \<open>The input action is enabled if there is space in the buffer for the new input: sz < maxbuff.
 The new element is appended to the buffer's contents and the size is updated\<close>
\<comment> \<open>The output action is enabled if there is something in the buffer: sz>0. The first element (head) is
output; the others are retained in order; the size of the buffer is updated.\<close>


datatype 'a buffer_any_event =  input_any 'a | output_any 'a

definition BBuf_any :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a buffer_any_event process\<close>
  where \<open>BBuf_any \<equiv> \<mu> X. (\<lambda>sz buff. (sz < maxbuff) \<^bold>& (input_any\<^bold>?x \<rightarrow> X (sz+1) (buff @ [x]))  \<box>
                                     (sz > 0) \<^bold>& (output_any\<^bold>!(hd buff) \<rightarrow> X (sz-1) (tl buff))) \<close>

lemma BBuf_any_cont : 
  \<open>cont (\<lambda>x sz buff. (sz < maxbuff) \<^bold>& (input_any\<^bold>?xa \<rightarrow> x (sz + 1) (buff @ [xa])) \<box>
                     (0 < sz) \<^bold>& (output_any\<^bold>!hd buff \<rightarrow> x (sz - 1) (tl buff)))\<close>
  (is \<open>cont (\<lambda>x sz buff. ?f x sz buff \<box> ?g x sz buff)\<close>)
proof (rule cont2cont_lambda, rule cont2cont_lambda, rule Det_cont)
  show \<open>\<And>sz buff. cont (\<lambda>x. ?f x sz buff)\<close>
      (* TODO: understand why the continuity proof is so difficult *)
    apply (rule Guard_cont)
    apply (rule read_cont)
    apply (rule cont2cont_lambda)
    by (rule cont2cont_fun, simp add: cont_fun)
next
  show \<open>\<And>sz buff. cont (\<lambda>x. ?g x sz buff)\<close>
    apply (rule Guard_cont)
    apply (rule write_cont)
    by (metis cont2cont_fun cont_fun)
qed

lemma BBuf_any_unfold :
  \<open>BBuf_any sz buff = (sz < maxbuff) \<^bold>& (input_any\<^bold>?x \<rightarrow> BBuf_any (sz+1) (buff @ [x]))  \<box>
                      (sz > 0) \<^bold>& (output_any\<^bold>!(hd buff) \<rightarrow> BBuf_any (sz-1) (tl buff))\<close>
  (is \<open>BBuf_any sz buff = ?f BBuf_any sz buff \<box> ?g BBuf_any sz buff\<close>)
  by (subst cont_process_rec[OF BBuf_any_def[THEN meta_eq_to_obj_eq] BBuf_any_cont]) simp






end


\<comment> \<open>An implementation uses a ring of cells, each implemented as a  process, and a central controller that keeps track of
the indexes of the first and last elements (bot, top), offering the input and output services.\<close>
context BoundedBuffer
begin

definition maxring :: nat where \<open>maxring \<equiv> maxbuff - 1\<close>
\<comment> \<open>The maximum size of the ring is one less than the size of the buffer, as the head is cached.\<close>

declare maxring_def [simp]


\<comment> \<open>The indexes of the ring go from 0 to maxring-1.\<close>
definition ringindex ::  \<open>nat set\<close> where \<open>ringindex = {0..<maxring}\<close> 

\<comment> \<open>The channels rd and wrt are used for communication with the ring cells.\<close>
\<comment> \<open>The values communicated through rd and wrt are pairs, where the first element iden-
tifes a cell, and the second element is the number actually communicated.\<close>


term size

\<comment> \<open>The solution is to cache the head (first element, bottom of stack) of the ring in the controller, and distribute
only the tail of the buffer around the ring.\<close>
\<comment> \<open>The state of the controller contains the size of the buffer (sz), the cache,
and two ring indexes, keeping track of the index of the next available position (top)
and the index of the first value stored (bot).\<close>


fixrec  Cell     :: \<open>nat \<rightarrow> int \<rightarrow> ringbuf_event process\<close> 
    and RingCell :: \<open>nat \<rightarrow> ringbuf_event process\<close> 
(*    and Ring     :: \<open>int  \<rightarrow> ringbuf_event process\<close> *) 
    and Ctrl     :: \<open>nat \<rightarrow> int \<rightarrow> nat  \<rightarrow> nat  \<rightarrow> ringbuf_event process\<close> 

where

[simp del] : \<open>Cell\<cdot>n\<cdot>v =  (rd\<^bold>!(n,v) \<rightarrow> Cell\<cdot>n\<cdot>v)  \<box>
               (wrt\<^bold>?(i,x) \<in> {i. i = n} \<times> UNIV \<rightarrow> Cell\<cdot>n\<cdot>x) \<close>

|[simp del] : \<open>RingCell\<cdot>n = (wrt\<^bold>?(i,x) \<in> {i. i = n} \<times> UNIV \<rightarrow> Cell\<cdot>n\<cdot>x) \<close>

|[simp del] : \<open>Ctrl\<cdot>sz\<cdot>cache\<cdot>to\<cdot>bo = ((input\<^bold>?x \<rightarrow> ((sz=0) \<^bold>& Ctrl\<cdot>1\<cdot>x\<cdot>to\<cdot>bo)  \<box>
                                    ((sz>0 \<and> sz< maxbuff) \<^bold>& (wrt\<^bold>!(to,x) \<rightarrow>
 Ctrl\<cdot>(sz+1)\<cdot>cache\<cdot>((to+1)mod maxring) \<cdot> bo)) )
                                  
                        \<box>
                        (((sz > 0) \<^bold>& (output\<^bold>!cache \<rightarrow>
                              ((sz>1)  \<^bold>& (rd\<^bold>?(i,x) \<in> {i. i = bo} \<times> UNIV \<rightarrow> Ctrl\<cdot>(sz-1)\<cdot>x\<cdot>to\<cdot>((bo+1)mod maxring)))
                              \<box>
                              (sz=1) \<^bold>& Ctrl\<cdot>0\<cdot>cache\<cdot>to\<cdot>bo  ) )))\<close>



\<comment> \<open>Controller: The input action depends on whether the buffer is empty: sz=0. 
If it is empty, then this input must be kept in the cache, not in the ring cell; 
if it is non-empty and there is space in the buffer, then the controller transmits
the input x to the cell at the top of the ring, the top index advances 
(the index of the next available position).the cache is ocuppied and unchanged. 
if it is full, then no input action is possible. 
When the input is cached, the top and bot indexes do not change.
\<close>
\<comment> \<open>Controller: The output always comes from the cache, which must be replaced if the ring is non-empty. 
The output action ' output!cache' is enabled when the buffer is non-empty: sz>0. 
In the case that the ring is empty, we have size = 1, the value is stored in cache; 
after output, buffer size sz is reset to 0; nothing else changes.? ? cache = null? ?
If the ring is non-empty: sz>1,
the controller obtains the input x from the cell at the bot of the ring.\<close>



(*\<open>Ctrl\<cdot>sz\<cdot>cache\<cdot>top\<cdot>bot = (input?x \<rightarrow> (sz=0 \<^bold>& Ctrl\<cdot>1\<cdot>x\<cdot>top\<cdot>bot)  \<box>
                                   (sz>0 \<^bold>& wrt.top!x \<rightarrow> Ctrl\<cdot>(sz+1)\<cdot>cache\<cdot>bot\<cdot>(top+1)mod maxring) )
                        \<box>
                        (sz > 0 \<^bold>& output!cache \<rightarrow>
                              (sz>1  \<^bold>& rd.bot\<^bold>?x \<rightarrow> Ctrl\<cdot>(sz-1)\<cdot>x\<cdot>top\<cdot>(bot+1)mod maxring)
                              \<box>
                              sz=1 \<^bold>&  Ctrl\<cdot>0\<cdot>cache\<cdot>bot\<cdot>top  )\<close>*)

term RingCell

definition
\<open>Ring = \<^bold>|\<^bold>|\<^bold>| i \<in># mset [0..<maxring]. RingCell\<cdot>i \<close>


\<comment> \<open>TODO: change the name, confusion with \<^const>\<open>Sync\<close>\<close>

definition Syn  :: \<open>ringbuf_event set\<close>
  where     \<open>Syn  \<equiv> {rd x | x. True} \<union> {wrt x | x . True}\<close>

definition RingBuffer :: \<open>ringbuf_event process\<close>
  where \<open>RingBuffer = (Ctrl\<cdot>0\<cdot>0\<cdot>0\<cdot>0 \<lbrakk>Syn\<rbrakk> Ring) \ Syn\<close>


find_theorems Ctrl

text \<open>First, we prove that the bounded buffer is deadlock free.\<close>

(* TODO: move this in CSP *)
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


(* Tasks: 
   (1) Generalise the guarded external choice theorem, so we can handle multiple branches -- probably requires an n-ary/replicated external choice;
   (2) Allow a deadlock freedom proof to make multiple steps before reaching the hypothesis process. 
*)

(* How can we prove a lemma like the below? Can we generalise this to a finite number of 
  internal choices? *)

thm fix_ind_k

lemma "(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow> X) = (\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow> \<sqinter>x\<in>UNIV \<rightarrow> X)"
  oops

lemma deadlock_free_BBuf : \<open>deadlock_free (BBuf\<cdot>(length L)\<cdot>L)\<close>
proof (unfold deadlock_free_def DF_def)
  show \<open>(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow> X) \<sqsubseteq>\<^sub>F\<^sub>D BBuf\<cdot>(length L)\<cdot>L\<close>
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
        apply (rule refine_guarded_extchoice)
          apply fastforce
            apply (simp_all add: read_def write_def)
         apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD]; simp)
         apply (metis hyp length_append_singleton)
         apply (rule trans_FD[OF Mndetprefix_trans_subset_FD Mprefix_refines_Mndetprefix_FD]; simp)
        apply (metis One_nat_def hyp length_tl)
        done
    qed
  qed
qed


lemma deadlock_free_BBuf : \<open>deadlock_free (BBuf\<cdot>(length L)\<cdot>L)\<close>
proof (unfold deadlock_free_def DF_def)
  show \<open>(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow>  X) \<sqsubseteq>\<^sub>F\<^sub>D BBuf\<cdot>(length L)\<cdot>L\<close>
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


corollary \<open>deadlock_free (BBuf\<cdot>0\<cdot>[])\<close>
  by (metis deadlock_free_BBuf list.size(3))


text \<open>Actually, the proof also works for the generalized version\<close>

lemma deadlock_free_BBuf_any : \<open>deadlock_free (BBuf_any (length L) L)\<close>
proof (unfold deadlock_free_def DF_def)
  show \<open>(\<mu> X. \<sqinter>x\<in>UNIV \<rightarrow>  X) \<sqsubseteq>\<^sub>F\<^sub>D  BBuf_any (length L) L\<close>
  proof (induct arbitrary: L rule: fix_ind)
    show \<open>adm (\<lambda>a. \<forall>L. a \<sqsubseteq>\<^sub>F\<^sub>D  BBuf_any (length L) L)\<close> by (simp add: monofunI)
  next
    show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D  BBuf_any (length L) L\<close> for L :: \<open>'a list\<close> by simp
  next
    fix X :: \<open>'a buffer_any_event process\<close> and L :: \<open>'a list\<close>
    assume hyp : \<open>X \<sqsubseteq>\<^sub>F\<^sub>D BBuf_any (length L) L\<close> for L
    show \<open>(\<Lambda> X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D BBuf_any (length L) L\<close>
    proof (subst beta_cfun)
      show \<open>cont (\<lambda>X. \<sqinter>x\<in>UNIV \<rightarrow> X)\<close> by simp
    next
      show \<open>\<sqinter>x\<in>UNIV \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D BBuf_any (length L) L\<close>
        apply (subst BBuf_any_unfold)
        apply simp
      proof -
        consider \<open>L = []\<close> \<open>length L < maxbuff\<close> | \<open>L \<noteq> []\<close> \<open>length L < maxbuff\<close>
        | \<open>L \<noteq> []\<close> \<open>\<not> length L < maxbuff\<close> by auto \<comment> \<open>we use @{thm maxbuff_g0} here\<close>
        thus \<open>\<sqinter>x\<in>UNIV \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D
             (length L < maxbuff) \<^bold>&
             (input_any\<^bold>?x \<rightarrow> BBuf_any (Suc (length L)) (L @ [x])) \<box>
             (L \<noteq> []) \<^bold>& (output_any\<^bold>!hd L \<rightarrow> BBuf_any (length L - Suc 0) (tl L))\<close>
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

corollary \<open>deadlock_free (BBuf_any 0 [])\<close>
  by (metis deadlock_free_BBuf_any list.size(3))


text \<open>The refinement\<close>


lemma \<open>BBuf\<cdot>0\<cdot>[] \<sqsubseteq>\<^sub>F\<^sub>D RingBuffer\<close>
proof (induct rule: BBuf.induct)
  show \<open>adm (\<lambda>BBuf. BBuf\<cdot>0\<cdot>[] \<sqsubseteq>\<^sub>F\<^sub>D RingBuffer)\<close>
    by (simp add: monofunI)
next
  show \<open>\<bottom>\<cdot>0\<cdot>[] \<sqsubseteq>\<^sub>F\<^sub>D RingBuffer\<close> by simp
next
  fix B :: \<open>nat \<rightarrow> int list \<rightarrow> ringbuf_event process\<close>
  assume \<open>B\<cdot>0\<cdot>[] \<sqsubseteq>\<^sub>F\<^sub>D RingBuffer\<close>
  show \<open>(\<Lambda> sz buff.
        (sz < maxbuff) \<^bold>& (input\<^bold>?xa \<rightarrow> B\<cdot>(sz + 1)\<cdot>(buff @ [xa])) \<box>
        (0 < sz) \<^bold>& (output\<^bold>!hd buff \<rightarrow> B\<cdot>(sz - 1)\<cdot>(tl buff)))\<cdot>0\<cdot>[]
        \<sqsubseteq>\<^sub>F\<^sub>D RingBuffer\<close>
  proof (simp add: Det_STOP) (* forbidden by the linter, but well... *)
    show \<open>input\<^bold>?x \<rightarrow> B\<cdot>(Suc 0)\<cdot>[x] \<sqsubseteq>\<^sub>F\<^sub>D RingBuffer\<close>
      apply (unfold RingBuffer_def Ring_def)
      apply (subst Ctrl.unfold, simp add: Det_STOP)
      (* some work here, probably easier with compactification *)
      sorry
  qed
qed




end

end