theory Casper
imports Main "Eisbach"
begin

locale byz_quorums =
  fixes member_1 :: "'n \<Rightarrow> 'q1 \<Rightarrow> bool" (infix "\<in>\<^sub>1" 50)(* membership in 2/3 set *)
    and member_2 :: "'n \<Rightarrow> 'q2 \<Rightarrow> bool" (infix "\<in>\<^sub>2" 50)(* membership in 1/3 set *)
  assumes "\<And> q1 q2 . \<exists> q3 . \<forall> n . n \<in>\<^sub>2 q3 \<longrightarrow> n \<in>\<^sub>1 q1 \<and> n \<in>\<^sub>1 q2"  (* 2/3 quorums have 1/3 intersection *)
    (* and "\<And> q1 q2 . \<exists> n . n \<in>\<^sub>2 q1 \<and> n \<in>\<^sub>1 q2" *) (* 2/3 sets and 1/3 sets intersect *)
    (* and "\<And> q . \<exists> n . n \<in>\<^sub>2 q" *)

record ('n,'h,'v)state =
  -- "@{typ 'n} is the type of validators (nodes), @{typ 'h} hashes, and @{typ nat} views"
  commit_msg :: "'n \<Rightarrow> 'h \<Rightarrow> nat \<Rightarrow> bool"
  prepare_msg :: "'n \<Rightarrow> 'h \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bool"

locale casper = byz_quorums +
fixes 
  hash_pred :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "\<leftarrow>" 50)
assumes
  -- "a hash has at most one predecessor which is not itself"
  "\<And> h1 h2 . h1 \<leftarrow> h2 \<Longrightarrow> h1 \<noteq> h2"
  and "\<And> h1 h2 h3 . \<lbrakk>h2 \<leftarrow> h1; h3 \<leftarrow> h1\<rbrakk> \<Longrightarrow> h2 = h3"
begin

inductive hash_ancestor (infix "\<leftarrow>\<^sup>*" 50) where 
  "h1 \<leftarrow> h2 \<Longrightarrow> h1 \<leftarrow>\<^sup>* h2"
| "\<lbrakk>h1 \<leftarrow> h2; h2 \<leftarrow>\<^sup>* h3\<rbrakk> \<Longrightarrow> h1 \<leftarrow>\<^sup>* h3"
declare hash_ancestor.intros[simp,intro]

inductive nth_parent :: "nat \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> bool" where 
  "nth_parent 0 h1 h1"
| "\<lbrakk>nth_parent n h1 h2; h2 \<leftarrow> h3\<rbrakk> \<Longrightarrow> nth_parent (n+1) h1 h3"
declare nth_parent.intros[simp,intro]

inductive_cases test2:"nth_parent 1 h1 h2"
thm test2

lemmas casper_assms_def = casper_def casper_axioms_def class.linorder_def class.order_def
    class.preorder_def class.order_axioms_def class.linorder_axioms_def byz_quorums_def
    class.order_bot_def class.order_bot_axioms_def

text {* All messages in epoch @{term 0} are ignored;  @{term 0} is used as a special value. *}

definition prepared where 
  "prepared s q h v1 v2 \<equiv> v1 \<noteq> 0 \<and> (\<forall> n . n \<in>\<^sub>1 q \<longrightarrow> prepare_msg s n h v1 v2)"
definition committed where
  "committed s q h v \<equiv> v \<noteq> 0 \<and> (\<forall> n . n \<in>\<^sub>1 q \<longrightarrow> commit_msg s n h v)"
definition fork where 
  "fork s \<equiv> \<exists> h1 h2 q1 q2 v1 v2 . committed s q1 h1 v1 \<and> committed s q2 h2 v2
    \<and> \<not>(h2 \<leftarrow>\<^sup>* h1 \<or> h1 \<leftarrow>\<^sup>* h2 \<or> h1 = h2)"

definition slashed_1 where  "slashed_1 s n \<equiv> 
  \<exists> h v . commit_msg s n h v \<and> (\<forall> q v2 . v2 < v \<longrightarrow> \<not>prepared s q h v v2)"
definition slashed_2 where
  "slashed_2 s n \<equiv>
  \<exists> h v1 v2 . prepare_msg s n h v1 v2 \<and> v2 \<noteq> 0 \<and>
    (\<forall> v3 q h2 . v3 < v2 \<longrightarrow> \<not>(nth_parent (v1 - v2) h2 h \<and> prepared s q h2 v2 v3))"
definition slashed_2' where
  -- "this is not exactly what Vitalik wrote."
  "slashed_2' s n \<equiv>
  \<exists> h v1 v2 . prepare_msg s n h v1 v2 \<and> v2 \<noteq> 0 \<and>
    (\<forall> v3 q h2 . v3 < v2 \<longrightarrow> \<not>(h2 \<leftarrow> h \<and> prepared s q h2 v2 v3))"
definition slashed_3 where 
  "slashed_3 s n \<equiv>
  \<exists> h1 h2 v1 v2 v3 . v1 < v2 \<and> v3 < v1 \<and> 
    commit_msg s n h1 v1 \<and> prepare_msg s n h2 v2 v3"
definition slashed_4 where
  "slashed_4 s n \<equiv> \<exists> h1 h2 v v1 v2 . (h1 \<noteq> h2 \<or> v1 \<noteq> v2) \<and> 
    prepare_msg s n h1 v v1 \<and> prepare_msg s n h2 v v2"

definition slashed where "slashed s n \<equiv> 
  slashed_1 s n \<or> slashed_2 s n \<or> slashed_3 s n \<or> slashed_4 s n"

lemma assumes "prepared s q h1 v1 v2" and "committed s q h2 v2" and "v1 > v2"
  and "\<not>nth_parent (v1 - v2) h2 h1"
shows "\<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed s n"
  using assms
proof (induct "v1 - v2 - 1")
  case 0
  have "\<not>h2 \<leftarrow> h1"
    by (metis "0.hyps" Nat.add_0_right One_nat_def Suc_diff_Suc add_Suc_right assms(3) assms(4) diff_diff_left nth_parent.intros(1) nth_parent.intros(2))  
  then show ?case using 0
  using assms casper_axioms nth_parent.intros
  unfolding slashed_def slashed_1_def slashed_2_def slashed_4_def slashed_3_def
      prepared_def fork_def committed_def casper_assms_def
  apply auto
  using [[smt_infer_triggers,smt_timeout=3000,smt_oracle=true,smt_random_seed=3143,smt_certificates="./casper.cert"]]
next
  case (Suc x)
  then show ?case sorry
qed oops

lemma assumes "fork s"
  shows "\<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed s n" oops
  using [[]]
  nitpick[verbose, card 'b=2, card 'c=2, card 'a=5, card nat=5, card 'h=4, card 'd=1,
      card "('a, 'h, nat, 'd) state_scheme" = 1, dont_box, timeout=300] (*,
      eval="(slashed s, committed s)"] *)
  using assms casper_axioms
  apply -
  unfolding slashed_def slashed_1_def slashed_2_def slashed_4_def slashed_3_def
      prepared_def fork_def committed_def
  apply (cases s)
  apply simp
  using hash_ancestor.intros nth_parent.intros
  unfolding casper_assms_def
  apply (simp (no_asm_use))
  apply (match premises in P[thin]:"?x = ?y" \<Rightarrow> \<open>-\<close>)
  apply clarify oops
  using [[smt_infer_triggers,smt_timeout=3000,smt_oracle=true,smt_random_seed=8789797972,smt_certificates="./casper.cert"]]
  sledgehammer[timeout=5000, provers=z3 spass]()


end