theory Casper
  imports Main
begin

text {* We use first-order modeling as much as possible. This allows to reduce the size of the model, 
  and also the size of the proofs from more than 1000 lines in Yoichi's proof to less than a 100. *}

locale byz_quorums =
  -- "Here we fix two types @{typ 'q1} and @{typ 'q2} for quorums of cardinality greater than 2/3 of 
the validators and quorum of cardinality greater than 1/3 of the validators."
  fixes member_1 :: "'n \<Rightarrow> 'q1 \<Rightarrow> bool" (infix "\<in>\<^sub>1" 50)
    -- "Membership in 2/3 set"
    and member_2 :: "'n \<Rightarrow> 'q2 \<Rightarrow> bool" (infix "\<in>\<^sub>2" 50)
    -- "Membership in 1/3 set"
  assumes "\<And> q1 q2 . \<exists> q3 . \<forall> n . n \<in>\<^sub>2 q3 \<longrightarrow> n \<in>\<^sub>1 q1 \<and> n \<in>\<^sub>1 q2"  
    -- "This is the only property of types @{typ 'q1} and @{typ 'q2} that we need: 
2/3 quorums have 1/3 intersection"

record ('n,'h)state =
  -- "@{typ 'n} is the type of validators (nodes), @{typ 'h} hashes, and views are @{typ nat}"
  commit_msg :: "'n \<Rightarrow> 'h \<Rightarrow> nat \<Rightarrow> bool"
  prepare_msg :: "'n \<Rightarrow> 'h \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"

locale casper = byz_quorums +
  -- "Here we make assumptions about hashes. In reality any message containing a hash not satisfying those
should be dropped."
fixes 
  hash_parent :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "\<leftarrow>" 50)
assumes
  -- "a hash has at most one parent which is not itself"
  "\<And> h1 h2 . h1 \<leftarrow> h2 \<Longrightarrow> h1 \<noteq> h2"
  and "\<And> h1 h2 h3 . \<lbrakk>h2 \<leftarrow> h1; h3 \<leftarrow> h1\<rbrakk> \<Longrightarrow> h2 = h3"
begin

lemmas casper_assms_def = casper_def casper_axioms_def byz_quorums_def

inductive hash_ancestor (infix "\<leftarrow>\<^sup>*" 50) where 
  "h1 \<leftarrow> h2 \<Longrightarrow> h1 \<leftarrow>\<^sup>* h2"
| "\<lbrakk>h1 \<leftarrow> h2; h2 \<leftarrow>\<^sup>* h3\<rbrakk> \<Longrightarrow> h1 \<leftarrow>\<^sup>* h3"
declare hash_ancestor.intros[simp,intro]
lemma hash_ancestor_intro': assumes "h1 \<leftarrow>\<^sup>* h2" and "h2 \<leftarrow> h3" shows "h1 \<leftarrow>\<^sup>* h3" 
  using assms by (induct h1 h2 rule:hash_ancestor.induct) auto

inductive nth_ancestor :: "nat \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> bool" where 
  "nth_ancestor 0 h1 h1"
| "\<lbrakk>nth_ancestor n h1 h2; h2 \<leftarrow> h3\<rbrakk> \<Longrightarrow> nth_ancestor (n+1) h1 h3"
declare nth_ancestor.intros[simp,intro]
inductive_cases nth_ancestor_succ:"nth_ancestor (n+1) h1 h3"
inductive_cases zeroth_ancestor:"nth_ancestor 0 h1 h3"
lemma parent_ancestor:"h1 \<leftarrow> h2 = nth_ancestor 1 h1 h2"
  by (metis One_nat_def add.right_neutral add_Suc_right add_diff_cancel_left' diff_Suc_Suc nat.simps(3) nth_ancestor.simps)

text {* All messages in epoch @{term "0::nat"} are ignored;  @{term "0::nat"} is used as a special value (was @{term "-1::int"} in the original model). *}
definition prepared' where
  "prepared' s q h v1 v2 \<equiv> v1 \<noteq> 0 \<and> (\<forall> n . n \<in>\<^sub>1 q \<longrightarrow> prepare_msg s n h v1 v2)"
definition prepared where
  "prepared s q h v1 v2 \<equiv> v1 \<noteq> 0 \<and> v2 < v1 \<and> (\<forall> n . n \<in>\<^sub>1 q \<longrightarrow> prepare_msg s n h v1 v2)"
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
    (\<forall> v3 q h2 . v3 < v2 \<longrightarrow> \<not>(nth_ancestor (v1 - v2) h2 h \<and> prepared s q h2 v2 v3))"
definition slashed_3 where 
  "slashed_3 s n \<equiv>
  \<exists> h1 h2 v1 v2 v3 . v1 < v2 \<and> v3 < v1 \<and> 
    commit_msg s n h1 v1 \<and> prepare_msg s n h2 v2 v3"
definition slashed_4 where
  "slashed_4 s n \<equiv> \<exists> h1 h2 v v1 v2 . (h1 \<noteq> h2 \<or> v1 \<noteq> v2) \<and> 
    prepare_msg s n h1 v v1 \<and> prepare_msg s n h2 v v2"
definition slashed where "slashed s n \<equiv> 
  slashed_1 s n \<or> slashed_2 s n \<or> slashed_3 s n \<or> slashed_4 s n"
definition one_third_slashed where "one_third_slashed s \<equiv> \<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed s n"
lemmas slashed_defs = slashed_def slashed_1_def slashed_2_def slashed_4_def slashed_3_def one_third_slashed_def

lemmas order_defs = class.linorder_axioms_def class.linorder_def class.order_def class.preorder_def class.order_axioms_def class.order_bot_def class.order_bot_axioms_def linorder_axioms[where ?'a=nat]
lemmas casper_defs = slashed_defs prepared_def fork_def committed_def casper_assms_def

lemma l1: assumes "prepared s q1 h1 v1 v2" and "committed s q2 h2 v3" and "v1 > v3" and "\<not>one_third_slashed s"
  shows "v1 > v2 \<and> v2 \<ge> v3"
(*<*)  nitpick[verbose, card 'b=1, card 'c=1, card 'a=1, card nat=5, card 'h=4, card 'd=1,
      card "('a, 'h, 'd) state_scheme" = 1, dont_box, timeout=300, eval="fork s"] (*>*)
  using assms casper_axioms linorder_axioms[where ?'a=nat] unfolding casper_defs order_defs
  by smt

lemma l2: assumes "nth_ancestor n h1 h2" and "nth_ancestor m h2 h3" 
  shows "nth_ancestor (n+m) h1 h3" 
  using assms 
proof (induct m arbitrary: h1 h2 h3)
  case 0 then show ?case using nth_ancestor.cases by auto
next
  case (Suc m)
  then show ?case by (metis Suc_eq_plus1 add_Suc_right nth_ancestor.simps nth_ancestor_succ)
qed

lemma l3: assumes "prepared s q1 h1 v1 v2" and "committed s q2 h2 v3" and "v1 > v3" and "\<not>one_third_slashed s"
  shows "nth_ancestor (v1 - v3) h2 h1"
proof -
  show ?thesis using assms
  proof (induct "v1 - v3" arbitrary: v1 v2 v3 q1 q2 h1 h2 rule:less_induct)
    case less then show ?case 
    proof (cases "v1-v3=0")
      case True then show ?thesis using less.prems(3) by linarith  next
      case False then show ?thesis
      proof (cases "v2=v3")
        case True
        then show ?thesis using less(2-5) casper_axioms linorder_axioms[where ?'a=nat]
          using [[smt_solver=cvc4]] by (simp add: casper_defs, unfold order_defs) smt
      next
        case False
        obtain q3 h3 v4 where 1:"nth_ancestor (v1-v2) h3 h1" and 2:"prepared s q3 h3 v2 v4"
          by (metis less.prems(1-3) assms(4) byz_quorums_axioms byz_quorums_def committed_def diff_is_0_eq diff_zero l1 one_third_slashed_def prepared_def slashed_2_def slashed_def)
        have 3:"nth_ancestor (v2-v3) h2 h3"
          by (metis False 2 l1 diff_less_mono less.hyps less.prems less_le)
        have 4:"v1 > v2 \<and> v2 \<ge> v3" using assms casper.l1 casper_axioms less.prems(1-3) by metis
        show ?thesis using 1 3 4 less.prems(3) l2 by force
      qed
    qed
  qed
qed

lemma l4:assumes "nth_ancestor n (h1::'h) h2" shows "h1 \<leftarrow>\<^sup>* h2 \<or> h1 = h2" using assms
proof (induct n arbitrary:h1 h2)
  case 0 then show ?case using zeroth_ancestor by auto
next
  case (Suc n)
  obtain h3 where 1:"h3 \<leftarrow> h2" and 2:"nth_ancestor n h1 h3" using nth_ancestor_succ Suc.prems by (metis Suc_eq_plus1) 
  show ?case using Suc.hyps[OF 2] 1 hash_ancestor_intro' by blast 
qed

lemma safety: assumes "fork s" shows "one_third_slashed s"
proof -
  obtain h1 h2 q1 q2 v1 v2 where 1:"committed s q1 h1 v1" and 2:"committed s q2 h2 v2" 
    and 3:"\<not> (h2 \<leftarrow>\<^sup>* h1 \<or> h1 \<leftarrow>\<^sup>* h2 \<or> h1 = h2)" using assms fork_def by blast
  have 4:"\<not>(nth_ancestor n h1 h2 \<or> nth_ancestor n h2 h1 \<or> h1 = h2)" for n using l4 3 by auto
  obtain q3 q4 v3 v4 where 5:"prepared s q3 h1 v1 v3" and 6:"prepared s q4 h2 v2 v4" if "\<not>one_third_slashed s" using 1 2
    by (metis byz_quorums_axioms byz_quorums_def committed_def one_third_slashed_def slashed_1_def slashed_def)
  show ?thesis 
  proof (cases "v1 = v2")
    case True
    show ?thesis using 1 4 2 5 6 True casper_axioms unfolding byz_quorums_def casper_def  slashed_def
      one_third_slashed_def casper_axioms committed_def prepared_def slashed_1_def slashed_4_def
      by metis
  next
    case False thus ?thesis using l3 1 2 4 5 6 by (metis less_le not_less)
  qed
qed

end

end