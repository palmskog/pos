theory CasperOneMessage
  imports Main
begin

text {* This formalization is a modification of Casper.thy by Giuliano Losa. *}

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
  -- "vote_msg node hash view view_src"
  vote_msg :: "'n \<Rightarrow> 'h \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"

locale casper = byz_quorums +
  -- "Here we make assumptions about hashes. In reality any message containing a hash not satisfying those
should be dropped."
fixes 
  hash_parent :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "\<leftarrow>" 50)
fixes
  genesis :: 'h
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
lemma hash_ancestor_concat : "h2 \<leftarrow>\<^sup>* h3 \<Longrightarrow> h1 \<leftarrow>\<^sup>* h2 \<Longrightarrow> h1 \<leftarrow>\<^sup>* h3"
proof(induction rule: hash_ancestor.induct)
  case (1 h1 h2)
  then show ?case
  	using hash_ancestor_intro' by blast
next
  case (2 h1 h2 h3)
  then show ?case
  	using hash_ancestor_intro' by blast
qed

lemma hash_ancestor_other: "h1 \<leftarrow>\<^sup>* h2 \<Longrightarrow> \<not> p \<leftarrow>\<^sup>* h2 \<Longrightarrow> \<not> p \<leftarrow>\<^sup>* h1" 
	using hash_ancestor_concat by blast

inductive nth_ancestor :: "nat \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> bool" where 
  "nth_ancestor 0 h1 h1"
| "\<lbrakk>nth_ancestor n h1 h2; h2 \<leftarrow> h3\<rbrakk> \<Longrightarrow> nth_ancestor (n+1) h1 h3"
declare nth_ancestor.intros[simp,intro]
inductive_cases nth_ancestor_succ:"nth_ancestor (n+1) h1 h3"
inductive_cases zeroth_ancestor:"nth_ancestor 0 h1 h3"
lemma parent_ancestor:"h1 \<leftarrow> h2 = nth_ancestor 1 h1 h2"
  by (metis One_nat_def add.right_neutral add_Suc_right add_diff_cancel_left' diff_Suc_Suc nat.simps(3) nth_ancestor.simps)

text {* All messages in epoch @{term "0::nat"} are ignored;  @{term "0::nat"} is used as a special value (was @{term "-1::int"} in the original model). *}

definition justified_link
where
"justified_link s q parent pre new now \<equiv>
   (\<forall> n. n \<in>\<^sub>1 q \<longrightarrow> vote_msg s n new now pre) \<and> nth_ancestor (now - pre) parent new \<and> now > pre
"

lemma ancestor_means :
  "nth_ancestor n parent new \<Longrightarrow> n > 0 \<Longrightarrow> parent \<leftarrow>\<^sup>* new "
proof(induction rule: nth_ancestor.induct)
  case (1 h1)
  then show ?case	by simp
next
  case (2 n h1 h2 h3)
  then show ?case
  	by (metis casper.zeroth_ancestor casper_axioms hash_ancestor.intros(1) hash_ancestor_other neq0_conv)
qed

lemma justified_means_ancestor :
  "justified_link s q parent pre new now \<Longrightarrow> parent \<leftarrow>\<^sup>* new"
	by (meson casper.ancestor_means casper.justified_link_def casper_axioms zero_less_diff)

inductive justified where
  orig: "justified s genesis 0"
| follow: "\<lbrakk>justified s parent pre; justified_link s q parent pre new now\<rbrakk> \<Longrightarrow> justified s new now"

definition finalized where
  "finalized s q h v child \<equiv> (h \<leftarrow> child \<and> justified s h v \<and> justified_link s q h v child (v + 1))"

definition fork where 
  "fork s \<equiv> \<exists> h1 h2 q1 q2 v1 v2 c1 c2. finalized s q1 h1 v1 c1 \<and> finalized s q2 h2 v2 c2
    \<and> \<not>(h2 \<leftarrow>\<^sup>* h1 \<or> h1 \<leftarrow>\<^sup>* h2 \<or> h1 = h2)"

definition slashed_DBL_VOTE where
  "slashed_DBL_VOTE (s :: ('a, 'h, 'd) state_scheme) n \<equiv>
     \<exists> h1 h2 v s1 s2. vote_msg s n h1 v s1 \<and> vote_msg s n h2 v s2 \<and> (h1 \<noteq> h2 \<or> s1 \<noteq> s2)"

definition slashed_SURROUND where
  "slashed_SURROUND (s :: ('a, 'h, 'd) state_scheme) n \<equiv>
    \<exists> h1 h2 v1 v2 s1 s2. vote_msg s n h1 v1 s1 \<and> vote_msg s n h2 v2 s2 \<and> v1 > v2 \<and> s2 > s1"

definition slashed where "slashed s n \<equiv> 
  slashed_DBL_VOTE s n \<or> slashed_SURROUND s n"
definition one_third_slashed where "one_third_slashed s \<equiv> \<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed s n"

lemmas slashed_defs = slashed_def slashed_DBL_VOTE_def slashed_SURROUND_def one_third_slashed_def
lemmas order_defs = class.linorder_axioms_def class.linorder_def class.order_def class.preorder_def 
  class.order_axioms_def class.order_bot_def class.order_bot_axioms_def linorder_axioms[where ?'a=nat]
lemmas casper_defs = slashed_defs vote_msg_def fork_def casper_assms_def

lemma l0: assumes "justified_link s q1 h2 v2 h1 v1"
  shows "v1 > v2"
using assms justified_link_def by blast

lemma l02: assumes "justified_link s q1 h2 v2 h1 (v3 + 1)" and "finalized s q2 h3 v3 c3"
          and "\<not> h3 \<leftarrow>\<^sup>* h1" and "v2 < v3"
          shows "\<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed_DBL_VOTE s n"
using assms proof(simp)
  have "\<forall> n. n \<in>\<^sub>1 q1 \<longrightarrow> vote_msg s n h1 (v3 + 1) v2"
    by (meson assms(1) casper.justified_link_def casper_axioms)
  moreover have "\<forall> n. n \<in>\<^sub>1 q2 \<longrightarrow> vote_msg s n c3 (v3 + 1) v3"
    by (meson assms(2) casper.justified_link_def casper_axioms finalized_def)
  moreover have "\<exists> q. \<forall> n. n \<in>\<^sub>2 q \<longrightarrow> n \<in>\<^sub>1 q1 \<and> n \<in>\<^sub>1 q2"
    using byz_quorums_axioms byz_quorums_def by fastforce
  ultimately have "\<exists> q. \<forall> n. n \<in>\<^sub>2 q \<longrightarrow> vote_msg s n h1 (v3 + 1) v2 \<and> vote_msg s n c3 (v3 + 1) v3 "
    by blast
  then show ?thesis
    by (metis assms(4) less_not_refl3 slashed_DBL_VOTE_def)
qed

lemma l01: assumes "justified_link s q1 h2 v2 h1 (v3 + 1)" and "finalized s q2 h3 v3 c3"
          and "\<not> h3 \<leftarrow>\<^sup>* h1" and "v2 < v3"
          shows "one_third_slashed s"
using assms proof(simp)
  have "\<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed_DBL_VOTE s n"
   by (meson assms(1) assms(2) assms(3) assms(4) casper.l02 casper_axioms)
  then show ?thesis
   by (meson casper.casper_defs(1) casper.casper_defs(4) casper_axioms)
qed

lemma l04: assumes "justified_link s q1 h2 v2 h1 v1" and "finalized s q2 h3 v3 c3" and "v3 + 1 < v1"
          and "\<not> h3 \<leftarrow>\<^sup>* h1" and "v2 < v3"
          shows "\<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed_SURROUND s n"
using assms proof(simp)
  have "\<forall> n. n \<in>\<^sub>1 q1 \<longrightarrow> vote_msg s n h1 v1 v2"
    by (meson assms(1) casper.justified_link_def casper_axioms)
  moreover have "\<forall> n. n \<in>\<^sub>1 q2 \<longrightarrow> vote_msg s n c3 (v3 + 1) v3"
    by (metis assms(2) casper.finalized_def casper.justified_link_def casper_axioms)
  moreover have "\<exists> q. \<forall> n. n \<in>\<^sub>2 q \<longrightarrow> n \<in>\<^sub>1 q1 \<and> n \<in>\<^sub>1 q2"
    using byz_quorums_axioms byz_quorums_def by fastforce
  ultimately have "\<exists> q. \<forall> n. n \<in>\<^sub>2 q \<longrightarrow> (vote_msg s n h1 v1 v2 \<and> vote_msg s n c3 (v3 + 1) v3)"
    by blast
  moreover have "\<forall> n. (vote_msg s n h1 v1 v2 \<and> vote_msg s n c3 (v3 + 1) v3) \<longrightarrow> slashed_SURROUND s n"
    using assms(3) assms(5) slashed_SURROUND_def by blast
  ultimately show ?thesis
    by blast
qed

lemma l03: assumes "justified_link s q1 h2 v2 h1 v1" and "finalized s q2 h3 v3 c3" and "v1 > v3 + 1"
          and "\<not> h3 \<leftarrow>\<^sup>* h1" and "v2 < v3"
        shows "one_third_slashed s"
using assms proof(simp)
  have "\<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed_SURROUND s n"
    using assms(1) assms(2) assms(3) assms(4) assms(5) l04 by blast
  then show ?thesis
    by (meson casper.casper_defs(1) casper.casper_defs(4) casper_axioms)
qed


lemma l00: assumes "justified_link s q1 h2 v2 h1 v1" and "finalized s q2 h3 v3 c3" and "v1 > v3"
          and "\<not> h3 \<leftarrow>\<^sup>* h1" and "v2 < v3"
          shows "one_third_slashed s"
proof (cases "v1 = v3 + 1")
  case True
  then show ?thesis using assms l01 by blast
next
  case False
  then have "v1 > v3 + 1"
    using assms(3) by linarith
  then show ?thesis
    using assms(1) assms(2) assms(4) assms(5) l03 by blast
qed

lemma l5sub:
"(\<forall> n. n \<in>\<^sub>2 q2 \<longrightarrow> vote_msg s n new now pre \<and> vote_msg s n h1 v1 pre1) \<Longrightarrow>
 now = v1 \<Longrightarrow>
 h1 \<noteq> new \<Longrightarrow>
 \<forall> n. n \<in>\<^sub>2 q2 \<longrightarrow> slashed_DBL_VOTE s n"
proof
  assume reg: "\<forall> n. n \<in>\<^sub>2 q2 \<longrightarrow> vote_msg s n new now pre \<and> vote_msg s n h1 v1 pre1"
  assume diff: "h1 \<noteq> new"
  assume same: "now = v1"
  fix n
  show "n \<in>\<^sub>2 q2 \<longrightarrow> slashed_DBL_VOTE s n" proof
   assume i: "n \<in>\<^sub>2 q2"
   then have "vote_msg s n new now pre" by (simp add: reg)
   moreover have "vote_msg s n h1 v1 pre1" by (simp add: i reg)
   ultimately show "slashed_DBL_VOTE s n"
   	 using diff same slashed_DBL_VOTE_def by blast
 qed
qed

lemma l5'' :
"justified_link s q parent pre new now \<Longrightarrow>
 justified_link s q1 parent1 pre1 h1 v1 \<Longrightarrow>  \<not> one_third_slashed s \<Longrightarrow>
 now = v1 \<Longrightarrow>
 h1 = new"
proof -
 assume a1: "justified_link s q parent pre new now"
 assume a2: "justified_link s q1 parent1 pre1 h1 v1"
 have "\<exists> q2. \<forall> n. n \<in>\<^sub>2 q2 \<longrightarrow> n \<in>\<^sub>1 q \<and> n \<in>\<^sub>1 q1"
    using byz_quorums_axioms byz_quorums_def by fastforce
 then obtain q2 where q2good: "\<forall> n. n \<in>\<^sub>2 q2 \<longrightarrow> n \<in>\<^sub>1 q \<and> n \<in>\<^sub>1 q1" by blast
  have vv: "\<forall> n. n \<in>\<^sub>2 q2 \<longrightarrow> vote_msg s n new now pre \<and> vote_msg s n h1 v1 pre1"
    by (meson a1 a2 casper.justified_link_def casper_axioms q2good)
 assume a3: "\<not> one_third_slashed s"
 assume a4: "now = v1"
 show ?thesis
   proof(cases "h1 = new")
 	 case True
 	 then show ?thesis by simp
 next
 	 case False
   have "\<forall> n. n \<in>\<^sub>2 q2 \<longrightarrow> slashed_DBL_VOTE s n" using vv False a4 l5sub by blast
   then have "one_third_slashed s"
	 by (meson casper.casper_defs(1) casper.casper_defs(4) casper_axioms)
 	 then show ?thesis using a3 by auto
 qed
qed

lemma l5':
  "justified s h2 v2 \<Longrightarrow>
  justified s h1 v1 \<Longrightarrow>
  \<not> one_third_slashed s \<Longrightarrow>
  h1 \<noteq> h2 \<Longrightarrow>
  v2 \<noteq> v1"
  by (metis justified.cases l0 l5'' not_less0)

lemma l5:
  assumes "finalized s q2 h2 v2 xa"
  and "\<not> one_third_slashed s"
  and "justified s parent pre"
  and "parent \<noteq> h2"
  shows "v2 \<noteq> pre"
using assms(1) assms(2) assms(3) assms(4) casper.finalized_def casper_axioms l5' by fastforce

lemma non_equal_case_ind:
 assumes "justified s h1 v1"
 assumes "finalized s q2 h2 v2 xa"
 assumes "\<not> h2 \<leftarrow>\<^sup>* h1"
 assumes "h1 \<noteq> h2"
 assumes "v1 > v2"
 shows "one_third_slashed s"
using assms proof (induct "v1 - v2" arbitrary: h1 v1 rule:less_induct)
  case less
    have "(h1 = genesis \<and> v1 = 0) \<or>
            (\<exists> q parent pre. justified s parent pre \<and> justified_link s q parent pre h1 v1)"
         (is "?caseL \<or> ?caseR")
      using justified.simps less.prems(1) by blast
    moreover have "?caseL \<longrightarrow> ?thesis" using assms
      using less.prems(5) by blast
    moreover have "?caseR \<Longrightarrow> ?thesis" using assms proof(cases "one_third_slashed s")
    	case True
    	then show ?thesis	by simp
    next
    	case False
      have sanity: "\<not> one_third_slashed s"	by (simp add: False)
      assume "\<exists>q parent pre. justified s parent pre \<and> justified_link s q parent pre h1 v1"
      then obtain q1 parent pre where link: "justified s parent pre \<and> justified_link s q1 parent pre h1 v1" by blast
    	show ?thesis
    	  by (metis (mono_tags, lifting) casper.justified_means_ancestor casper.l00 casper_axioms diff_less_mono hash_ancestor_concat l0 l5 less.hyps less.prems(2) less.prems(3) less.prems(5) link linorder_neqE_nat not_le_imp_less)
    qed
    moreover have "?caseR \<longrightarrow> ?thesis"
    	by (simp add: calculation(3))
    ultimately show ?thesis by blast
qed

lemma non_equal_case:
 assumes "finalized s q1 h1 v1 x"
 assumes "finalized s q2 h2 v2 xa"
 assumes "\<not> h2 \<leftarrow>\<^sup>* h1"
 assumes "h1 \<noteq> h2"
 assumes "v1 > v2"
 shows "one_third_slashed s"
by (metis assms casper.finalized_def casper.non_equal_case_ind casper_axioms)

lemma equal_case:
  assumes "finalized s q1 h1 v1 x"
  assumes "finalized s q2 h2 v1 xa"
  assumes "h1 \<noteq> h2"
  shows "one_third_slashed s"
using assms proof(simp add: finalized_def)
  have "\<forall> n. n \<in>\<^sub>1 q1 \<longrightarrow> vote_msg s n x (v1 + 1) v1"
    by (metis assms(1) casper.finalized_def casper.justified_link_def casper_axioms)
  moreover have "\<forall> n. n \<in>\<^sub>1 q2 \<longrightarrow> vote_msg s n xa (v1 + 1) v1"
    using assms(2) finalized_def justified_link_def by blast
  moreover have "\<exists> q. \<forall> n. n \<in>\<^sub>2 q \<longrightarrow> n \<in>\<^sub>1 q1 \<and> n \<in>\<^sub>1 q2"
    using byz_quorums_axioms byz_quorums_def by fastforce
  ultimately have "\<exists> q. \<forall> n. n\<in>\<^sub>2 q \<longrightarrow> vote_msg s n x (v1 + 1) v1 \<and> vote_msg s n xa (v1 + 1) v1"
    by blast
  moreover have "x \<noteq> xa"
    by (metis assms(1) assms(2) assms(3) casper.axioms(2) casper.finalized_def casper_assms_def(2) casper_axioms)
  moreover have "\<forall> n. vote_msg s n x (v1 + 1) v1 \<and> vote_msg s n xa (v1 + 1) v1 \<longrightarrow> slashed_DBL_VOTE s n"
    using calculation(2) slashed_DBL_VOTE_def by blast
  then have  "\<exists> q. \<forall> n. n \<in>\<^sub>2 q \<longrightarrow> slashed_DBL_VOTE s n"
    using calculation(1) by blast
  then show ?thesis
    by (meson casper.casper_defs(1) casper.casper_defs(4) casper_axioms)
qed

lemma safety':
 assumes "finalized s q1 h1 v1 x"
 assumes "finalized s q2 h2 v2 xa"
 assumes "\<not> h2 \<leftarrow>\<^sup>* h1"
 assumes "\<not> h1 \<leftarrow>\<^sup>* h2"
 assumes "h1 \<noteq> h2"
 shows "one_third_slashed s"
proof (cases "v1 = v2")
  case True
  then show ?thesis
    using assms equal_case by auto
next
  case False
  then show ?thesis
    by (metis assms linorder_neqE_nat non_equal_case)
qed

lemma safety: assumes "fork s" shows "one_third_slashed s"
using assms fork_def safety' by blast

end

end
