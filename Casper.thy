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
  -- "@{typ 'n} is the type of validators (nodes), @{typ 'h} hashes, and @{typ 'v} views"
  commit_msg :: "'n \<Rightarrow> 'h \<Rightarrow> 'v \<Rightarrow> bool"
  prepare_msg :: "'n \<Rightarrow> 'h \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"

locale casper = byz_quorums +
  views:linorder view_less_eq view_less + 
  order_bot  bot view_less_eq view_less for
  view_less_eq :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "\<le>\<^sub>v" 50)
  and view_less :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "<\<^sub>v" 50)
  and bot::"'v" ("\<bottom>") +
fixes 
  hash_pred :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "\<leftarrow>" 50)
assumes
  -- "a hash has at most one predecessor which is not itself"
  "\<And> h1 h2 . h1 \<leftarrow> h2 \<Longrightarrow> h1 \<noteq> h2"
  and "\<And> h1 h2 h3 . \<lbrakk>h2 \<leftarrow> h1; h3 \<leftarrow> h1\<rbrakk> \<Longrightarrow> h2 = h3"
begin

inductive hash_ancestor (infix "\<leftarrow>\<^sup>*" 50) where 
  "h1 \<leftarrow> h2 \<Longrightarrow> h1 \<leftarrow>\<^sup>* h2"
| "\<lbrakk>h1 \<leftarrow>\<^sup>* h2; h2 \<leftarrow>\<^sup>* h3\<rbrakk> \<Longrightarrow> h1 \<leftarrow>\<^sup>* h3"

lemmas casper_assms_def = casper_def class.linorder_def class.order_def
    class.preorder_def class.order_axioms_def class.linorder_axioms_def byz_quorums_def
    class.order_bot_def class.order_bot_axioms_def

text {* All messages in epoch @{term \<bottom>} are ignored;  @{term \<bottom>} is used as a special value. *}

definition prepared where 
  "prepared s q h v1 v2 \<equiv> v1 \<noteq> \<bottom> \<and> (\<forall> n . n \<in>\<^sub>1 q \<longrightarrow> prepare_msg s n h v1 v2)"
definition committed where
  "committed s q h v \<equiv> v \<noteq> bot \<and> (\<forall> n . n \<in>\<^sub>1 q \<longrightarrow> commit_msg s n h v)"
definition fork where 
  "fork s \<equiv> \<exists> h1 h2 q1 q2 v1 v2 . committed s q1 h1 v1 \<and> committed s q2 h2 v2
    \<and> \<not>(h2 \<leftarrow>\<^sup>* h1 \<or> h1 \<leftarrow>\<^sup>* h2 \<or> h1 = h2)"

definition slashed_1 where  "slashed_1 s n \<equiv> 
  \<exists> h v . commit_msg s n h v \<and> (\<forall> q v2 . v2 <\<^sub>v v \<longrightarrow> \<not>prepared s q h v v2)"
definition slashed_2 where
  -- "this is not exactly what Vitalik wrote."
  "slashed_2 s n \<equiv>
  \<exists> h v1 v2 . prepare_msg s n h v1 v2 \<and> v2 \<noteq> \<bottom> \<and>
    (\<forall> v3 q h2 . v3 <\<^sub>v v2 \<longrightarrow> \<not>(h2 \<leftarrow> h \<and> prepared s q h2 v2 v3))"
definition slashed_3 where 
  "slashed_3 s n \<equiv>
  \<exists> h1 h2 v1 v2 v3 . v1 <\<^sub>v v2 \<and> v3 <\<^sub>v v1 \<and> 
    commit_msg s n h1 v1 \<and> prepare_msg s n h2 v2 v3"
definition slashed_4 where
  "slashed_4 s n \<equiv> \<exists> h1 h2 v v1 v2 . (h1 \<noteq> h2 \<or> v1 \<noteq> v2) \<and> 
    prepare_msg s n h1 v v1 \<and> prepare_msg s n h2 v v2"

definition slashed where "slashed s n \<equiv> 
  slashed_1 s n \<or> slashed_2 s n \<or> slashed_3 s n \<or>  slashed_4 s n"

lemma assumes "fork s"
  shows "\<exists> q . \<forall> n . n \<in>\<^sub>2 q \<longrightarrow> slashed s n"
  using [[]]
  nitpick[verbose, card 'b=2, card 'c=2, card 'a=5, card 'v=8, card 'h=7, card 'd=1,
      card "('a, 'h, 'v, 'd) state_scheme" = 1, dont_box, timeout=300] (*,
      eval="(slashed s, committed s)"] *)
  using assms casper_axioms
  apply -
  unfolding slashed_def slashed_1_def slashed_2_def slashed_4_def slashed_3_def
      prepared_def fork_def committed_def slashed_2a_def
  apply (cases s)
  apply simp
  unfolding casper_assms_def
  apply (simp (no_asm_use))
  apply (match premises in P[thin]:"?x = ?y" \<Rightarrow> \<open>-\<close>)
  apply clarify
  oops
  using [[smt_timeout=3000,smt_oracle=true,smt_random_seed=456363655542,smt_certificates="./casper.cert"]]
  sledgehammer[timeout=5000, provers=z3 spass]()


end