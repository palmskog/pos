theory Casper
imports Main
begin

locale byz_quorums =
  fixes member_1 :: "'n \<Rightarrow> 'q1 \<Rightarrow> bool" (* membership in 2/3 set *)
    and member_2 :: "'n \<Rightarrow> 'q2 \<Rightarrow> bool" (* membership in 1/3 set *)
  assumes "\<And> q1 q2 . \<exists> q3 . \<forall> n . member_2 n q3 \<longrightarrow> member_1 n q1 \<and> member_1 n q2" (* 2/3 quorums have 1/3 intersection *)
    and "\<And> q1 q2 . \<exists> n . member_2 n q1 \<and> member_1 n q2" (* 2/3 sets and 1/3 sets intersect *)

record ('n,'h,'v)state =
  -- "@{typ 'n} is the type of validators (nodes), @{typ 'h} hashes, and @{typ 'v} views"
  commit_msg :: "'n \<Rightarrow> 'h \<Rightarrow> 'v \<Rightarrow> bool"
  prepare_msg :: "'n \<Rightarrow> 'h \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"

locale casper = byz_quorums + 
  hashes:order hash_less_eq hash_less + 
  views:linorder view_less_eq view_less + 
  order_bot bot for
  hash_less_eq :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "\<le>\<^sub>h" 50)
  and hash_less :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "<\<^sub>h" 50)
  and view_less_eq :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "\<le>\<^sub>v" 50)
  and view_less :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "<\<^sub>v" 50)
  and bot::"'v" ("\<bottom>") +
assumes "\<And> h1 h2 . \<lbrakk>h1 \<le>\<^sub>h h; h2 \<le>\<^sub>h h\<rbrakk> \<Longrightarrow> h1 \<le>\<^sub>h h2 \<or> h2 \<le>\<^sub>h h1"
  -- "a hash has a unique parent"
begin

lemmas casper_assms = casper_axioms casper_def class.linorder_def class.order_def
    class.preorder_def class.order_axioms_def class.linorder_axioms_def byz_quorums_def

definition is_pred where "is_pred h1 h2 \<equiv> h1 <\<^sub>h h2 \<and> (\<forall> h . \<not> (h1 <\<^sub>h h \<and> h <\<^sub>h h2))"

definition prepared where 
  "prepared s q h v1 v2 \<equiv> \<forall> n . member_1 n q \<longrightarrow> prepare_msg s n h v1 v2"
definition committed where
  "committed s q h v \<equiv> \<forall> n . member_1 n q \<longrightarrow> commit_msg s n h v"
definition fork where 
  "fork s \<equiv> \<exists> h1 h2 q1 q2 v1 v2 . committed s q1 h1 v1 \<and> committed s q2 h2 v2
    \<and> \<not>(h2 \<le>\<^sub>h h1 \<or> h1 \<le>\<^sub>h h2)"

definition slashed_1 where  "slashed_1 s n \<equiv> 
  \<exists> h v . commit_msg s n h v \<and> (\<forall> q v2 . v2 \<le>\<^sub>v v \<longrightarrow> \<not>prepared s q h v v2)"
definition slashed_2 where "slashed_2 s n \<equiv>
  \<exists> h v1 v2 . prepare_msg s n h v1 v2 \<and> v2 \<noteq> \<bottom> \<and>
    (\<forall> v3 q h2 . v3 \<le>\<^sub>v v2 \<longrightarrow> \<not>(prepared s q h2 v2 v3 \<and> is_pred h2 h))"
definition slashed_3 where "slashed_3 s n \<equiv>
  \<exists> h1 h2 v1 v2 v3 . v1 <\<^sub>v v2 \<and> v3 <\<^sub>v v1 \<and> 
    commit_msg s n h1 v1 \<and> prepare_msg s n h2 v2 v3"
definition slashed_4 where "slashed_4 s n \<equiv>
  \<exists> h1 h2 v v1 v2 . (h1 \<noteq> h2 \<or> v1 \<noteq> v2) \<and> 
    prepare_msg s n h1 v v1 \<and> prepare_msg s n h2 v v2"
definition slashed where "slashed s n \<equiv> 
  slashed_1 s n \<or> slashed_2 s n \<or> slashed_3 s n \<or> slashed_4 s n"

lemma assumes "fork s" 
  shows "\<exists> q . \<forall> n . member_2 n q \<longrightarrow> slashed s n"
  using [[show_types]]
  nitpick[verbose, card 'b=2, card 'c=2, card 'a=5, card 'v=2, card 'h=3, card 'd=1,
      card "('a, 'h, 'v, 'd) state_scheme" = 1, dont_box]

end

end


end