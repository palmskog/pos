(*
Copyright 2017 Yoichi Hirai

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

theory DynamicValidatorSetOneMessage

imports Main

begin

(* many things are copied and adjusted from @nano-o's contribution. *)

locale byz_quorums =
  -- "Here we fix two types @{typ 'q1} and @{typ 'q2} for quorums and one type @{typ 'v} for
      validator sets. of cardinality greater than 2/3 of 
the validators and quorum of cardinality greater than 1/3 of the validators."
  fixes member_1 :: "'n \<Rightarrow> 'q1 \<Rightarrow> 'v \<Rightarrow> bool" ("_ \<in>\<^sub>1 _ of _" 50)
    -- "Membership in 2/3 set"
    and member_2 :: "'n \<Rightarrow> 'q2 \<Rightarrow> 'v \<Rightarrow> bool" ("_ \<in>\<^sub>2 _ of _" 50)
    -- "Membership in 1/3 set"
  fixes
    hash_parent :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "\<leftarrow>" 50)
  fixes
    genesis :: 'h
  fixes
    vset_fwd :: "'h \<Rightarrow> 'v"
  fixes
    vset_bwd :: "'h \<Rightarrow> 'v"
  fixes
    vset_chosen :: "'h \<Rightarrow> 'v"
    -- "the next set chosen in the dynasity: https://ethresear.ch/t/casper-ffg-with-one-message-type-and-simpler-fork-choice-rule/103/34"
  assumes
  -- "Here we make assumptions about hashes. In reality any message containing a hash not satisfying those
should be dropped."
  -- "a hash has at most one parent which is not itself"
  "\<And> h1 h2 . h1 \<leftarrow> h2 \<Longrightarrow> h1 \<noteq> h2"
  and "\<And> h1 h2 h3 . \<lbrakk>h2 \<leftarrow> h1; h3 \<leftarrow> h1\<rbrakk> \<Longrightarrow> h2 = h3"
  and "\<And> q1 q2 vs. \<exists> q3 . \<forall> n . (n \<in>\<^sub>2 q3 of vs) \<longrightarrow> (n \<in>\<^sub>1 q1 of vs) \<and> (n \<in>\<^sub>1 q2 of vs)"  

    -- "This is the only property of types @{typ 'q1} and @{typ 'q2} that we need:
2/3 quorums have 1/3 intersection"

(* how do we get the forward and the backward validator set? *)
record ('n,'h)state =
  -- "@{typ 'n} is the type of validators (nodes), @{typ 'h} hashes, and views are @{typ nat}"
  -- "vote_msg node hash view view_src"
  vote_msg :: "'n \<Rightarrow> 'h \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"


locale casper = byz_quorums
begin

lemma hoge:
  "\<exists> q.  \<forall> n.  (n \<in>\<^sub>2 q of (vset_fwd root)) \<longrightarrow> ((n \<in>\<^sub>1 q0 of (vset_fwd root)) \<and> (n \<in>\<^sub>1 q1 of (vset_fwd root)))"
  using byz_quorums_axioms byz_quorums_def by force

inductive nth_parent where
  zeroth_parent: "nth_parent (0 :: nat) h h"
| Sth_parent: "nth_parent n oldest mid \<Longrightarrow> mid \<leftarrow> newest \<Longrightarrow> nth_parent (Suc n) oldest newest"

definition voted_by where
  "voted_by s q vset orig v2 h v1 \<equiv>
     v1 \<noteq> 0 \<and> v2 < v1 \<and> nth_parent (v1 - v2) orig h \<and>
     (\<forall> n. (n \<in>\<^sub>1 q of vset) \<longrightarrow> vote_msg s n h v1 v2)"

(* the forward set and the backward set must be taken from orig, not from h.
 * Otherwise, there is a forking situation.
 *)
definition voted_by_fwd where
  "voted_by_fwd s q orig v2 h v1 \<equiv>
     voted_by s q (vset_fwd h) orig v2 h v1"

definition voted_by_bwd where
  "voted_by_bwd s q orig v2 h v1 \<equiv>
     voted_by s q (vset_bwd h) orig v2 h v1"

definition voted_by_both where
  "voted_by_both s q0 q1 orig v2 h v1 \<equiv> voted_by_fwd s q0 orig v2 h v1 \<and> voted_by_bwd s q1 orig v2 h v1"

inductive hash_ancestor (infix "\<leftarrow>\<^sup>*" 50) where
  "h1 \<leftarrow> h2 \<Longrightarrow> h1 \<leftarrow>\<^sup>* h2"
| "\<lbrakk>h1 \<leftarrow> h2; h2 \<leftarrow>\<^sup>* h3\<rbrakk> \<Longrightarrow> h1 \<leftarrow>\<^sup>* h3"
declare hash_ancestor.intros[simp,intro]
lemma hash_ancestor_intro': assumes "h1 \<leftarrow>\<^sup>* h2" and "h2 \<leftarrow> h3" shows "h1 \<leftarrow>\<^sup>* h3" 
  using assms by (induct h1 h2 rule:hash_ancestor.induct) auto

lemma hash_ancestor_trans: assumes "h1 \<leftarrow>\<^sup>* h2" and "h2 \<leftarrow>\<^sup>* h3" shows "h1 \<leftarrow>\<^sup>* h3" 
  using assms by (induct h1 h2 rule:hash_ancestor.induct) auto

definition validator_changing_link where
"validator_changing_link s q0 q1 orig origE new newE \<equiv>
   voted_by_both s q0 q1 orig origE new newE \<and>
   vset_bwd new = vset_fwd orig \<and> vset_fwd new = vset_chosen orig"

definition usual_link where
"usual_link s q0 q1 orig origE new newE \<equiv>
   voted_by_both s q0 q1 orig origE new newE \<and>
   vset_bwd orig = vset_bwd new \<and> vset_fwd orig = vset_fwd new"

datatype Mode = Usual | FinalizingChild

inductive justified_with_root where
  justified_genesis: "r = r' \<Longrightarrow> rE = rE' \<Longrightarrow> justified_with_root r rE mode s r' rE' mode"
| usual_justification:
    "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new newE \<Longrightarrow>
     newM = (if newE - origE = 1 then FinalizingChild else Usual) \<Longrightarrow>
     justified_with_root r rE mode s new newE newM"
| justified_on_finalization:
   "justified_with_root r rE mode s c e FinalizingChild \<Longrightarrow>
    validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
    newM = (if ee - e = 1 then FinalizingChild else Usual) \<Longrightarrow>
    justified_with_root r rE mode s h ee newM"

inductive finalized_with_root where
  under_usual_link:
    "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new (origE + 1) \<Longrightarrow>
     finalized_with_root r rE mode s orig new origE Usual"
  | under_changing_link:
    "justified_with_root r rE mode s c e FinalizingChild \<Longrightarrow>
     validator_changing_link s q0 q1 c e h (e + 1) \<Longrightarrow>
     finalized_with_root r rE mode s c h e FinalizingChild"

abbreviation justified where
  "justified s h v m \<equiv> justified_with_root genesis 0 Usual s h v m"

definition fork where
  "fork s h0 v0 m0 h1 v1 m1 \<equiv> \<exists> child0 child1.
    (finalized_with_root genesis 0 Usual s h0 child0 v0 m0 \<and> finalized_with_root genesis 0 Usual s h1 child1 v1 m1 \<and>
     \<not>(h1 \<leftarrow>\<^sup>* h0 \<or> h0 \<leftarrow>\<^sup>* h1 \<or> h0 = h1))"

definition slashed_dbl where "slashed_dbl s n \<equiv>
  \<exists> h0 h1 v v0 v1. (h0 \<noteq> h1 \<or> v0 \<noteq> v1) \<and> vote_msg s n h0 v v0 \<and> vote_msg s n h1 v v1"
(* source difference needs to be punished as well, for
 * https://ethresear.ch/t/casper-ffg-with-one-message-type-and-simpler-fork-choice-rule/103/41?u=yhirai *)

definition slashed_surround where "slashed_surround s n \<equiv>
  \<exists> h0 h1 v0 v1 vs0 vs1. vs0 < vs1 \<and> vs1 < v1 \<and> v1 < v0
          \<and> vote_msg s n h0 v0 vs0 \<and> vote_msg s n h1 v1 vs1"

definition slashed where "slashed s n \<equiv> 
  slashed_dbl s n \<or> slashed_surround s n"

definition one_third_of_fwd_slashed where
"one_third_of_fwd_slashed s h q \<equiv>
  \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd h)) \<longrightarrow> slashed s n"

definition one_third_of_bwd_slashed where
"one_third_of_bwd_slashed s h q \<equiv>
  \<forall> n. (n \<in>\<^sub>2 q of (vset_bwd h)) \<longrightarrow> slashed s n"

definition one_third_of_fwd_or_bwd_slashed where
"one_third_of_fwd_or_bwd_slashed s h q \<equiv>
   one_third_of_fwd_slashed s h q \<or> one_third_of_bwd_slashed s h q"


(**** intermediate stuff ends ****)

inductive justified_with_root_with_n_switchings where
  justified_genesis_n: "r = r' \<Longrightarrow> rE = rE' \<Longrightarrow> mode = mode' \<Longrightarrow>
     n = (0 :: nat) \<Longrightarrow>
     justified_with_root_with_n_switchings n r rE mode s r' rE' mode'"
| usual_justification_n:
    "justified_with_root_with_n_switchings n r rE mode s orig origE origM \<Longrightarrow>
     origM = Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new newE \<Longrightarrow>
     newM = (if newE - origE = 1 then FinalizingChild else Usual) \<Longrightarrow>
     justified_with_root_with_n_switchings n r rE mode s new newE newM"
| justified_on_finalization_n:
   "justified_with_root_with_n_switchings n r rE mode s c e origM \<Longrightarrow>
    origM = FinalizingChild \<Longrightarrow>
    validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
    newM = (if ee - e = 1 then FinalizingChild else Usual) \<Longrightarrow>
(*    newN = Suc n \<Longrightarrow> *)
    justified_with_root_with_n_switchings (Suc n) r rE mode s h ee newM"

lemma forget_n_switchings:
"justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
 justified_with_root r rE rM s h v m"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' s)
  then show ?case
    by (simp add: justified_genesis)
next
  case (usual_justification_n n r rE mode s orig origE q0 q1 new newE newM)
  then show ?case
    using casper.usual_justification casper_axioms by fastforce
next
  case (justified_on_finalization_n n r rE mode s c e q0 q1 h ee newM)
  then show ?case
    using casper.justified_on_finalization casper_axioms by fastforce
qed

lemma voted_by_higher:
  "voted_by s q vset orig v2 h v1 \<Longrightarrow>
   v2 < v1"
  by (simp add: voted_by_def)

lemma voted_by_fwd_higher:
  "voted_by_fwd s q orig v2 h v1 \<Longrightarrow>
   v2 < v1"
  by (simp add: voted_by_fwd_def voted_by_higher)

lemma voted_by_both_higher:
  "voted_by_both s q0 q1 orig v2 h v1 \<Longrightarrow>
   v2 < v1"
  using voted_by_both_def voted_by_fwd_higher by blast

lemma usual_link_higher:
  "usual_link s q0 q1 orig origE new newE \<Longrightarrow>
   origE < newE"
  using usual_link_def voted_by_both_higher by blast

lemma validator_changing_link_higher:
    "validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
     e < ee"
  using validator_changing_link_def voted_by_both_higher by blast

lemma voted_by_fwd_means_ancestor :
  "voted_by_fwd s q orig v2 h v1 \<Longrightarrow>
   nth_parent (v1 - v2) orig h"
  by (simp add: voted_by_def voted_by_fwd_def)

lemma voted_by_both_means_ancestor:
  "voted_by_both s q0 q1 orig v2 h v1 \<Longrightarrow>
  nth_parent (v1 - v2) orig h"
  using voted_by_both_def voted_by_fwd_means_ancestor by blast

lemma validator_changing_link_means_ancestor:
   "validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
    nth_parent (ee - e) c h"
  using validator_changing_link_def voted_by_both_means_ancestor by blast

lemma justifies_higher:
  "justified_with_root r rE rM s h v m \<Longrightarrow>
   rE \<le> v"
proof(induct rule: justified_with_root.induct)
  case (justified_genesis r rE s)
  then show ?case by simp
next
  case (usual_justification r rE s orig origE q0 q1 new newE)
  then show ?case
    by (meson casper.usual_link_higher casper_axioms leD leI order.strict_trans)
next
  case (justified_on_finalization r rE s c e q0 q1 h ee)
  then show ?case
    by (meson leD leI less_trans validator_changing_link_higher)
qed

lemma justified_with_root_refl:
  "justified_with_root h v m s h v m"
  by (simp add: justified_genesis)

lemma justified_with_root_trans:
   "justified_with_root h1 v1 m1 s h2 v2 m2 \<Longrightarrow>
    justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
    justified_with_root h0 v0 m0 s h2 v2 m2"
proof(induct rule: justified_with_root.inducts)
  case (justified_genesis r r' rE rE' s)
  then show ?case by blast
next
  case (usual_justification r rE s orig origE q0 q1 new newE)
  then show ?case
    using justified_with_root.usual_justification by blast
next
  case (justified_on_finalization r rE s c e q0 q1 h ee)
  then show ?case
    using casper.justified_on_finalization casper_axioms by fastforce
qed


inductive finalized_with_root_with_n_switchings where
  under_usual_link_n:
    "justified_with_root_with_n_switchings n r rE mode s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new (origE + 1) \<Longrightarrow>
     finalized_with_root_with_n_switchings n r rE mode s orig new origE Usual"
  | under_changing_link_n:
    "justified_with_root_with_n_switchings n r rE mode s c e FinalizingChild \<Longrightarrow>
     validator_changing_link s q0 q1 c e h (e + 1) \<Longrightarrow>
     finalized_with_root_with_n_switchings n r rE mode s c h e FinalizingChild"

lemma fjn:
  "finalized_with_root_with_n_switchings n r rE rM s h child v m \<Longrightarrow>
   justified_with_root_with_n_switchings n r rE rM s h v m"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    by linarith
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    by simp
qed


lemma refl_inv:
 "justified_with_root_with_n_switchings n r rE mode s c e origM \<Longrightarrow>
  rE = e \<Longrightarrow>
  origM = mode"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case  by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case by (metis casper.justifies_higher casper_axioms diff_is_0_eq' forget_n_switchings less_numeral_extra(3) usual_link_higher zero_less_diff)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (metis casper.justifies_higher casper_axioms diff_is_0_eq' forget_n_switchings less_numeral_extra(3) validator_changing_link_higher zero_less_diff)
qed

lemma zero_justification_f:
  "justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
   n = 0 \<Longrightarrow>
   rM = FinalizingChild \<Longrightarrow>
   rE = v"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then have "rE = origE" by blast
  then show ?case
    using casper.refl_inv casper_axioms usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.prems(2) by fastforce
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case by blast
qed


definition close_finalization where
  "close_finalization s r rE rM h v m \<equiv>
  (rE + 1 < v \<longrightarrow> m = Usual) \<and>
   ((\<exists> child.
    finalized_with_root_with_n_switchings (0 :: nat) r rE rM s h child v m) \<or>
  (\<exists> child. finalized_with_root_with_n_switchings (1 :: nat) r rE rM s h child v m) \<and> rE < v \<and> (rE + 1 = v \<longrightarrow> vset_fwd h = vset_chosen r \<and> rM = FinalizingChild) \<or>
  (\<exists> child. finalized_with_root_with_n_switchings (2 :: nat) r rE rM s h child v m) \<and> rE + 1 < v \<and> vset_bwd h = vset_chosen r \<and> rM = FinalizingChild)"

definition close_justification where
  "close_justification s r rE rM h v hist \<equiv>
  (rE + 1 < v \<longrightarrow> hist = Usual) \<and>
  (justified_with_root_with_n_switchings (0 :: nat) r rE rM s h v hist \<or>
  justified_with_root_with_n_switchings (1 :: nat) r rE rM s h v hist \<and> rE < v \<and> (rE + 1 = v \<longrightarrow> vset_fwd h = vset_chosen r \<and> rM = FinalizingChild) \<or>
  justified_with_root_with_n_switchings (2 :: nat) r rE rM s h v hist \<and> rE + 1 < v \<and> vset_bwd h = vset_chosen r \<and> rM = FinalizingChild)"

definition justification_fork_with_root where
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 \<equiv>
     justified s r rE rM \<and>
     (\<exists> child0 child1.
       finalized_with_root r rE rM s h0 child0 v0 m0 \<and> finalized_with_root r rE rM s h1 child1 v1 m1) \<and>
    \<not>(justified_with_root h1 v1 m1 s h0 v0 m0 \<or> justified_with_root h0 v0 m0 s h1 v1 m1)"

lemma justification_fork_with_root_sym :
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 =
   justification_fork_with_root s r rE rM h1 v1 m1 h0 v0 m0"
  by (meson justification_fork_with_root_def)

definition small_fork where
  "small_fork s hr vr mr h0 v0 m0 h1 v1 m1 \<equiv>
    justification_fork_with_root s hr vr mr h0 v0 m0 h1 v1 m1 \<and>
    (\<forall> hr' vr' mr' h0' v0' m0' h1' v1' m1'.
       v0' + v1' - vr' < v0 + v1 - vr \<longrightarrow>
       \<not> justification_fork_with_root s hr' vr' mr' h0' v0' m0' h1' v1' m1')"

lemma small_fork_sym :
  "small_fork s hr vr mr h0 v0 m0 h1 v1 m1 = small_fork s hr vr mr h1 v1 m1 h0 v0 m0"
  by (simp add: add.commute justification_fork_with_root_sym small_fork_def)

lemma close_justification_refl:
  "close_justification s r rE rM r rE rM"
  by (simp add: close_justification_def justified_genesis_n)

lemma justified_graft :
   "justified s r rE rM \<Longrightarrow>
    justified_with_root r rE rM s h v m \<Longrightarrow>
    justified s h v m"
  using justified_with_root_trans by blast

lemma usual_link_means_ancestor:
 "usual_link s q0 q1 orig origE new newE \<Longrightarrow>
  nth_parent (newE - origE) orig new"
  by (meson casper.usual_link_def casper.voted_by_both_means_ancestor casper_axioms)

lemma nth_parent_trans:
  "nth_parent b mid fin \<Longrightarrow>
   nth_parent a orig mid \<Longrightarrow>
   nth_parent (a + b) orig fin"
proof(induct rule: nth_parent.induct)
case (zeroth_parent h)
  then show ?case
    by simp
next
  case (Sth_parent n oldest mid newest)
  then show ?case
    using nth_parent.Sth_parent by auto
qed

lemma justified_means_ancestor:
  "justified_with_root r rE rM s h v m \<Longrightarrow>
   nth_parent (v - rE) r h"
proof(induct rule: justified_with_root.induct)
  case (justified_genesis r r' rE rE' mode s)
  then show ?case
    by (simp add: zeroth_parent)
next
  case (usual_justification r rE mode s orig origE q0 q1 new newE)
  then show ?case
  proof -
    have "nth_parent (origE - rE + (newE - origE)) r new"
      using local.usual_justification(2) local.usual_justification(3) nth_parent_trans usual_link_means_ancestor by blast
    then show ?thesis
      by (metis Nat.add_diff_assoc add.commute casper.justifies_higher casper_axioms le_add_diff_inverse2 less_imp_le_nat local.usual_justification(3) usual_justification.hyps(1) usual_link_higher)
  qed
next
  case (justified_on_finalization r rE mode s c e q0 q1 h ee)
  then show ?case
  proof -
have f1: "nth_parent (e - rE + (ee - e)) r h"
by (meson casper.validator_changing_link_means_ancestor casper_axioms justified_on_finalization.hyps(2) justified_on_finalization.hyps(3) nth_parent_trans)
  have f2: "rE \<le> e"
    by (meson casper.justifies_higher casper_axioms justified_on_finalization.hyps(1))
  have "e < ee"
    by (meson casper.validator_changing_link_higher casper_axioms justified_on_finalization.hyps(3))
  then show ?thesis
    using f2 f1 by (metis (no_types) Nat.add_diff_assoc add.commute le_add_diff_inverse2 less_imp_le_nat)
qed
qed

lemma nth_parent_unique:
   "nth_parent n r0 h \<Longrightarrow>
    nth_parent n r1 h \<Longrightarrow>
    r0 = r1"
proof(induct n arbitrary: h)
  case 0
  then show ?case
    by (metis less_numeral_extra(3) nth_parent.simps zero_less_Suc)
next
  case (Suc n)
  obtain mid0 where m0: "nth_parent n r0 mid0 \<and> mid0 \<leftarrow> h"
    using Suc.prems(1) nth_parent.simps by blast
  obtain mid1 where m1: "nth_parent n r1 mid1 \<and> mid1 \<leftarrow> h"
    using Suc.prems(2) nth_parent.simps by blast
  have u: "mid0 = mid1"
    by (metis byz_quorums_axioms byz_quorums_def m0 m1)
  then show ?case
    using Suc.hyps m0 m1 by blast
qed


lemma justified_back_unique:
   "justified_with_root r0 rE rM s h v m \<Longrightarrow>
    justified_with_root r1 rE rM s h v m \<Longrightarrow>
    r0 = r1"
  using justified_means_ancestor nth_parent_unique by blast

lemma finalized_is_justified :
  "finalized_with_root r rE rM s h c v m \<Longrightarrow>
   justified_with_root r rE rM s h v m"
  by(auto simp add: finalized_with_root.simps)

lemma when_n_justified_is_justified:
  "finalized_with_root r rE rM s h c v m \<Longrightarrow>
   justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
   finalized_with_root_with_n_switchings n r rE rM s h c v m"
proof(induct rule: finalized_with_root.cases)
  case (under_usual_link r rE mode s orig origE q0 q1 new)
  then show ?case
    by (meson casper.under_usual_link_n casper_axioms)
next
  case (under_changing_link r rE mode s c e q0 q1 h)
  then show ?case
    by (meson casper.under_changing_link_n casper_axioms)
qed


lemma jf :
  "justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
   finalized_with_root r rE rM s h c v m \<Longrightarrow>
   \<exists> child. finalized_with_root_with_n_switchings n r rE rM s h child v m"
  by (meson casper.when_n_justified_is_justified casper_axioms)


lemma when_close_justification_is_finalized_f :
  "close_justification s r rE FinalizingChild h v m \<Longrightarrow>
   finalized_with_root r rE FinalizingChild s h c v m \<Longrightarrow>
   close_finalization s r rE FinalizingChild h v m"
  by(auto simp add: close_finalization_def close_justification_def jf)

lemma when_close_justification_is_finalized_u :
  "close_justification s r rE Usual h v m \<Longrightarrow>
   finalized_with_root r rE Usual s h c v m \<Longrightarrow>
   close_finalization s r rE Usual h v m"
  by(auto simp add: close_finalization_def close_justification_def jf)

lemma when_close_justification_is_finalized :
  "close_justification s r rE rM h v m \<Longrightarrow>
   finalized_with_root r rE rM s h c v m \<Longrightarrow>
   close_finalization s r rE rM h v m"
  apply(cases rM)
   apply (simp add: when_close_justification_is_finalized_u)
  by (simp add: when_close_justification_is_finalized_f)

lemma jff:
   "finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
    justified s r rE rM \<Longrightarrow>
    justified_with_root h0' v0' m0' s h0 v0 m0 \<Longrightarrow>
    finalized_with_root h0' v0' m0' s h0 child0 v0 m0"
proof(induct rule: finalized_with_root.induct)
  case (under_usual_link r rE mode s orig origE q0 q1 new)
  then show ?case
    by (simp add: finalized_with_root.under_usual_link)
next
  case (under_changing_link r rE mode s c e q0 q1 h)
  then show ?case
    by (meson casper.finalized_with_root.intros(2) casper_axioms)
qed

lemma small_fork_with_middle_means_without_link:
 "justified s r rE rM \<Longrightarrow>
  finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
  finalized_with_root r rE rM s h1 child1 v1 m1 \<Longrightarrow>
  \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
  rE \<noteq> v0' \<Longrightarrow> v0' \<noteq> v0 \<Longrightarrow>
  justified_with_root r rE rM s h0' v0' m0' \<Longrightarrow>
  justified_with_root h0' v0' m0' s h0 v0 m0 \<Longrightarrow> finalized_with_root r rE rM s h0' c0' v0' m0' \<Longrightarrow>
  \<not> justified_with_root h0' v0' m0' s h1 v1 m1 \<Longrightarrow>
  justification_fork_with_root s r rE rM h0' v0' m0' h1 v1 m1"
  using justification_fork_with_root_def justified_with_root_trans by blast

lemma small_fork_with_middle_means_with_link:
 "justified s r rE rM \<Longrightarrow>
  finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
  finalized_with_root r rE rM s h1 child1 v1 m1 \<Longrightarrow>
  \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
  rE \<noteq> v0' \<Longrightarrow> v0' \<noteq> v0 \<Longrightarrow>
  justified_with_root r rE rM s h0' v0' m0' \<Longrightarrow>
  justified_with_root h0' v0' m0' s h0 v0 m0 \<Longrightarrow> finalized_with_root r rE rM s h0' c0' v0' m0' \<Longrightarrow>
  justified_with_root h0' v0' m0' s h1 v1 m1 \<Longrightarrow>
  justification_fork_with_root s h0' v0' m0' h0 v0 m0 h1 v1 m1"
  by (meson jff justification_fork_with_root_def justified_with_root_trans)

lemma small_fork_with_middle_means:
 "justified s r rE rM \<Longrightarrow>
  finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
  finalized_with_root r rE rM s h1 child1 v1 m1 \<Longrightarrow>
  \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
  rE \<noteq> v0' \<Longrightarrow> v0' \<noteq> v0 \<Longrightarrow>
  justified_with_root r rE rM s h0' v0' m0' \<Longrightarrow>
  justified_with_root h0' v0' m0' s h0 v0 m0 \<Longrightarrow> finalized_with_root r rE rM s h0' c0' v0' m0' \<Longrightarrow>
  justification_fork_with_root s r rE rM h0' v0' m0' h1 v1 m1 \<or>
  justification_fork_with_root s h0' v0' m0' h0 v0 m0 h1 v1 m1"
  by (meson small_fork_with_middle_means_with_link small_fork_with_middle_means_without_link)

lemma small_fork_has_no_middle_fin:
 "justified s r rE rM \<Longrightarrow>
  finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
  finalized_with_root r rE rM s h1 child1 v1 m1 \<Longrightarrow>
  \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
  \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
  rE \<noteq> v0' \<Longrightarrow> v0' \<noteq> v0 \<Longrightarrow>
  justified_with_root r rE rM s h0' v0' m0' \<Longrightarrow>
  justified_with_root h0' v0' m0' s h0 v0 m0 \<Longrightarrow> finalized_with_root r rE rM s h0' c0' v0' m0' \<Longrightarrow> False"
proof -
  assume j: "justified s r rE rM"
  assume f0: "finalized_with_root r rE rM s h0 child0 v0 m0"
  assume f1: "finalized_with_root r rE rM s h1 child1 v1 m1"
  assume j10: "\<not> justified_with_root h1 v1 m1 s h0 v0 m0"
  assume j01: "\<not> justified_with_root h0 v0 m0 s h1 v1 m1"
  assume rv: "rE \<noteq> v0'"
  assume vv: "v0' \<noteq> v0"
  assume lower: "justified_with_root r rE rM s h0' v0' m0'"
  assume higher: "justified_with_root h0' v0' m0' s h0 v0 m0"
  assume mid_f: "finalized_with_root r rE rM s h0' c0' v0' m0'"
  assume no_mid: "  \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
     v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1'"
  consider
    (a) "justification_fork_with_root s r rE rM h0' v0' m0' h1 v1 m1" |
    (b) "justification_fork_with_root s h0' v0' m0' h0 v0 m0 h1 v1 m1"
    by (meson casper.small_fork_with_middle_means casper_axioms f0 f1 higher j j01 j10 lower mid_f rv vv)
  then show ?thesis
  proof(cases)
    case a
    then have "v0' + v1 - rE < v0 + v1 - rE"
      by (meson add_strict_right_mono diff_less_mono higher justifies_higher le_neq_implies_less less_le_trans linorder_not_le lower not_add_less1 vv)
    then show ?thesis
      using a no_mid by blast
  next
    case b
    then have "v0 + v1 - v0' < v0 + v1 - rE"
      by (metis casper.justifies_higher casper_axioms diff_less_mono2 higher le_less_trans le_neq_implies_less lower rv trans_less_add1)
    then show ?thesis
      using b no_mid by blast
  qed
qed

lemma not_finalizing:
  "origM \<noteq> FinalizingChild \<Longrightarrow> origM = Usual"
  using Mode.exhaust by blast

lemma justified_with_shallow_usual_link:
  "justified_with_root_with_n_switchings n r rE mode s orig origE Usual \<Longrightarrow>
   usual_link s q0 q1 orig origE new newE \<Longrightarrow>
   newE - origE = 1 \<Longrightarrow>
   finalized_with_root r rE mode s orig new origE Usual"
proof -
  assume num: "newE - origE = 1"
  assume "justified_with_root_with_n_switchings n r rE mode s orig origE Usual"
  then have "justified_with_root r rE mode s orig origE Usual"
    using forget_n_switchings by blast
  moreover have "newE = origE + 1"
    using num by linarith
  moreover assume "usual_link s q0 q1 orig origE new newE"
  ultimately show ?thesis
    using under_usual_link by blast
qed

lemma finalizing_can_happen_near:
  "justified_with_root_with_n_switchings n r rE rM s c e m \<Longrightarrow>
   m = FinalizingChild \<Longrightarrow>
   \<forall> h' c' v' m'.
      rE \<noteq> v' \<longrightarrow> v' \<noteq> e \<longrightarrow>
      justified_with_root r rE rM s h' v' m' \<longrightarrow>
      justified_with_root h' v' m' s c e FinalizingChild \<longrightarrow>
      \<not> finalized_with_root r rE rM s h' c' v' m' \<Longrightarrow>
   e \<le> rE + 1"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' s)
  then show ?case by linarith
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have f :"finalized_with_root r rE mode s orig new origE Usual"
    using casper.justified_with_shallow_usual_link casper_axioms usual_justification_n.hyps(1)
         usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5)
         usual_justification_n.prems(1) by fastforce
  show ?case proof(cases "rE = origE")
    case True
    then show ?thesis
      by (metis Mode.simps(1) add_diff_inverse_nat eq_iff less_numeral_extra(3)
           nat_diff_split usual_justification_n.hyps(4) usual_justification_n.hyps(5)
           usual_justification_n.prems(1) usual_link_higher zero_less_diff)
  next
    case False
    have diff1: "rE \<noteq> origE"
      by (simp add: False)
    have diff2: "origE \<noteq> newE"
      using usual_justification_n.hyps(5) usual_justification_n.prems(1) by force
    have j1: "justified_with_root r rE mode s orig origE Usual"
      using f finalized_is_justified by blast
    have j2: "justified_with_root orig origE Usual s new newE FinalizingChild"
      using casper.justified_with_root_refl casper_axioms usual_justification
         usual_justification_n.hyps(4) usual_justification_n.hyps(5)
         usual_justification_n.prems(1) by fastforce
    have "\<forall>h' c' v' m'.
       rE \<noteq> v' \<longrightarrow>
       v' \<noteq> newE \<longrightarrow>
       justified_with_root r rE mode s h' v' m' \<longrightarrow>
       justified_with_root h' v' m' s new newE newM \<longrightarrow>
       \<not> finalized_with_root r rE mode s h' c' v' m'"
      using usual_justification_n.prems by blast
    moreover have "newM = FinalizingChild"
      by (simp add: usual_justification_n.prems(1))
    ultimately have r: "rE \<noteq> origE \<Longrightarrow> origE \<noteq> newE \<Longrightarrow>
      justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
      justified_with_root orig origE Usual s new newE FinalizingChild \<Longrightarrow>
      \<not> finalized_with_root r rE mode s orig new origE Usual"
      by blast
    have strange: " \<not> finalized_with_root r rE mode s orig new origE Usual"
      using diff1 diff2 j1 j2 by(rule r; auto)
    show ?thesis using f strange by auto
  qed
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  have f :"finalized_with_root r rE mode s c h e FinalizingChild"
    by (metis Mode.simps(1) add_diff_inverse_nat casper.under_changing_link casper_axioms 
       forget_n_switchings justified_on_finalization_n.hyps(1)
       justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(4)
       justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(1) less_numeral_extra(3)
       nat_diff_split validator_changing_link_higher zero_less_diff)
  have "e = rE"
    by (metis casper.finalized_is_justified casper.justified_with_root.intros(3) casper_axioms f justified_genesis justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(2) nat_neq_iff validator_changing_link_higher)
  then show ?case
    by (metis Mode.simps(1) add_diff_inverse_nat eq_iff
      justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5)
      justified_on_finalization_n.prems(1) less_numeral_extra(3) 
      nat_diff_split validator_changing_link_higher zero_less_diff)
qed

lemma justified_switch_really_higher :
  "justified_with_root_with_n_switchings n r rE mode s h ee m \<Longrightarrow>
   0 < n \<Longrightarrow>
   rE < ee"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (meson less_trans usual_link_higher)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (meson casper.justifies_higher casper_axioms forget_n_switchings less_le_trans linorder_not_le validator_changing_link_higher)
qed

lemma short_one_switching:
"justified_with_root_with_n_switchings one r rE mode s h ee FinalizingChild \<Longrightarrow>
 one = (1 :: nat) \<Longrightarrow>
 rE + 1 = ee \<Longrightarrow>
 vset_fwd h = vset_chosen r"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' s)
  then show ?case
    by linarith
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have "rE = origE"
    using justified_switch_really_higher usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_link_higher by fastforce
  then have "False"
    using casper.justified_switch_really_higher casper_axioms usual_justification_n.hyps(1) usual_justification_n.prems(1) by fastforce
  then show ?case by simp
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have "validator_changing_link s q0 q1 r rE h ee"
    by (metis One_nat_def add.right_neutral add_Suc_right casper.justifies_higher casper_axioms forget_n_switchings justified_means_ancestor le_neq_implies_less neq0_conv not_less_eq nth_parent_unique validator_changing_link_higher zero_less_diff zeroth_parent)
  then show ?case
    using validator_changing_link_def by blast
qed


lemma short_fin:
"justified_with_root_with_n_switchings one r rE mode s h ee FinalizingChild \<Longrightarrow>
 one = (1 :: nat) \<Longrightarrow>
 rE + 1 = ee \<Longrightarrow>
 mode = FinalizingChild"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case
  by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have "rE = origE"
    using justified_switch_really_higher usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_link_higher by fastforce
  then have "False"
    using casper.justified_switch_really_higher casper_axioms usual_justification_n.hyps(1) usual_justification_n.prems(1) by fastforce
  then show ?case by simp
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have "e = rE"
    by (metis One_nat_def Suc_diff_Suc add.right_neutral add_Suc_right casper.justifies_higher casper_axioms diff_Suc_Suc diff_add_inverse2 diff_diff_cancel diff_is_0_eq forget_n_switchings order.strict_iff_order validator_changing_link_higher)
  then show ?case
    using justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(2) refl_inv by fastforce
qed


lemma jR':
   "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
    usual_link s q0 q1 orig origE new newE \<Longrightarrow>
    newE - origE = 1 \<Longrightarrow>
    finalized_with_root r rE mode s orig new origE Usual"
  by (metis le_add_diff_inverse less_imp_le under_usual_link usual_link_higher)

lemma jR:
   "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
    usual_link s q0 q1 orig origE new newE \<Longrightarrow>
    newM = (if newE - origE = 1 then FinalizingChild else Usual) \<Longrightarrow>
    \<forall>h' c' v' m'.
       rE \<noteq> v' \<longrightarrow>
       v' \<noteq> newE \<longrightarrow>
       justified_with_root r rE mode s h' v' m' \<longrightarrow>
       justified_with_root h' v' m' s new newE newM \<longrightarrow> \<not> finalized_with_root r rE mode s h' c' v' m' \<Longrightarrow>
    rE + 1 < newE \<Longrightarrow> newE - origE \<noteq> 1"
proof(cases "newE - origE = 1")
  case True
  assume j0: "justified_with_root r rE mode s orig origE Usual"
  assume u: " usual_link s q0 q1 orig origE new newE"
  then have "finalized_with_root r rE mode s orig new origE Usual"
    using True j0 jR' by blast
  assume strech: "rE + 1 < newE"
  have dif0: "rE \<noteq> origE"
    using True strech by linarith
  have dif1: "origE \<noteq> newE"
    using True by linarith
  assume "newM = (if newE - origE = 1 then FinalizingChild else Usual)"
  then have nF: "newM = FinalizingChild"
    by (simp add: True)
  have j1: "justified_with_root orig origE Usual s new newE FinalizingChild"
    by (meson True casper.justified_genesis casper_axioms u usual_justification)
  have j2: "justified_with_root orig origE Usual s new newE newM"
    by (simp add: j1 nF)
  assume no_mid: "\<forall>h' c' v' m'.
       rE \<noteq> v' \<longrightarrow>
       v' \<noteq> newE \<longrightarrow>
       justified_with_root r rE mode s h' v' m' \<longrightarrow>
       justified_with_root h' v' m' s new newE newM \<longrightarrow> \<not> finalized_with_root r rE mode s h' c' v' m'"
  then have "\<not> finalized_with_root r rE mode s orig new origE Usual"
    using dif0 dif1 j0 j2 by blast
  then show ?thesis
    using \<open>finalized_with_root r rE mode s orig new origE Usual\<close> by blast
next
  case False
  then show ?thesis by blast
qed

lemma close_justification_alt :
  "justified_with_root r rE rM s h v m \<Longrightarrow>
   \<forall> h' c' v' m'.
      rE \<noteq> v' \<longrightarrow> v' \<noteq> v \<longrightarrow>
      justified_with_root r rE rM s h' v' m' \<longrightarrow>
      justified_with_root h' v' m' s h v m \<longrightarrow> \<not> finalized_with_root r rE rM s h' c' v' m' \<Longrightarrow>
   close_justification s r rE rM h v m"
proof(induct rule: justified_with_root.induct)
  case (justified_genesis r r' rE rE' mode s)
  then show ?case by (simp add: close_justification_refl)
next
  case (usual_justification r rE mode s orig origE q0 q1 new newE newM)
  then have cd: "rE + 1 < newE \<longrightarrow> newE - origE \<noteq> 1"
    using jR by blast
  then have c0: "rE + 1 < newE \<longrightarrow> newM = Usual"
    by (simp add: usual_justification.hyps(4))
  have "close_justification s r rE mode orig origE Usual"
    by (smt antisym justified_with_root.usual_justification justifies_higher order.order_iff_strict usual_justification.hyps(2) usual_justification.hyps(3) usual_justification.hyps(4) usual_justification.prems usual_link_higher)
  then consider 
    (a) "justified_with_root_with_n_switchings (0 :: nat) r rE mode s orig origE Usual" |
    (b) "justified_with_root_with_n_switchings (1 :: nat) r rE mode s orig origE Usual \<and> rE < origE \<and> (rE + 1 = origE \<longrightarrow> vset_fwd orig = vset_chosen r \<and> mode = FinalizingChild)" |
    (c) "justified_with_root_with_n_switchings (2 :: nat) r rE mode s orig origE Usual \<and> rE + 1 < origE \<and> vset_bwd orig = vset_chosen r \<and> mode = FinalizingChild"
    using close_justification_def by blast
  then show ?case proof(cases)
    case a
    then show ?thesis
      by (smt casper.close_justification_def casper.usual_justification_n casper_axioms cd usual_justification.hyps(3) usual_justification.hyps(4))
  next
    case b
    then show ?thesis
      by (smt Suc_eq_plus1 Suc_leI c0 casper.usual_justification_n casper_axioms cd close_justification_def justifies_higher le_less_trans nat_neq_iff usual_justification.hyps(1) usual_justification.hyps(3) usual_link_higher)
  next
    case c
    then show ?thesis
      by (smt casper.usual_justification_n casper_axioms cd close_justification_def le_less_trans order.strict_iff_order usual_justification.hyps(3) usual_justification.hyps(4) usual_link_def usual_link_higher)
  qed

  next
  case (justified_on_finalization r rE mode s c e q0 q1 h ee newM)
  then have "close_justification s r rE mode c e FinalizingChild"
  proof -
    obtain nn :: nat and eea :: 'e and mm :: Mode and eeb :: 'e where
      "(\<exists>v0 v1 v2 v3. (rE \<noteq> v2 \<and> v2 \<noteq> e \<and> justified_with_root r rE mode s v0 v2 v3 \<and> justified_with_root v0 v2 v3 s c e FinalizingChild) \<and> finalized_with_root r rE mode s v0 v1 v2 v3) = ((rE \<noteq> nn \<and> nn \<noteq> e \<and> justified_with_root r rE mode s eea nn mm \<and> justified_with_root eea nn mm s c e FinalizingChild) \<and> finalized_with_root r rE mode s eea eeb nn mm)"
      by blast
    moreover
    { assume "justified_with_root eea nn mm s h ee (if ee - e = 1 then FinalizingChild else Usual)"
      moreover
      { assume "\<not> nn \<le> ee \<or> nn = ee"
        then have "(rE = nn \<or> nn = e \<or> \<not> justified_with_root r rE mode s eea nn mm \<or> \<not> justified_with_root eea nn mm s c e FinalizingChild) \<or> \<not> finalized_with_root r rE mode s eea eeb nn mm"
          by (meson justifies_higher le_less_trans local.justified_on_finalization(3) order.strict_iff_order validator_changing_link_higher) }
      ultimately have "(rE = nn \<or> nn = e \<or> \<not> justified_with_root r rE mode s eea nn mm \<or> \<not> justified_with_root eea nn mm s c e FinalizingChild) \<or> \<not> finalized_with_root r rE mode s eea eeb nn mm"
        using justified_on_finalization.hyps(4) justified_on_finalization.prems by blast }
    ultimately show ?thesis
      using justified_with_root.justified_on_finalization local.justified_on_finalization(2) local.justified_on_finalization(3) by blast
  qed
  then consider (a) "justified_with_root_with_n_switchings (0 :: nat) r rE mode s c e FinalizingChild" |
    (b) "justified_with_root_with_n_switchings (1 :: nat) r rE mode s c e FinalizingChild \<and> rE < e \<and> (rE + 1 = e \<longrightarrow> vset_fwd c = vset_chosen r)" |
    (c) "justified_with_root_with_n_switchings (2 :: nat) r rE mode s c e FinalizingChild \<and> rE + 1 < e \<and> vset_bwd c = vset_chosen r \<and> mode = FinalizingChild"
    by(simp add: close_justification_def; auto)
  then show ?case proof cases
    case a
    then show ?thesis proof (cases "ee = e + 1")
      case True
      have nextj: "justified_with_root_with_n_switchings (1 :: nat) r rE mode s h ee FinalizingChild"
        using True a casper.justified_with_root_with_n_switchings.intros(3) casper_axioms justified_on_finalization.hyps(3) by fastforce
      have ee_big: "rE < ee"
        using casper.justifies_higher casper_axioms justified_on_finalization.hyps(1) justified_on_finalization.hyps(3) nat.simps(3) validator_changing_link_higher by fastforce
      have additional: "rE + 1 = ee \<longrightarrow> vset_fwd h = vset_chosen r \<and> mode = FinalizingChild"
        using nextj short_fin short_one_switching by blast
      have "justified_with_root_with_n_switchings (1 :: nat) r rE mode s h ee FinalizingChild \<and> rE < ee \<and> (rE + 1 = ee \<longrightarrow> vset_fwd h = vset_chosen r \<and> mode = FinalizingChild)"
        using additional ee_big nextj by linarith
      then show ?thesis
        by (smt One_nat_def Suc_diff_Suc Suc_eq_plus1 True cancel_comm_monoid_add_class.diff_cancel casper.close_justification_def casper_axioms finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justified_on_finalization.prems leD validator_changing_link_higher)
    next
      case False
      then show ?thesis
        by (smt One_nat_def Suc_eq_plus1 Suc_lessI a add_diff_inverse_nat casper.justified_with_root_with_n_switchings.intros(3) casper_axioms close_justification_def justified_on_finalization.hyps(1) justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justifies_higher le_less_trans le_neq_implies_less less_numeral_extra(3) nat_diff_split validator_changing_link_higher zero_less_diff)
    qed
  next
    case b
    then show ?thesis
    proof(cases "ee - e = 1")
      case True
      have j2: "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee FinalizingChild"
      proof -
        have "\<forall>x0 x10 x11 x12 x13 x14 x16 x1 x4 x6 x7 x8 x9. casper.justified_with_root_with_n_switchings (x16::'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) x14 x13 x12 x11 (Suc x10) x9 x8 x7 (x6::(_, 'e, 'f) state_scheme) x1 x0 (if x0 - x4 = 1 then FinalizingChild else Usual) = (if x0 - x4 = 1 then casper.justified_with_root_with_n_switchings x16 x14 x13 x12 x11 (Suc x10) x9 x8 x7 x6 x1 x0 FinalizingChild else casper.justified_with_root_with_n_switchings x16 x14 x13 x12 x11 (Suc x10) x9 x8 x7 x6 x1 x0 Usual)"
          by presburger
        then have "justified_with_root_with_n_switchings (Suc 1) r rE mode s h ee FinalizingChild"
          by (meson True b casper.justified_with_root_with_n_switchings.intros(3) casper_axioms justified_on_finalization.hyps(3))
        then show ?thesis
          by (metis Suc_1)
      qed
      have num: "rE + 1 < ee"
        using True b by linarith
      have "rE < e"
        by (simp add: b)
      moreover have "e \<le> rE + 1"
        by (smt True finalizing_can_happen_near j2 justified_on_finalization.hyps(4) justified_on_finalization.prems leD num)
      ultimately have era: "rE + 1 = e"
        by linarith
      have "vset_bwd h = vset_fwd c"
        using justified_on_finalization.hyps(3) validator_changing_link_def by blast
      moreover have "vset_fwd c = vset_chosen r" (* I need the fact rE + 1 = e ... Maybe strengthen the close_justification conditions? *)
        using b era by blast
      ultimately have vs: "vset_bwd h = vset_chosen r"
        by simp
      have "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee FinalizingChild \<and> rE + 1 < ee \<and> vset_bwd h = vset_chosen r"
        using j2 num vs by blast
      then show ?thesis
        by (smt True finalizing_can_happen_near justified_on_finalization.hyps(4) justified_on_finalization.prems leD)
    next
      case False
      have "validator_changing_link s q0 q1 c e h ee"
        using justified_on_finalization.hyps(3) by auto
      have jee: "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee Usual"
        by (metis False One_nat_def b casper.justified_with_root_with_n_switchings.intros(3) casper_axioms justified_on_finalization.hyps(3) numeral_2_eq_2)
      moreover have "rE < ee"
        by (meson b justified_on_finalization.hyps(3) less_trans validator_changing_link_higher)
      moreover have "rE + 1 \<noteq> ee"
        using b justified_on_finalization.hyps(3) validator_changing_link_higher by fastforce
      ultimately have "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee Usual \<and> rE + 1 < ee \<and> vset_bwd h = vset_chosen r"
        by (smt antisym b casper.justified_with_root.intros(3) casper_axioms diff_is_0_eq' discrete finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justified_on_finalization.prems justifies_higher less_numeral_extra(3) validator_changing_link_def validator_changing_link_higher zero_less_diff)
      moreover have "newM = Usual"
        using False justified_on_finalization.hyps(4) by auto
      moreover have "mode = FinalizingChild"
        by (smt False Suc_eq_plus1 Suc_lessI b calculation(2) finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.prems justified_with_root.justified_on_finalization justifies_higher not_less short_fin validator_changing_link_higher)
      ultimately show ?thesis
        by (simp add: close_justification_def)
    qed
  next
    case c
    then show ?thesis
      by (smt finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justified_on_finalization.prems justified_with_root.justified_on_finalization justifies_higher leD validator_changing_link_higher)
  qed
qed

lemma close_finalization_alt :
  "finalized_with_root r rE rM s h c v m \<Longrightarrow>
   \<forall> h' c' v' m'.
      rE \<noteq> v' \<longrightarrow> v' \<noteq> v \<longrightarrow>
      justified_with_root r rE rM s h' v' m' \<longrightarrow>
      justified_with_root h' v' m' s h v m \<longrightarrow> \<not> finalized_with_root r rE rM s h' c' v' m' \<Longrightarrow>
   close_finalization s r rE rM h v m"
  by (simp add: close_justification_alt finalized_is_justified when_close_justification_is_finalized)

lemma close_justification_three:
 "justified s r rE rM \<Longrightarrow>
    finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
    finalized_with_root r rE rM s h1 child1 v1 m1 \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
proof -
  assume "justified s r rE rM"
  moreover assume f0: "finalized_with_root r rE rM s h0 child0 v0 m0"
  moreover assume "finalized_with_root r rE rM s h1 child1 v1 m1"
  moreover assume "\<not> justified_with_root h1 v1 m1 s h0 v0 m0"
  moreover assume "\<not> justified_with_root h0 v0 m0 s h1 v1 m1"
  moreover assume "\<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1'"
  ultimately have "\<forall> h0' c0' v0' m0'.
      rE \<noteq> v0' \<longrightarrow> v0' \<noteq> v0 \<longrightarrow> justified_with_root r rE rM s h0' v0' m0' \<longrightarrow> 
      justified_with_root h0' v0' m0' s h0 v0 m0 \<longrightarrow> \<not> finalized_with_root r rE rM s h0' c0' v0' m0'"
    apply(rule_tac allI)
    apply(rule_tac allI)
    apply(rule_tac allI)
    apply(rule_tac allI)
    apply(rule_tac impI)
    apply(rule_tac impI)
    apply(rule_tac impI)
    apply(rule_tac impI)
    using small_fork_has_no_middle_fin by auto
  then show ?thesis
    using close_finalization_alt f0 by blast
qed

lemma close_justification_two:
 "justified s r rE rM \<Longrightarrow>
    (\<exists>child0. finalized_with_root r rE rM s h0 child0 v0 m0) \<Longrightarrow>
    (\<exists>child1. finalized_with_root r rE rM s h1 child1 v1 m1) \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
proof -
  assume j: "justified s r rE rM"
  assume "\<exists>child0. finalized_with_root r rE rM s h0 child0 v0 m0"
  then obtain child0 where a0: "finalized_with_root r rE rM s h0 child0 v0 m0" by blast
  assume "\<exists>child1. finalized_with_root r rE rM s h1 child1 v1 m1"
  then obtain child1 where a1: "finalized_with_root r rE rM s h1 child1 v1 m1" by blast
  assume a2: "\<not> justified_with_root h1 v1 m1 s h0 v0 m0"
  assume a3: "\<not> justified_with_root h0 v0 m0 s h1 v1 m1"
  assume a4: "
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1'"
  show ?thesis using j a0 a1 a2 a3 a4 by(rule close_justification_three; auto)
qed

lemma close_justification_one:
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
  apply (simp add: justification_fork_with_root_def)
  apply (rule_tac close_justification_two; auto)
  apply (auto simp add: justification_fork_with_root_def)
  by blast

lemma small_fork_has_close_justification :
  "small_fork s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
  apply(simp add: small_fork_def)
  apply(rule close_justification_one; auto)
  by blast

lemma close_justification_era:
  "close_justification s r rE rM h v m \<Longrightarrow>
   rE \<le> v"
  by (meson casper.close_justification_def casper_axioms forget_n_switchings justifies_higher)

lemma close_justification_is_justification:
  "close_justification s r rE rM h v m \<Longrightarrow>
   justified_with_root r rE rM s h v m"
  by (meson casper.close_justification_def casper_axioms forget_n_switchings justifies_higher)

lemma trivial_is_refl0:
  "justified_with_root_with_n_switchings 0 r v rM s h v m \<Longrightarrow> rE = v \<Longrightarrow> r = h"
  by (metis cancel_comm_monoid_add_class.diff_cancel forget_n_switchings justified_means_ancestor less_Suc_eq_0_disj less_numeral_extra(3) nth_parent.simps)

lemma trivial_is_refl1:
  "justified_with_root_with_n_switchings 0 r v rM s h v m \<Longrightarrow> rE = v \<Longrightarrow> rM = m"
  using refl_inv by blast

lemma trivial_is_refl:
  "close_justification s r rE rM h v m \<Longrightarrow>
   rE = v \<Longrightarrow>
   r = h \<and> rM = m"
  by (metis casper.close_justification_def casper_axioms not_add_less1 order_less_irrefl refl_inv trivial_is_refl0)

lemma really_close_justification_zero:
  "justified_with_root_with_n_switchings n r rE rM s h rE' m \<Longrightarrow>
   rE' = Suc rE \<Longrightarrow> m = FinalizingChild"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case using n_not_Suc_n by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (metis Nat.diff_diff_right Suc_eq_plus1_left casper.forget_n_switchings casper.usual_link_higher casper_axioms diff_is_0_eq' justifies_higher linorder_not_le minus_nat.diff_0 not_less_eq_eq)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
then show ?case
  by (metis Suc_eq_plus1 add_left_imp_eq casper.justifies_higher casper_axioms forget_n_switchings leD le_add_diff_inverse not_less_eq_eq order.strict_iff_order validator_changing_link_higher)
qed

lemma close_justification_mode_f:
  "close_justification s r rE rM h v m \<Longrightarrow>
   v = rE + 1 \<Longrightarrow> m = FinalizingChild"
  by (metis Suc_eq_plus1 casper.close_justification_def casper_axioms really_close_justification_zero)

lemma close_justification_mode_u:
  "close_justification s r rE rM h v m \<Longrightarrow>
   v > rE + 1 \<Longrightarrow> m = Usual"
  by(auto simp add: close_justification_def)

lemma zero_switching_means:
  "justified_with_root_with_n_switchings n r rE Usual s h0 v m0 \<Longrightarrow>
   n = 0 \<Longrightarrow>
   vset_fwd r = vset_fwd h0 \<and>
   vset_bwd r = vset_bwd h0"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (simp add: usual_link_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case by linarith
qed

lemma one_switching_means:
  "justified_with_root_with_n_switchings n r rE rM s h0 v m0 \<Longrightarrow>
   rM = Usual \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
   vset_fwd r = vset_bwd h0"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case by (simp add: usual_link_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have "justified_with_root_with_n_switchings 0 r rE Usual s c e origM"
    by blast
  then have e1: "vset_fwd r = vset_fwd c"
    using zero_switching_means by blast
  have "vset_fwd c = vset_bwd h"
    using justified_on_finalization_n.hyps(4) validator_changing_link_def by force
  then show ?case
    by (simp add: e1)
qed



lemma justified_is_voted:
   "justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
    rE \<noteq> v \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_fwd h) p0 pv0 h v"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case by (meson usual_link_def voted_by_both_def voted_by_fwd_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (meson casper.validator_changing_link_def casper.voted_by_both_def casper_axioms voted_by_fwd_def)
qed

lemma justified_is_voted_bwd:
   "justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
    rE \<noteq> v \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_bwd h) p0 pv0 h v"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (meson usual_link_def voted_by_both_def voted_by_bwd_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (meson validator_changing_link_def voted_by_both_def voted_by_bwd_def)
qed


lemma zero_switching_involves_root_vote:
   "rE \<noteq> v \<Longrightarrow>
    justified_with_root_with_n_switchings 0 r rE Usual s h0 v m0 \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
proof -
  assume j: "justified_with_root_with_n_switchings 0 r rE Usual s h0 v m0"
  have same: "vset_fwd r = vset_fwd h0"
    using j zero_switching_means by blast
  assume non_trivial: "rE \<noteq> v"
  have v: "\<exists>q0 p0 pv0. voted_by s q0 (vset_fwd h0) p0 pv0 h0 v"
    by (meson casper.justified_is_voted casper_axioms j non_trivial)
  show ?thesis
    by (simp add: same v)
qed

lemma one_switching_involves_root_vote:
   "rE \<noteq> v \<Longrightarrow>
    justified_with_root_with_n_switchings (Suc 0) r rE Usual s h0 v m0 \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
proof -
  assume j: "justified_with_root_with_n_switchings (Suc 0) r rE Usual s h0 v m0"
  have same: "vset_fwd r = vset_bwd h0"
    using j one_switching_means by blast
  assume non_trivial: "rE \<noteq> v"
  have v: "\<exists>q0 p0 pv0. voted_by s q0 (vset_bwd h0) p0 pv0 h0 v"
    using j justified_is_voted_bwd non_trivial by blast
  show ?thesis
    by (simp add: same v)
qed


lemma after_one_switching:
  "justified_with_root_with_n_switchings n r rE rM s h0 v m0 \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
   rM = FinalizingChild \<Longrightarrow>
   vset_fwd h0 = vset_chosen r \<and> vset_bwd h0 = vset_fwd r"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (simp add: usual_link_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have z: "n = 0" by blast
  then have "rE = e"
    using casper.zero_justification_f casper_axioms justified_on_finalization_n.hyps(1) justified_on_finalization_n.prems(2) by fastforce
  then have "r = c"
    using z justified_on_finalization_n.hyps(1) trivial_is_refl0 by blast
  then show ?case
    by (meson casper.validator_changing_link_def casper_axioms justified_on_finalization_n.hyps(4))
qed

lemma one_switching_involves_root_vote_f:
    "justified_with_root_with_n_switchings (Suc 0) r rE FinalizingChild s h0 v m0 \<Longrightarrow>
    rE < v \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_chosen r) p0 pv0 h0 v"
proof -
  assume j: "justified_with_root_with_n_switchings (Suc 0) r rE FinalizingChild s h0 v m0"
  assume diff: "rE < v"
  have "\<exists>q0 p0 pv0. voted_by s q0 (vset_fwd h0) p0 pv0 h0 v"
    by (metis casper.justified_is_voted casper_axioms diff j nat_neq_iff)
  moreover have "vset_fwd h0 = vset_chosen r"
    using after_one_switching j by blast
  ultimately show ?thesis by auto
qed

lemma close_involves_vote:
  "close_justification s r rE Usual h0 v m0 \<Longrightarrow>
   rE \<noteq> v \<Longrightarrow>
   \<exists> q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
  by (metis Mode.simps(1) One_nat_def casper.close_justification_def casper_axioms one_switching_involves_root_vote zero_switching_involves_root_vote)

lemma close_involves_vote_f:
  "close_justification s r rE FinalizingChild h0 v m0 \<Longrightarrow>
   rE \<noteq> v \<Longrightarrow>
   \<exists> q0 p0 pv0. voted_by s q0 (vset_chosen r) p0 pv0 h0 v"
  apply(auto simp add: close_justification_def)
  using zero_justification_f apply blast
  using zero_justification_f apply blast
  apply (simp add: one_switching_involves_root_vote_f)
    apply (meson casper.one_switching_involves_root_vote_f casper_axioms)
  apply (meson casper.one_switching_involves_root_vote_f casper_axioms)
  using justified_is_voted_bwd by fastforce

lemma double_vote:
  "voted_by s q0 vset p0 pv0 h0 v \<Longrightarrow>
   voted_by s q1 vset p1 pv1 h1 v \<Longrightarrow>
   h0 \<noteq> h1 \<or> pv0 \<noteq> pv1 \<Longrightarrow>
   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> slashed s n"
proof -
  assume v0: "voted_by s q0 vset p0 pv0 h0 v"
  assume v1: "voted_by s q1 vset p1 pv1 h1 v"
  have "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> (n \<in>\<^sub>1 q0 of vset) \<and> (n \<in>\<^sub>1 q1 of vset)"
    by (metis byz_quorums_axioms byz_quorums_def)
  then obtain q where qP: "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> (n \<in>\<^sub>1 q0 of vset) \<and> (n \<in>\<^sub>1 q1 of vset)"
    by blast
  have vv0: "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> vote_msg s n h0 v pv0"
    using qP v0 voted_by_def by blast
  have vv1: "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> vote_msg s n h1 v pv1"
    using qP v1 voted_by_def by blast
  assume diff: "h0 \<noteq> h1 \<or> pv0 \<noteq> pv1"
  have ddr: "\<forall> n. vote_msg s n h0 v pv0 \<longrightarrow> vote_msg s n h1 v pv1 \<longrightarrow> slashed_dbl s n"
    using diff slashed_dbl_def by fastforce
  have "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> slashed_dbl s n"
    by (simp add: ddr vv0 vv1)
  then show ?thesis
    by (meson slashed_def)
qed


lemma close_finalizations_cause_slashing_u_j :
  " close_justification s r rE Usual h0 v m0 \<Longrightarrow>
    close_justification s r rE Usual h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
    \<exists>q. one_third_of_fwd_or_bwd_slashed s r q"
proof -
  assume c0: "close_justification s r rE Usual h0 v m0"
  assume c1: "close_justification s r rE Usual h1 v m1"
  assume n01: "\<not> justified_with_root h0 v m0 s h1 v m1"
  then have not_same: "h0 \<noteq> h1 \<or> m0 \<noteq> m1"
    using justified_genesis by blast
  have non_trivial: "rE \<noteq> v"
    using c0 c1 not_same trivial_is_refl by blast
  have v0: "\<exists> q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
    using c0 close_involves_vote non_trivial by blast
  have v1: "\<exists> q1 p1 pv1. voted_by s q1 (vset_fwd r) p1 pv1 h1 v"
    using c1 close_involves_vote non_trivial by blast
  have "m0 = m1"
    by (metis c0 c1 close_justification_era close_justification_mode_f close_justification_mode_u discrete le_neq_implies_less non_trivial)
  then have "h0 \<noteq> h1"
    using not_same by blast
  then show ?thesis
    by (meson casper.double_vote casper_axioms one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def v0 v1)
qed

lemma close_fj :
  "close_finalization s r rE rM h v m \<Longrightarrow>
   close_justification s r rE rM h v m"
  by(auto simp add: close_finalization_def close_justification_def fjn)

lemma close_finalizations_cause_slashing_u_inner :
  " close_finalization s r rE Usual h0 v m0 \<Longrightarrow>
    close_finalization s r rE Usual h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
    \<exists>q. one_third_of_fwd_or_bwd_slashed s r q"
  by (meson casper.close_finalizations_cause_slashing_u_j casper.close_fj casper_axioms)

lemma close_finalizations_cause_slashing_u :
  " close_finalization s r rE Usual h0 v m0 \<Longrightarrow>
    close_finalization s r rE Usual h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
    \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
  using close_finalizations_cause_slashing_u_inner by blast

lemma close_finalizations_cause_slashing_f_chosen :
  " close_finalization s r rE FinalizingChild h0 v m0 \<Longrightarrow>
    close_finalization s r rE FinalizingChild h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   \<exists> q. (\<forall> n. (n \<in>\<^sub>2 q of (vset_chosen r)) \<longrightarrow> slashed s n)"
proof -
  assume c0: "close_finalization s r rE FinalizingChild h0 v m0"
  assume c1: "close_finalization s r rE FinalizingChild h1 v m1"
  assume n01: "\<not> justified_with_root h0 v m0 s h1 v m1"
  then have not_same: "h0 \<noteq> h1 \<or> m0 \<noteq> m1"
    using justified_genesis by blast
  have non_trivial: "rE \<noteq> v"
    by (metis c0 c1 close_fj close_justification_is_justification n01 trivial_is_refl)
  have v0: "\<exists> q0 p0 pv0. voted_by s q0 (vset_chosen r) p0 pv0 h0 v"
    by (meson c0 casper.close_involves_vote_f casper_axioms close_fj non_trivial)
  have v1: "\<exists> q1 p1 pv1. voted_by s q1 (vset_chosen r) p1 pv1 h1 v"
    using c1 close_fj close_involves_vote_f non_trivial by blast
  have "m0 = m1"
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right c0 c1 close_fj close_justification_def close_justification_era le_less_Suc_eq linorder_neqE_nat non_trivial really_close_justification_zero)
  then have "h0 \<noteq> h1"
    using not_same by blast
  then show ?thesis
    by (meson casper.double_vote casper_axioms v0 v1)
qed

lemma find_first_change_one:
   "justified_with_root_with_n_switchings n r rE rM s h0 v m0 \<Longrightarrow>
    justified s r rE rM \<Longrightarrow>
    n = Suc 0 \<Longrightarrow>
    rM = FinalizingChild \<Longrightarrow>
    rE < v \<Longrightarrow>
    \<exists>r'. (\<exists>rE' m. justified s r' rE' m) \<and> vset_fwd r' = vset_chosen r"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case by (simp add: justified_switch_really_higher)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have n0: "n = 0" by blast
  have ee: "rE = e"
    using justified_on_finalization_n.hyps(1) justified_on_finalization_n.prems(3) n0 zero_justification_f by blast
  then have rr: "r = c"
    using justified_on_finalization_n.hyps(1) n0 trivial_is_refl0 by blast
  have vv: "vset_fwd h = vset_chosen c"
    by (meson casper.validator_changing_link_def casper_axioms justified_on_finalization_n.hyps(4))
  have "\<exists>rE' m. justified s h rE' m"
    using casper.justified_on_finalization casper_axioms ee justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) rr by fastforce
  then show ?case
    using rr vv by blast
qed

lemma find_first_change_two:
   "justified_with_root_with_n_switchings n r rE rM s h0 v m0 \<Longrightarrow>
    justified s r rE rM \<Longrightarrow>
    n = Suc (Suc 0) \<Longrightarrow>
    rM = FinalizingChild \<Longrightarrow>
    rE < v \<Longrightarrow>
    \<exists>r'. (\<exists>rE' m. justified s r' rE' m) \<and> vset_fwd r' = vset_chosen r"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    using justified_switch_really_higher by blast
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (smt One_nat_def Suc_inject find_first_change_one justified_switch_really_higher zero_less_one)
qed

lemma close_finalizations_cause_slashing_f_chosen_becomes_inner :
  " close_justification s r rE FinalizingChild h0 v m0 \<Longrightarrow>
    justified s r rE FinalizingChild \<Longrightarrow>
    rE < v \<Longrightarrow>
    \<exists>r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> (vset_fwd r' = vset_chosen r)"
  by (smt One_nat_def casper.close_justification_def casper_axioms find_first_change_one find_first_change_two nat_neq_iff numeral_2_eq_2 zero_justification_f)

lemma close_finalizations_cause_slashing_f_chosen_becomes :
  " close_finalization s r rE FinalizingChild h0 v m0 \<Longrightarrow>
    close_finalization s r rE FinalizingChild h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   justified s r rE FinalizingChild \<Longrightarrow>
    \<exists>r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> (vset_fwd r' = vset_chosen r)"
  by (smt Suc_eq_plus1 Suc_less_eq casper.close_justification_def casper_axioms close_finalizations_cause_slashing_f_chosen_becomes_inner close_fj close_justification_is_justification less_Suc_eq trivial_is_refl zero_justification_f)

lemma close_finalizations_cause_slashing_f :
  " close_finalization s r rE FinalizingChild h0 v m0 \<Longrightarrow>
    close_finalization s r rE FinalizingChild h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   justified s r rE FinalizingChild \<Longrightarrow>
    \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof -
  assume a0: "close_finalization s r rE FinalizingChild h0 v m0"
  assume a1: "close_finalization s r rE FinalizingChild h1 v m1"
  assume j0: "\<not> justified_with_root h0 v m0 s h1 v m1"
  assume j1: "\<not> justified_with_root h1 v m1 s h0 v m0"
  assume j: "justified s r rE FinalizingChild"
  obtain r' where r'P: "(\<exists>rE'. Ex (justified s r' rE')) \<and> (vset_fwd r' = vset_chosen r)"
    using a0 a1 close_finalizations_cause_slashing_f_chosen_becomes j j0 j1 by blast
  have sl_orig: "\<exists> q. (\<forall> n. (n \<in>\<^sub>2 q of (vset_chosen r)) \<longrightarrow> slashed s n)"
    using a0 a1 close_finalizations_cause_slashing_f_chosen j j0 j1 by blast
  show ?thesis
  proof -
    obtain dd :: 'd where
      "one_third_of_fwd_slashed s r' dd"
      by (metis (no_types) one_third_of_fwd_slashed_def r'P sl_orig)
    then show ?thesis
      using one_third_of_fwd_or_bwd_slashed_def r'P by blast
  qed
qed

lemma close_finalizations_cause_slashing :
  "close_finalization s r rE rM h0 v m0 \<Longrightarrow>
   close_finalization s r rE rM h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
   \<exists> q r' rE' rM'. justified s r' rE' rM' \<and> one_third_of_fwd_or_bwd_slashed s r' q"
  apply(cases rM; clarsimp)
   apply (simp add: close_finalizations_cause_slashing_u)
  by (simp add: close_finalizations_cause_slashing_f)

lemma small_accountable_safety_equal :
  "small_fork s r rE rM h0 v m0 h1 v m1 \<Longrightarrow>
   \<exists> q r' rE' rM' . justified s r' rE' rM' \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof -
  assume a: "small_fork s r rE rM h0 v m0 h1 v m1"
  have dif0: "\<not> justified_with_root h0 v m0 s h1 v m1"
    using a casper.justification_fork_with_root_def casper.small_fork_def casper_axioms by fastforce
  have dif1: "\<not> justified_with_root h1 v m1 s h0 v m0"
    using a casper.small_fork_def casper_axioms justification_fork_with_root_def by fastforce
  have c0: "close_finalization s r rE rM h0 v m0"
    by (meson a casper.small_fork_has_close_justification casper_axioms)
  have c1: "close_finalization s r rE rM h1 v m1"
    using a small_fork_has_close_justification small_fork_sym by blast
  have j: "justified s r rE rM"
    using a casper.small_fork_def casper_axioms justification_fork_with_root_def by fastforce
  show ?thesis
    using dif0 dif1 c0 c1 j close_finalizations_cause_slashing by blast
qed

lemma finalized_zero_has_child:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   n = 0 \<Longrightarrow>
   rM = Usual \<Longrightarrow>
   \<exists>q1 ch1. voted_by s q1 (vset_fwd r) h1 v1 ch1 (Suc v1)"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then have v: "\<exists>q1. voted_by s q1 (vset_fwd new) orig origE new (Suc origE)"
    by (metis Suc_eq_plus1 usual_link_def voted_by_both_def voted_by_fwd_def)
  have l: "vset_fwd new = vset_fwd orig"
    by (metis under_usual_link_n.hyps(2) usual_link_def)
  have "vset_fwd r = vset_fwd orig"
    using under_usual_link_n.hyps(1) under_usual_link_n.prems(1) under_usual_link_n.prems(2) zero_switching_means by blast
  then have v: "\<exists>q1. voted_by s q1 (vset_fwd r) orig origE new (Suc origE)"
    using l v by auto
  then show ?case by blast
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then have v: "\<exists>q1. voted_by s q1 (vset_bwd h) c e h (Suc e)"
    by (metis Suc_eq_plus1 casper.validator_changing_link_def casper_axioms voted_by_both_def voted_by_bwd_def)
  have eq: "vset_fwd r = vset_bwd h"
    by (metis casper.validator_changing_link_def casper_axioms under_changing_link_n.hyps(1) under_changing_link_n.hyps(2) under_changing_link_n.prems(1) under_changing_link_n.prems(2) zero_switching_means)
  then show ?case
    using v by auto
qed

lemma finalized_one_has_child:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   m1 = Usual \<Longrightarrow>
   rM = Usual \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
   rE < v1 \<Longrightarrow>
   \<exists>q1 ch1. voted_by s q1 (vset_fwd r) h1 v1 ch1 (Suc v1)"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    by (metis Suc_eq_plus1 casper.voted_by_both_def casper.voted_by_bwd_def casper_axioms one_switching_means usual_link_def)
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case by blast
qed

lemma finalized_ending_u:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   m1 = Usual \<Longrightarrow>
   \<exists>q0 q1. usual_link s q0 q1 h1 v1 child (Suc v1)"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    by (metis Suc_eq_plus1)
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case by blast
qed

lemma finalized_ending_f:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   m1 = FinalizingChild \<Longrightarrow>
   \<exists>q0 q1. validator_changing_link s q0 q1 h1 v1 child (Suc v1)"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case by blast
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case by (metis Suc_eq_plus1) 
qed

(* think about adding a ch argument to close_finalization *)
lemma close_finalization_has_child_usually_linked:
"close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
 m1 = Usual \<Longrightarrow>
 \<exists> q0 q1 ch1. usual_link s q0 q1 h1 v1 ch1 (v1 + 1)"
  apply(auto simp add: close_finalization_def)
  using finalized_ending_u apply blast
    apply (meson casper.finalized_ending_u casper_axioms)
   apply (meson casper.finalized_ending_u casper_axioms)
  by (meson casper.finalized_ending_u casper_axioms)

lemma close_finalization_has_child_changing_linked:
"close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
 m1 = FinalizingChild \<Longrightarrow>
 \<exists> q0 q1 ch1. validator_changing_link s q0 q1 h1 v1 ch1 (v1 + 1)"
  by (smt Suc_eq_plus1 Suc_lessD Suc_lessI casper.close_finalization_def casper_axioms close_fj close_justification_era diff_add_inverse finalized_ending_f order_le_less)

lemma close_finalization_has_child:
"close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
 rM = Usual \<Longrightarrow>
 \<exists> q1 ch1. voted_by s q1 (vset_fwd r) h1 v1 ch1 (v1 + 1)"
by (smt Mode.simps(1) One_nat_def Suc_eq_plus1 Suc_lessI casper.close_finalization_def casper_axioms finalized_one_has_child finalized_zero_has_child)

lemma surround_concrete:
  "voted_by s q0 vset orig origE new newE \<Longrightarrow>
   voted_by s q1 vset h1 v1 ch1 chE \<Longrightarrow>
   origE < v1 \<Longrightarrow>
   chE < newE \<Longrightarrow>
   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> slashed s n"
proof -
  assume v0: "voted_by s q0 vset orig origE new newE"
  assume v1: "voted_by s q1 vset h1 v1 ch1 chE"
  have both: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> (n \<in>\<^sub>1 q0 of vset) \<and> (n \<in>\<^sub>1 q1 of vset)"
    by (metis byz_quorums_axioms byz_quorums_def)
  then obtain q where qP: "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> (n \<in>\<^sub>1 q0 of vset) \<and> (n \<in>\<^sub>1 q1 of vset)"
    by blast
  have vote0: "\<forall> n.  (n \<in>\<^sub>2 q of vset) \<longrightarrow> vote_msg s n new newE origE"
    by (meson casper.voted_by_def casper_axioms qP v0)
  have vote1: "\<forall> n.  (n \<in>\<^sub>2 q of vset) \<longrightarrow> vote_msg s n ch1 chE v1"
    by (meson casper.voted_by_def casper_axioms qP v1)
  assume orig_v1: " origE < v1"
  assume ch_new: "chE < newE"
  show ?thesis
    by (meson ch_new orig_v1 slashed_def slashed_surround_def v1 vote0 vote1 voted_by_higher)
qed

lemma close_j_f_u_zero:
   "justified_with_root_with_n_switchings n r rE rM s h0 v0 m0 \<Longrightarrow>
    close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
    n = 0 \<Longrightarrow>
    rM = Usual \<Longrightarrow>
    v1 < v0 \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
    justified s r rE Usual \<Longrightarrow>
    \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case
    using close_fj close_justification_era leD by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then have f1: "close_finalization s r rE mode h1 v1 m1" by blast
  consider (a) "origE > v1" | (b) "origE = v1" | (c) "origE < v1"
    using antisym_conv3 by blast
  then show ?case
  proof cases
    case a
    then show ?thesis
      using usual_justification usual_justification_n.hyps(2) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_justification_n.prems(5) usual_justification_n.prems(6) by blast
  next
    case b
    have orignt: "rE < origE"
      by (metis b casper.justifies_higher casper.trivial_is_refl casper.usual_justification_n casper_axioms close_fj forget_n_switchings le_neq_implies_less usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(1) usual_justification_n.prems(5))
    have v0: "\<exists> q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 orig origE"
      by (metis orignt nat_neq_iff usual_justification_n.hyps(1) usual_justification_n.prems(2) usual_justification_n.prems(3) zero_switching_involves_root_vote)
    have v1: "\<exists> q1 p1 pv1. voted_by s q1 (vset_fwd r) p1 pv1 h1 v1"
      by (smt b casper.trivial_is_refl casper_axioms close_fj close_involves_vote trivial_is_refl0 usual_justification_n.hyps(1) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_justification_n.prems(3) v0)
    have diff: "orig \<noteq> h1"
      by (metis Mode.simps(1) Suc_eq_plus1 Suc_lessI b casper.justified_genesis casper.usual_justification casper_axioms close_finalization_def orignt really_close_justification_zero usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(1) usual_justification_n.prems(5))
    have sl: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd r)) \<longrightarrow> slashed s n"
      using b casper.double_vote casper_axioms diff v0 v1 by fastforce
    show ?thesis
      by (metis Mode.simps(1) Suc_eq_plus1 Suc_lessI b casper.close_justification_def casper_axioms close_finalizations_cause_slashing_u_j close_fj diff justified_back_unique orignt really_close_justification_zero usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_justification_n.prems(6))
  next
    case c
    then show ?thesis
    proof(cases "newE > v1 + 1")
      case True (* surrounding rule *)
      have v0: "\<exists> q0. voted_by s q0 (vset_fwd r) orig origE new newE"
        by (metis usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_link_def voted_by_both_def voted_by_fwd_def zero_switching_means)
      have v1: "\<exists> q1 ch1. voted_by s q1 (vset_fwd r) h1 v1 ch1 (v1 + 1)"
        using casper.close_finalization_has_child casper_axioms usual_justification_n.prems(1) usual_justification_n.prems(3) by fastforce
      have sl: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd r)) \<longrightarrow> slashed s n"
        using True c surround_concrete v0 v1 by blast
      then obtain q where qP: "\<forall> n. (n \<in>\<^sub>2 q of (vset_fwd r)) \<longrightarrow> slashed s n"
        by blast
      then have "one_third_of_fwd_or_bwd_slashed s r q"
        by (simp add: one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def)
      then show ?thesis
        using usual_justification_n.prems(6) by blast
    next
      case False (* double rule *)
      have v0: "\<exists> q0. voted_by s q0 (vset_fwd r) orig origE new newE"
        by (metis usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_link_def voted_by_both_def voted_by_fwd_def zero_switching_means)
      show ?thesis
      proof(cases m1)
        case Usual
        have "close_finalization s r rE mode h1 v1 m1" using f1 by blast
        have v1: "\<exists> q0 q1 ch1. usual_link s q0 q1 h1 v1 ch1 (v1 + 1)"
          using Usual close_finalization_has_child_usually_linked usual_justification_n.prems(1) by blast
        then obtain ch1 q0 q1 where ch1P: "usual_link s q0 q1 h1 v1 ch1 (v1 + 1)"
          by blast
        then have v_fwd: "voted_by s q0 (vset_fwd ch1) h1 v1 ch1 (v1 + 1)"
          by (simp add: usual_link_def voted_by_both_def voted_by_fwd_def)
        have eq: "newE = v1 + 1"
          using False usual_justification_n.prems(4) by auto
        have v_0: "\<exists> q2 q3. usual_link s q2 q3 orig origE new newE"
          using usual_justification_n.hyps(4) by blast
        then obtain q2 q3 where q23P: "usual_link s q2 q3 orig origE new newE"
          by blast
        have vr1: "\<exists> q. voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)"
          by (metis Mode.simps(1) One_nat_def casper.close_justification_def casper.zero_switching_means casper_axioms ch1P close_fj one_switching_means usual_justification_n.prems(1) usual_justification_n.prems(3) usual_link_def v_fwd voted_by_both_def voted_by_bwd_def)
        have vr0: "\<exists> q. voted_by s q (vset_fwd r) orig origE new newE"
          by (simp add: v0)
        have fwr_sl: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd r)) \<longrightarrow> slashed s n"
          by (metis c casper.double_vote casper_axioms eq nat_neq_iff v0 vr1)
        have sl: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
          using fwr_sl one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def by blast
        then show ?thesis
          using usual_justification_n.prems(6) by blast
      next
        case FinalizingChild
        have "close_finalization s r rE mode h1 v1 m1" using f1 by blast
        have v1: "\<exists> q0 q1 ch1. validator_changing_link s q0 q1 h1 v1 ch1 (v1 + 1)"
          using FinalizingChild close_finalization_has_child_changing_linked usual_justification_n.prems(1) by blast
        then obtain ch1 q0 q1 where ch1P: "validator_changing_link s q0 q1 h1 v1 ch1 (v1 + 1)"
          by blast
        then have v_bwd: "voted_by s q1 (vset_bwd ch1) h1 v1 ch1 (v1 + 1)"
          using validator_changing_link_def voted_by_both_def voted_by_bwd_def by blast
        have eq: "newE = v1 + 1"
          using False usual_justification_n.prems(4) by auto
        have v_0: "\<exists> q2 q3. usual_link s q2 q3 orig origE new newE"
          using usual_justification_n.hyps(4) by blast
        then obtain q2 q3 where q23P: "usual_link s q2 q3 orig origE new newE"
          by blast
        have vr1: "\<exists> q. voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)"
          by (smt FinalizingChild Mode.simps(1) One_nat_def add.right_neutral add_Suc_right casper.close_justification_def casper.zero_switching_means casper_axioms ch1P close_fj diff_add_inverse2 less_Suc_eq less_diff_conv usual_justification_n.prems(1) usual_justification_n.prems(3) v_bwd validator_changing_link_def)
        have vr0: "\<exists> q. voted_by s q (vset_fwd r) orig origE new newE"
          by (simp add: v0)
        have fwr_sl: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd r)) \<longrightarrow> slashed s n"
          by (metis c casper.double_vote casper_axioms eq nat_neq_iff v0 vr1)
        have sl: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
          using fwr_sl one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def by blast
        then show ?thesis
          using usual_justification_n.prems(6) by blast
      qed
    qed
  qed
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case by linarith
qed

lemma finalizing_justification_is_like_inner_u0:
  "justified_with_root_with_n_switchings n r rE rM s h1 v1 m1 \<Longrightarrow>
   rE < v1 \<Longrightarrow>
   m1 = Usual \<Longrightarrow>
   n = 0 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 < v1"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case
    by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have lt: "origE + 1 < newE"
    by (metis Mode.simps(1) One_nat_def Suc_diff_Suc Suc_eq_plus1 not_less_less_Suc_eq usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(2) usual_link_higher zero_less_diff)
  have v: "\<exists> q. voted_by s q (vset_fwd new) orig origE new newE"
    by (meson casper.usual_link_def casper.voted_by_both_def casper_axioms usual_justification_n.hyps(4) voted_by_fwd_def)
  then show ?case
    by (smt Mode.exhaust casper.usual_justification_n casper.zero_justification_f casper_axioms lt nat_neq_iff usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(3) zero_switching_means)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by linarith
qed

lemma finalizing_justification_is_like_inner_u:
  "justified_with_root_with_n_switchings n r rE rM s h1 v1 m1 \<Longrightarrow>
   m1 = Usual \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 < v1"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case
    by linarith
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then have diff: "newE - origE > 1"
    by (metis Mode.simps(1) One_nat_def Suc_lessI usual_link_higher zero_less_diff)
  have u: "usual_link s q0 q1 orig origE new newE"
    by (metis add.commute diff le_add_diff_inverse2 less_or_eq_imp_le usual_justification_n.hyps(4) usual_link_higher)
  have v: "voted_by s q1 (vset_bwd new) orig origE new newE "
    by (meson casper.usual_link_def casper.voted_by_both_def casper_axioms usual_justification_n.hyps(4) voted_by_bwd_def)
  have eq: "vset_fwd r = vset_bwd new"
    by (metis (full_types) casper.after_one_switching casper.usual_link_def casper_axioms not_finalizing one_switching_means usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(2))
  then show ?case
    using diff v by fastforce
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have diff: "ee - e > 1"
    by (metis Mode.simps(1) One_nat_def Suc_lessI validator_changing_link_higher zero_less_diff)
  have u: "validator_changing_link s q0 q1 c e h ee"
    by (metis add.commute diff justified_on_finalization_n.hyps(4) le_add_diff_inverse2 less_imp_le_nat validator_changing_link_higher)
  have v: "voted_by s q1 (vset_bwd h) c e h ee "
    by (meson casper.validator_changing_link_def casper.voted_by_both_def casper_axioms justified_on_finalization_n.hyps(4) voted_by_bwd_def)
  have eq: "vset_fwd r = vset_bwd h"
    by (smt Suc_inject casper.trivial_is_refl0 casper.validator_changing_link_def casper.zero_justification_f casper_axioms justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(2) not_finalizing zero_switching_means)
  then show ?case
    using diff v by fastforce
qed



lemma finalizing_justification_is_like_inner:
  "justified_with_root_with_n_switchings n r rE rM s h1 v1 m1 \<Longrightarrow>
   m1 = FinalizingChild \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 = v1"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then have diff: "newE - origE = 1"
    using Mode.simps(1) by presburger
  have u: "usual_link s q0 q1 orig origE new (origE + 1)"
    by (metis add.commute diff le_add_diff_inverse2 less_or_eq_imp_le usual_justification_n.hyps(4) usual_link_higher)
  have v: "voted_by s q1 (vset_bwd new) orig origE new newE "
    by (meson casper.usual_link_def casper.voted_by_both_def casper_axioms usual_justification_n.hyps(4) voted_by_bwd_def)
  have eq: "vset_fwd r = vset_bwd new"
    by (metis (full_types) casper.after_one_switching casper.usual_link_def casper_axioms not_finalizing one_switching_means usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(2))
  then show ?case
    using diff v by fastforce
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have diff: "ee - e = 1"
    using Mode.simps(1) by presburger
  have u: "validator_changing_link s q0 q1 c e h (e + 1)"
    by (metis add.commute diff justified_on_finalization_n.hyps(4) le_add_diff_inverse2 less_imp_le_nat validator_changing_link_higher)
  have v: "voted_by s q1 (vset_bwd h) c e h ee "
    by (meson casper.validator_changing_link_def casper.voted_by_both_def casper_axioms justified_on_finalization_n.hyps(4) voted_by_bwd_def)
  have eq: "vset_fwd r = vset_bwd h"
    by (smt Suc_inject casper.trivial_is_refl0 casper.validator_changing_link_def casper.zero_justification_f casper_axioms justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(2) not_finalizing zero_switching_means)
  then show ?case
    using diff v by fastforce
qed


lemma finalizing_justification_is_like_u0:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   m1 = Usual \<Longrightarrow>
   n = 0 \<Longrightarrow>
   rE < v1 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 < v1"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    using finalizing_justification_is_like_inner_u0 by blast
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    by blast
qed

lemma finalizing_justification_is_like_u:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   m1 = Usual \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 < v1"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    using finalizing_justification_is_like_inner_u by blast
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    by blast
qed

lemma finalizing_justification_is_like0_j:
  "justified_with_root_with_n_switchings n r rE rM s h1 v1 m1 \<Longrightarrow>
   m1 = FinalizingChild \<Longrightarrow>
   n = 0 \<Longrightarrow>
   rE < v1 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 = v1"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case
    by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then have "\<exists> q. voted_by s q (vset_fwd r) orig origE new newE"
  proof -
    have "mode = Usual \<or> mode = FinalizingChild"
      by (metis (no_types) Mode.exhaust)
    then show ?thesis
      by (metis (no_types) refl_inv usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.prems(2) usual_link_def voted_by_both_def voted_by_fwd_def zero_justification_f zero_switching_means)
  qed
  moreover have "origE + 1 = newE"
    using Mode.simps(1) usual_justification_n.hyps(5) usual_justification_n.prems(1) by presburger
  then show ?case
    using calculation by blast
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case  by linarith
qed

lemma finalizing_justification_is_like0:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   m1 = FinalizingChild \<Longrightarrow>
   n = 0 \<Longrightarrow>
   rE < v1 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 = v1"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    by blast
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    using finalizing_justification_is_like0_j by blast
qed

lemma finalizing_justification_is_like:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   m1 = FinalizingChild \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
  \<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 = v1"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  show ?case
    using under_usual_link_n.prems(1) by blast
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    using finalizing_justification_is_like_inner by blast
qed


lemma diff_conc3:
    "justified_with_root_with_n_switchings 0 r rE Usual s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new v1 \<Longrightarrow>
     newM = (if v1 - origE = Suc 0 then FinalizingChild else Usual) \<Longrightarrow>
     newE = v1 \<Longrightarrow>
     justified s r rE Usual \<Longrightarrow>
     finalized_with_root_with_n_switchings (Suc 0) r rE Usual s h1 child v1 m1 \<Longrightarrow>
     newM \<noteq> m1 \<Longrightarrow> \<exists>q r'. (\<exists>rE' a. justified s r' rE' a) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof(cases newM)
  case Usual
  assume m1e: "newM \<noteq> m1"
  assume ff: "finalized_with_root_with_n_switchings (Suc 0) r rE Usual s h1 child v1 m1"
  have fff: "finalized_with_root_with_n_switchings (Suc 0) r rE Usual s h1 child v1 FinalizingChild"
    by (metis Mode.exhaust Usual ff m1e)
  then have f: "\<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 = v1"
    using finalizing_justification_is_like by blast
  assume ul: "usual_link s q0 q1 orig origE new v1"
  assume newMarith: "newM = (if v1 - origE = Suc 0 then FinalizingChild else Usual)"
  assume oj: "justified_with_root_with_n_switchings 0 r rE Usual s orig origE Usual"
  have "\<exists> q. voted_by s q (vset_fwd new) orig origE new v1"
    by (meson casper.usual_link_def casper.voted_by_fwd_def casper_axioms ul voted_by_both_def)
  moreover have "vset_fwd r = vset_fwd new"
    by (metis casper.zero_switching_means casper_axioms oj ul usual_link_def)
  moreover have "origE + 1 < v1"
    by (metis Mode.simps(1) Suc_diff_Suc Suc_eq_plus1 Usual add_diff_inverse_nat diff_add_0 newMarith ul usual_link_higher)
  ultimately have e: "\<exists> q. voted_by s q (vset_fwd r) orig origE new v1 \<and> origE + 1 < v1"
    by simp
  have ss: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
    by (metis casper.double_vote casper_axioms e f nat_neq_iff)
  have sl: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
    using one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def ss by blast
  assume "justified s r rE Usual"
  then show ?thesis 
    using sl by blast
next
  case FinalizingChild
  assume m1e: "newM \<noteq> m1"
  assume ff: "finalized_with_root_with_n_switchings (Suc 0) r rE Usual s h1 child v1 m1"
  have fff: "finalized_with_root_with_n_switchings (Suc 0) r rE Usual s h1 child v1 Usual"
    by (metis FinalizingChild Mode.exhaust ff m1e)
  then have f: "\<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 < v1"
    using finalizing_justification_is_like_u by blast
  assume ul: "usual_link s q0 q1 orig origE new v1"
  assume newMarith: "newM = (if v1 - origE = Suc 0 then FinalizingChild else Usual)"
  assume oj: "justified_with_root_with_n_switchings 0 r rE Usual s orig origE Usual"
  have "\<exists> q. voted_by s q (vset_fwd new) orig origE new v1"
    by (meson casper.usual_link_def casper.voted_by_fwd_def casper_axioms ul voted_by_both_def)
  moreover have "vset_fwd r = vset_fwd new"
    by (metis casper.zero_switching_means casper_axioms oj ul usual_link_def)
  moreover have "origE + 1 = v1"
    using FinalizingChild Mode.simps(1) newMarith by presburger
  ultimately have e: "\<exists> q. voted_by s q (vset_fwd r) orig origE new v1 \<and> origE + 1 = v1"
    by simp
  have ss: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
    by (metis casper.double_vote casper_axioms e f nat_neq_iff)
  have sl: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
    using one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def ss by blast
  assume "justified s r rE Usual"
  then show ?thesis 
    using sl by blast
qed

lemma diff_conc2:
   "justified_with_root_with_n_switchings 0 r rE Usual s orig origE origM \<Longrightarrow>
    usual_link s q0 q1 orig origE new v1 \<Longrightarrow>
    newE = v1 \<Longrightarrow>
    justified s r rE Usual \<Longrightarrow>
    finalized_with_root_with_n_switchings (Suc 0) r rE Usual s h1 child v1 m1 \<Longrightarrow>
    new \<noteq> h1 \<Longrightarrow> \<exists>q r'. (\<exists>rE' a. justified s r' rE' a) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof-
  assume j: "justified_with_root_with_n_switchings 0 r rE Usual s orig origE origM"
  assume ul: "usual_link s q0 q1 orig origE new v1"
  have v_left:"\<exists> q. voted_by s q (vset_fwd new) orig origE new v1"
    by (meson casper.voted_by_both_def casper_axioms ul usual_link_def voted_by_fwd_def)
  have v_left2: "\<exists> q. voted_by s q (vset_fwd r) orig origE new v1"
    by (metis casper.usual_link_def casper.zero_switching_means casper_axioms j ul v_left)
  assume f: "finalized_with_root_with_n_switchings (Suc 0) r rE Usual s h1 child v1 m1"
  have v_right: "\<exists> q p pE. voted_by s q (vset_fwd r) p pE h1 v1"
    by (metis casper.forget_n_switchings casper_axioms f fjn j justifies_higher leD one_switching_involves_root_vote v_left2 voted_by_higher)
  assume diff: "new \<noteq> h1 "
  have ss: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
    by (meson casper.double_vote casper_axioms diff v_left2 v_right)
  have sl: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
    by (metis casper.zero_switching_means casper_axioms diff double_vote j one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def ul usual_link_def v_left v_right)
  assume jj: "justified s r rE Usual"
  show ?thesis
    using jj sl by auto
qed

lemma diff_concl1:
    "justified_with_root_with_n_switchings 0 r rE Usual s orig origE origM \<Longrightarrow>
     usual_link s q0 q1 orig origE new v1 \<Longrightarrow>
     newM = (if v1 - origE = Suc 0 then FinalizingChild else Usual) \<Longrightarrow>
     newE = v1 \<Longrightarrow>
     rE < v1 \<Longrightarrow>
     justified s r rE Usual \<Longrightarrow>
     finalized_with_root_with_n_switchings 0 r rE Usual s h1 child v1 m1 \<Longrightarrow>
     newM \<noteq> m1 \<Longrightarrow> \<exists>q r'. (\<exists>rE' a. justified s r' rE' a) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof(cases newM)
  case Usual
  assume m1e: "newM \<noteq> m1"
  assume ff: "finalized_with_root_with_n_switchings 0 r rE Usual s h1 child v1 m1"
  have fff: "finalized_with_root_with_n_switchings 0 r rE Usual s h1 child v1 FinalizingChild"
    by (metis Mode.exhaust Usual ff m1e)
  then have f: "\<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 = v1"
    by (metis Mode.simps(1) casper.fjn casper.forget_n_switchings casper_axioms finalizing_justification_is_like0 justifies_higher order.strict_iff_order refl_inv)
  assume ul: "usual_link s q0 q1 orig origE new v1"
  assume newMarith: "newM = (if v1 - origE = Suc 0 then FinalizingChild else Usual)"
  assume oj: "justified_with_root_with_n_switchings 0 r rE Usual s orig origE origM"
  have "\<exists> q. voted_by s q (vset_fwd new) orig origE new v1"
    by (meson casper.usual_link_def casper.voted_by_fwd_def casper_axioms ul voted_by_both_def)
  moreover have "vset_fwd r = vset_fwd new"
    by (metis casper.zero_switching_means casper_axioms oj ul usual_link_def)
  moreover have "origE + 1 < v1"
    by (metis Mode.simps(1) Suc_diff_Suc Suc_eq_plus1 Usual add_diff_inverse_nat diff_add_0 newMarith ul usual_link_higher)
  ultimately have e: "\<exists> q. voted_by s q (vset_fwd r) orig origE new v1 \<and> origE + 1 < v1"
    by simp
  have ss: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
    by (metis casper.double_vote casper_axioms e f nat_neq_iff)
  have sl: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
    using one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def ss by blast
  assume "justified s r rE Usual"
  then show ?thesis 
    using sl by blast
next
  case FinalizingChild
  assume m1e: "newM \<noteq> m1"
  assume ff: "finalized_with_root_with_n_switchings 0 r rE Usual s h1 child v1 m1"
  assume lt: "rE < v1"
  have fff: "finalized_with_root_with_n_switchings 0 r rE Usual s h1 child v1 Usual"
    by (metis FinalizingChild Mode.exhaust ff m1e)
  then have f: "\<exists> q v1_src h1_src. voted_by s q (vset_fwd r) h1_src v1_src h1 v1 \<and> v1_src + 1 < v1"
    using lt finalizing_justification_is_like_u0 by blast
  assume ul: "usual_link s q0 q1 orig origE new v1"
  assume newMarith: "newM = (if v1 - origE = Suc 0 then FinalizingChild else Usual)"
  assume oj: "justified_with_root_with_n_switchings 0 r rE Usual s orig origE origM"
  have "\<exists> q. voted_by s q (vset_fwd new) orig origE new v1"
    by (meson casper.usual_link_def casper.voted_by_fwd_def casper_axioms ul voted_by_both_def)
  moreover have "vset_fwd r = vset_fwd new"
    by (metis casper.zero_switching_means casper_axioms oj ul usual_link_def)
  moreover have "origE + 1 = v1"
    using FinalizingChild Mode.simps(1) newMarith by presburger
  ultimately have e: "\<exists> q. voted_by s q (vset_fwd r) orig origE new v1 \<and> origE + 1 = v1"
    by simp
  have ss: "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
    by (metis casper.double_vote casper_axioms e f nat_neq_iff)
  have sl: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
    using one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def ss by blast
  assume "justified s r rE Usual"
  then show ?thesis 
    using sl by blast
qed

lemma diff_concl0:
    "justified_with_root_with_n_switchings 0 r rE Usual s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new v1 \<Longrightarrow>
     justified s r rE Usual \<Longrightarrow>
     finalized_with_root_with_n_switchings 0 r rE Usual s h1 child v1 m1 \<Longrightarrow>
     new \<noteq> h1 \<Longrightarrow> \<exists>q r'. (\<exists>rE' a. justified s r' rE' a) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof -
  assume j: "justified_with_root_with_n_switchings 0 r rE Usual s orig origE Usual"
  then have eq: "vset_fwd r = vset_fwd orig"
    using zero_switching_means by blast
  assume u: "usual_link s q0 q1 orig origE new v1"
  then have eq1: "vset_fwd r = vset_fwd new"
    by (simp add: eq usual_link_def)
  assume f: "finalized_with_root_with_n_switchings 0 r rE Usual s h1 child v1 m1"
  then have f1: "\<exists> q p pE. voted_by s q (vset_fwd r) p pE h1 v1"
    by (metis casper.forget_n_switchings casper_axioms fjn j justifies_higher leD u usual_link_higher zero_switching_involves_root_vote)
  have f2: "\<exists> q p pE. voted_by s q (vset_fwd r) p pE new v1"
    by (metis eq1 u usual_link_def voted_by_both_def voted_by_fwd_def)
  assume diff: "new \<noteq> h1"
  have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
    by (meson casper.double_vote casper_axioms diff f1 f2)
  then have slr: "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
    by (metis (no_types, lifting) casper.forget_n_switchings casper.justified_is_voted_bwd casper.usual_link_def casper.voted_by_both_def casper_axioms diff double_vote f fjn j justifies_higher leD one_third_of_bwd_slashed_def one_third_of_fwd_or_bwd_slashed_def u voted_by_bwd_def voted_by_higher zero_switching_means)
  assume "justified s r rE Usual"
  then show ?thesis
    using slr by blast
qed

lemma different_conclusion_at_same_epoch:
  "justified_with_root_with_n_switchings n r rE mode s c e origM \<Longrightarrow>
  close_finalization s r rE mode h1 v1 m1 \<Longrightarrow>
  e = v1 \<Longrightarrow>
  n = 0 \<Longrightarrow>
  rE < e \<Longrightarrow>
  c \<noteq> h1 \<or> origM \<noteq> m1 \<Longrightarrow>
  mode = Usual \<Longrightarrow>
  justified s r rE mode \<Longrightarrow>
  \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case
    by (meson casper.trivial_is_refl casper_axioms close_fj)
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    apply(auto simp add: close_finalization_def)
         apply (simp add: diff_concl0)
    using diff_concl0 apply blast
       apply (metis One_nat_def Suc_lessI casper.justifies_higher casper.usual_justification_n casper_axioms diff_is_0_eq' fjn forget_n_switchings le_neq_implies_less really_close_justification_zero usual_link_higher zero_less_diff)
    using diff_concl1 apply blast
    using diff_conc2 apply blast
    using diff_conc3 by blast

next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by(auto simp add: close_finalization_def)
qed

lemma fwd_slashed_means:
  "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd r)) \<longrightarrow> slashed s n \<Longrightarrow>
   \<exists>q. one_third_of_fwd_or_bwd_slashed s r q"
  by(auto simp add: one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def)

lemma close_j_f_u_one:
   "justified_with_root_with_n_switchings n r rE rM s h0 v0 m0 \<Longrightarrow>
    n = Suc 0 \<Longrightarrow>
    close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
    rM = Usual \<Longrightarrow>
    v1 < v0 \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
    justified s r rE Usual \<Longrightarrow>
    \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case
    using close_fj close_justification_is_justification by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have inv: "    \<not> justified_with_root new newE newM s h1 v1 m1"
    using justifies_higher leD usual_justification_n.prems(4) by blast
  consider (reduce) "v1 < origE" | (dblA) "v1 = origE" | (dblB) "origE < v1 \<and> newE = v1 + 1" | (surround) "origE < v1 \<and> v1 + 1 < newE"
    using usual_justification_n.prems(4) by linarith
  then show ?case proof cases
    case reduce
    then show ?thesis
      using usual_justification usual_justification_n.hyps(2) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_justification_n.prems(5) usual_justification_n.prems(6) by blast
  next
    case dblA
    then show ?thesis
      by (smt Mode.simps(1) One_nat_def Suc_eq_plus1 Suc_lessI casper.close_finalizations_cause_slashing_u_j casper.close_justification_def casper_axioms close_fj justified_back_unique justified_switch_really_higher really_close_justification_zero usual_justification usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_justification_n.prems(5) usual_justification_n.prems(6) zero_less_one)
  next
    case dblB
    have vv0: "\<exists> q. voted_by s q (vset_bwd new) orig origE new newE"
      by (meson usual_justification_n.hyps(4) usual_link_def voted_by_both_def voted_by_bwd_def)
    then have vote0: "\<exists> q. voted_by s q (vset_fwd r) orig origE new newE"
      by (metis casper.one_switching_means casper.usual_link_def casper_axioms usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(3))
    have vv1: "\<exists> q ch1. voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)"
      using close_finalization_has_child usual_justification_n.prems(2) usual_justification_n.prems(3) by blast
    have diff: "origE \<noteq> v1"
      using dblB by blast
    have "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd r)) \<longrightarrow> slashed s n"
      using casper.double_vote casper_axioms dblB vote0 vv1 by fastforce
    then have goal_sl: "\<exists>q. one_third_of_fwd_or_bwd_slashed s r q"
      using fwd_slashed_means by blast
    have j: "\<exists>rE' a. justified s r rE' a"
      using usual_justification_n.prems(6) by auto
    then show ?thesis
      using goal_sl by blast
  next
    case surround
    have vv1: "\<exists> q ch1. voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)"
      using casper.close_finalization_has_child casper_axioms usual_justification_n.prems(2) usual_justification_n.prems(3) by fastforce
    have vote0: "\<exists> q. voted_by s q (vset_fwd r) orig origE new newE"
      by (metis casper.usual_link_def casper.voted_by_both_def casper.voted_by_bwd_def casper_axioms one_switching_means usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(3))
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
      using surround surround_concrete vote0 vv1 by blast
    then show ?thesis
      using one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def usual_justification_n.prems(6) by blast
  qed
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then consider (reduce_zero) "v1 < e" | (dbl_a) "e = v1" | (dbl_b) "e < v1 \<and> ee = v1 + 1" | (surround) "e < v1 \<and> v1 + 1 < ee"
    by (metis discrete le_neq_implies_less nat_neq_iff)
  then show ?case
  proof cases
    case reduce_zero
    then have j0: "\<not> justified_with_root c e origM s h1 v1 m1"
      using justifies_higher leD by blast
    then have j1: "\<not> justified_with_root h1 v1 m1 s c e origM"
      using casper.justified_with_root.intros(3) casper_axioms justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(5) by fastforce
    then show ?thesis
      using close_j_f_u_zero j0 justified_on_finalization_n.hyps(1) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) justified_on_finalization_n.prems(6) reduce_zero by fastforce
  next
    case dbl_a
    have diff: "c \<noteq> h1 \<or> origM \<noteq> m1"
      using casper.justified_genesis casper.justified_on_finalization casper_axioms dbl_a justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(5) by fastforce
    have close0: "justified_with_root_with_n_switchings 0 r rE Usual s c e origM"
      using justified_on_finalization_n.hyps(1) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) by blast
    have close1: "close_finalization s r rE Usual h1 v1 m1"
      using justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) by blast
    have lt: "rE < e"
      by (metis Mode.simps(1) casper.forget_n_switchings casper.justifies_higher casper.refl_inv casper_axioms close0 justified_on_finalization_n.hyps(3) le_neq_implies_less)
    then show ?thesis
      using casper.different_conclusion_at_same_epoch casper_axioms close0 close1 dbl_a diff justified_on_finalization_n.prems(6) by fastforce
  next
    case dbl_b
    have vv0: "\<exists> q. voted_by s q (vset_bwd h) c e h ee"
      by (meson casper.validator_changing_link_def casper.voted_by_both_def casper_axioms justified_on_finalization_n.hyps(4) voted_by_bwd_def)
    have vv0': "\<exists> q. voted_by s q (vset_fwd r) c e h ee"
      by (metis Suc_inject justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) validator_changing_link_def vv0 zero_switching_means)
    have vv1: "\<exists> q ch1. voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)"
      using casper.close_finalization_has_child casper_axioms justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) by fastforce
    then obtain q ch1 where ch1P :"voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)" by blast
    have diff: "e \<noteq> v1"
      using dbl_b by blast
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
      using casper.double_vote casper_axioms ch1P dbl_b vv0' by fastforce
    have sl': "\<exists> q'. one_third_of_fwd_or_bwd_slashed s r q'"
      using one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def sl by blast
    then show ?thesis
      using justified_on_finalization_n.prems(6) by blast
  next
    case surround
    have vv0: "\<exists> q. voted_by s q (vset_bwd h) c e h ee"
      by (meson casper.validator_changing_link_def casper.voted_by_both_def casper_axioms justified_on_finalization_n.hyps(4) voted_by_bwd_def)
    have vv0': "\<exists> q. voted_by s q (vset_fwd r) c e h ee"
      by (metis Suc_inject justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) validator_changing_link_def vv0 zero_switching_means)
    have vv1: "\<exists> q ch1. voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)"
      using casper.close_finalization_has_child casper_axioms justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) by fastforce
    then obtain q ch1 where ch1P :"voted_by s q (vset_fwd r) h1 v1 ch1 (v1 + 1)" by blast
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r) \<longrightarrow> slashed s n"
      using ch1P surround surround_concrete vv0' by blast
    have sl' : "\<exists> q. one_third_of_fwd_or_bwd_slashed s r q"
      by (metis casper.one_third_of_fwd_slashed_def casper_axioms one_third_of_fwd_or_bwd_slashed_def sl)
    have ju: "\<exists> a. justified s r rE a"
      using justified_on_finalization_n.prems(6) by auto
    then show ?thesis
      using sl' by auto
  qed
qed

lemma close_justification_and_finalization_cause_slashing_u :
  "close_justification s r rE rM h0 v0 m0 \<Longrightarrow>
   close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
   rM = Usual \<Longrightarrow>
   v0 > v1 \<Longrightarrow>
   \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
   \<exists> q r' rE' rM'. justified s r' rE' rM' \<and> one_third_of_fwd_or_bwd_slashed s r' q"
  apply(auto simp add: close_justification_def)
    apply (simp add: close_j_f_u_zero)
   apply (simp add: close_j_f_u_zero)
  using close_j_f_u_one by blast

lemma close_too_close:
 "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
  n = 0 \<Longrightarrow>
  rM = FinalizingChild \<Longrightarrow>
  \<exists>q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 (Suc v1)"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    using refl_inv zero_justification_f by blast
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    by (metis Suc_eq_plus1 casper.validator_changing_link_def casper.voted_by_both_def casper_axioms trivial_is_refl0 voted_by_fwd_def zero_justification_f)
qed

lemma close_not_so_close:
  "finalized_with_root_with_n_switchings n r rE rM s h1 child v1 m1 \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
   rM = FinalizingChild \<Longrightarrow>
   \<exists>q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 (Suc v1)"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    by (metis Suc_eq_plus1 after_one_switching casper.voted_by_fwd_def casper_axioms usual_link_def voted_by_both_def)
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    by (metis Suc_eq_plus1 casper.after_one_switching casper.voted_by_both_def casper.voted_by_bwd_def casper_axioms validator_changing_link_def)
qed


lemma close_finalization_is_followed:
   "close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
    rM = FinalizingChild \<Longrightarrow>
   \<exists> q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 (v1 + 1)"
  apply(auto simp add: close_finalization_def)
       apply (simp add: close_too_close)
      apply (simp add: close_too_close)
  using close_not_so_close apply blast
    apply (simp add: close_not_so_close)
   apply (simp add: close_not_so_close)
  by (metis casper.finalized_ending_u casper.voted_by_both_def casper_axioms usual_link_def voted_by_bwd_def)

lemma close_j_f_f_one:
  "justified_with_root_with_n_switchings n r rE rM s h0 v0 m0 \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
   close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
   rM = FinalizingChild \<Longrightarrow>
   v1 < v0 \<Longrightarrow>
(*   \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow> *)
   \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
   \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  consider (reduce) "v1 < origE" | (dbl_a) "origE = v1" | (dbl_b) "origE < v1 \<and> newE = v1 + 1" | (surround) "origE < v1 \<and> newE \<noteq> v1 + 1"
    using less_linear by blast
  then show ?case proof cases
    case reduce
    then show ?thesis
      using usual_justification usual_justification_n.hyps(2) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_justification_n.prems(5) usual_justification_n.prems(6) by blast
  next
    case dbl_a
    have aux: "\<not> justified_with_root new newE newM s h1 v1 m1"
      using justifies_higher leD usual_justification_n.prems(4) by blast
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_chosen r) \<longrightarrow> slashed s n"
      by (metis Mode.simps(1) One_nat_def Suc_eq_plus1 Suc_leI casper.close_finalization_def casper.close_finalizations_cause_slashing_f_chosen casper.close_fj casper.close_involves_vote_f casper.justified_with_root.intros(2) casper.one_switching_involves_root_vote_f casper.really_close_justification_zero casper_axioms dbl_a double_vote justified_switch_really_higher order.strict_iff_order usual_justification_n.hyps(1) usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_justification_n.prems(3) usual_justification_n.prems(5) zero_less_one)
    have used: "\<exists> r' rE' a. justified s r' rE' a \<and> vset_fwd r' = vset_chosen r"
      using find_first_change_one justified_switch_really_higher usual_justification_n.hyps(1) usual_justification_n.prems(1) usual_justification_n.prems(3) usual_justification_n.prems(6) by fastforce
    then obtain r' rE' a where jjj: "justified s r' rE' a \<and> vset_fwd r' = vset_chosen r" by blast
    have sl'': "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r') \<longrightarrow> slashed s n"
      by (simp add: jjj sl)
    then have "\<exists> q. one_third_of_fwd_slashed s r' q"
      by (simp add: one_third_of_fwd_slashed_def)
    then have sl': "\<exists> q. one_third_of_fwd_or_bwd_slashed s r' q"
      using one_third_of_fwd_or_bwd_slashed_def by blast
    then show ?thesis using jjj by blast
  next
    case dbl_b
    have v0: "   \<exists> q. voted_by s q (vset_chosen r) orig origE new newE"
      by (metis after_one_switching casper.usual_link_def casper.voted_by_fwd_def casper_axioms usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(3) voted_by_both_def)
    have v1: "   \<exists> q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 (v1 + 1)"
      using close_finalization_is_followed usual_justification_n.prems(2) usual_justification_n.prems(3) by blast
    have diff: "origE \<noteq> v1"
      using dbl_b by blast
    have eq: "newE = v1 + 1"
      using dbl_b by auto
    have v1': "   \<exists> q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 newE"
      using eq v1 by blast
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_chosen r) \<longrightarrow> slashed s n"
      using diff double_vote v0 v1' by blast
    have used: "\<exists> r' rE' a. justified s r' rE' a \<and> vset_fwd r' = vset_chosen r"
      using find_first_change_one justified_switch_really_higher usual_justification_n.hyps(1) usual_justification_n.prems(1) usual_justification_n.prems(3) usual_justification_n.prems(6) by fastforce
    then obtain r' rE' a where jjj: "justified s r' rE' a \<and> vset_fwd r' = vset_chosen r" by blast
    have sl'': "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r') \<longrightarrow> slashed s n"
      by (simp add: jjj sl)
    then have "\<exists> q. one_third_of_fwd_slashed s r' q"
      by (simp add: one_third_of_fwd_slashed_def)
    then have sl': "\<exists> q. one_third_of_fwd_or_bwd_slashed s r' q"
      using one_third_of_fwd_or_bwd_slashed_def by blast
    then show ?thesis
      using jjj by blast
  next
    case surround
    have v0: "   \<exists> q. voted_by s q (vset_chosen r) orig origE new newE"
      by (metis after_one_switching casper.usual_link_def casper.voted_by_fwd_def casper_axioms usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(3) voted_by_both_def)
    have v1: "   \<exists> q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 (v1 + 1)"
      using close_finalization_is_followed usual_justification_n.prems(2) usual_justification_n.prems(3) by blast
    have diff: "origE < v1"
      by (simp add: surround)
    have eq: "newE > v1 + 1"
      using surround usual_justification_n.prems(4) by auto
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_chosen r) \<longrightarrow> slashed s n"
      by (metis (no_types, lifting) diff discrete double_vote le_antisym linorder_not_less surround_concrete usual_justification_n.prems(4) v0 v1)
    have used: "\<exists> r' rE' a. justified s r' rE' a \<and> vset_fwd r' = vset_chosen r"
      using find_first_change_one justified_switch_really_higher usual_justification_n.hyps(1) usual_justification_n.prems(1) usual_justification_n.prems(3) usual_justification_n.prems(7) by fastforce
    then obtain r' rE' a where jjj: "justified s r' rE' a \<and> vset_fwd r' = vset_chosen r" by blast
    have sl'': "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r') \<longrightarrow> slashed s n"
      by (simp add: jjj sl)
    then have "\<exists> q. one_third_of_fwd_slashed s r' q"
      by (simp add: one_third_of_fwd_slashed_def)
    then have sl': "\<exists> q. one_third_of_fwd_or_bwd_slashed s r' q"
      using one_third_of_fwd_or_bwd_slashed_def by blast
    then show ?thesis
      using jjj by blast
  qed
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  consider (reduce) "e > v1" | (dbl_a) "e = v1" | (dbl_b) "v1 > e \<and> ee = v1 + 1" |
           (surround) "v1 > e \<and> ee > v1 + 1"
    using justified_on_finalization_n.prems(4) by linarith
  then show ?case proof cases
    case reduce
  then show ?thesis
    using close_fj close_justification_era justified_on_finalization_n.hyps(1) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) zero_justification_f by fastforce
  next
    case dbl_a
    then show ?thesis
      by (metis Suc_inject casper.justified_on_finalization_n casper_axioms close_fj forget_n_switchings justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) justified_on_finalization_n.prems(5) trivial_is_refl zero_justification_f)
  next
    case dbl_b
    have v0: "   \<exists> q. voted_by s q (vset_chosen r) c e h ee"
      by (metis (mono_tags, lifting) Suc_inject casper.validator_changing_link_def casper.voted_by_both_def casper_axioms justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) trivial_is_refl0 voted_by_fwd_def zero_justification_f)
    have v1: "   \<exists> q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 (v1 + 1)"
      using close_finalization_is_followed justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) by blast
    have diff: "e \<noteq> v1"
      using dbl_b by blast
    have eq: "ee = v1 + 1"
      using dbl_b by auto
    have v1': "   \<exists> q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 ee"
      using eq v1 by blast
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_chosen r) \<longrightarrow> slashed s n"
      using diff double_vote v0 v1' by blast
    have used: "\<exists> r' rE' a. justified s r' rE' a \<and> vset_fwd r' = vset_chosen r"
      by (metis Suc_inject casper.justified_with_root.intros(3) casper_axioms justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) justified_on_finalization_n.prems(6) trivial_is_refl0 validator_changing_link_def zero_justification_f)
    then obtain r' rE' a where jjj: "justified s r' rE' a \<and> vset_fwd r' = vset_chosen r" by blast
    have sl'': "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r') \<longrightarrow> slashed s n"
      by (simp add: jjj sl)
    then have "\<exists> q. one_third_of_fwd_slashed s r' q"
      by (simp add: one_third_of_fwd_slashed_def)
    then have sl': "\<exists> q. one_third_of_fwd_or_bwd_slashed s r' q"
      using one_third_of_fwd_or_bwd_slashed_def by blast
    then show ?thesis
      using jjj by blast
  next
    case surround
    have v0: "   \<exists> q. voted_by s q (vset_chosen r) c e h ee"
      by (metis (mono_tags, lifting) Suc_inject casper.validator_changing_link_def casper.voted_by_both_def casper_axioms justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) trivial_is_refl0 voted_by_fwd_def zero_justification_f)
    have v1: "   \<exists> q ch1. voted_by s q (vset_chosen r) h1 v1 ch1 (v1 + 1)"
      using close_finalization_is_followed justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) by blast
    have diff: "e < v1"
      by (simp add: surround)
    have eq: "ee > v1 + 1"
      using surround by blast
    have sl: "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_chosen r) \<longrightarrow> slashed s n"
      using surround surround_concrete v0 v1 by blast
    have used: "\<exists> r' rE' a. justified s r' rE' a \<and> vset_fwd r' = vset_chosen r"
      by (metis Suc_inject casper.justified_with_root.intros(3) casper_axioms justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(4) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(3) justified_on_finalization_n.prems(6) trivial_is_refl0 validator_changing_link_def zero_justification_f)
    then obtain r' rE' a where jjj: "justified s r' rE' a \<and> vset_fwd r' = vset_chosen r" by blast
    have sl'': "   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset_fwd r') \<longrightarrow> slashed s n"
      by (simp add: jjj sl)
    then have "\<exists> q. one_third_of_fwd_slashed s r' q"
      by (simp add: one_third_of_fwd_slashed_def)
    then have sl': "\<exists> q. one_third_of_fwd_or_bwd_slashed s r' q"
      using one_third_of_fwd_or_bwd_slashed_def by blast
    then show ?thesis
      using jjj by blast
  qed
qed

lemma close_j_f_f_two:
   "justified_with_root_with_n_switchings n r rE rM s h0 v0 m0 \<Longrightarrow>
    n = 2 \<Longrightarrow>
    close_finalization s r rE FinalizingChild h1 v1 m1 \<Longrightarrow>
    rM = FinalizingChild \<Longrightarrow>
    v1 < v0 \<Longrightarrow>
    \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
    justified s r rE FinalizingChild \<Longrightarrow>
    Suc rE < v0 \<Longrightarrow>
    vset_bwd h0 = vset_chosen r \<Longrightarrow>
    m0 = Usual \<Longrightarrow> (* this cannot be kept during the induction...?  Yes, it can be kept! *)
    \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case sorry
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  consider (reduce) "e > v1" | (others) "e \<le> v1"
    using leI by blast
  then show ?case proof cases
    case reduce
    have n1: "n = 1"
      by (simp add: Suc_inject justified_on_finalization_n.prems(1))
    have jv0: "justified_with_root_with_n_switchings n r rE mode s c e origM"
      by (simp add: justified_on_finalization_n.hyps(1))
    have non_j: "\<not> justified_with_root h1 v1 m1 s c e origM"
      using justified_on_finalization justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(6) by blast
    then show ?thesis
      using casper.close_j_f_f_one casper_axioms justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(2) justified_on_finalization_n.prems(3) justified_on_finalization_n.prems(7) jv0 reduce by fastforce
  next
    case others
    then show ?thesis sorry
  qed
qed

  sorry

lemma close_justification_and_finalization_cause_slashing_f :
  "close_justification s r rE rM h0 v0 m0 \<Longrightarrow>
   close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
   rM = FinalizingChild \<Longrightarrow>
   v0 > v1 \<Longrightarrow>
   \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
   \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
   \<exists> q r' rE' rM'. justified s r' rE' rM' \<and> one_third_of_fwd_or_bwd_slashed s r' q"
  apply(auto simp add: close_justification_def)
  using casper.close_justification_era casper.zero_justification_f casper_axioms close_fj apply fastforce
  using refl_inv zero_justification_f apply blast
     apply (metis casper.forget_n_switchings casper.trivial_is_refl casper_axioms close_fj close_justification_era le_less_Suc_eq not_less_iff_gr_or_eq order.order_iff_strict)
    apply (simp add: close_j_f_f_one)
  using close_j_f_f_one really_close_justification_zero apply blast
  by (simp add: close_j_f_f_two)


lemma close_justification_and_finalization_cause_slashing :
  "close_justification s r rE rM h0 v0 m0 \<Longrightarrow>
   close_finalization s r rE rM h1 v1 m1 \<Longrightarrow>
   v0 > v1 \<Longrightarrow>
   \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
   \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
   \<exists> q r' rE' rM'. justified s r' rE' rM' \<and> one_third_of_fwd_or_bwd_slashed s r' q"
  apply(cases "rM")
  using close_justification_and_finalization_cause_slashing_u apply blast
  using close_justification_and_finalization_cause_slashing_f by blast

lemma small_accountable_safety_gt :
  "small_fork s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   v0 > v1 \<Longrightarrow>
   \<exists> h v m q. justified s h v m \<and> one_third_of_fwd_or_bwd_slashed s h q"
proof -
  assume a: "small_fork s r rE rM h0 v0 m0 h1 v1 m1"
  have f: "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1"
    using a small_fork_def by blast
  have dif0: "\<not> justified_with_root h0 v0 m0 s h1 v1 m1"
    using f justification_fork_with_root_def by blast
  have dif1: "\<not> justified_with_root h1 v1 m1 s h0 v0 m0"
    using f justification_fork_with_root_def by blast
  have c00: "close_finalization s r rE rM h0 v0 m0"
    by (meson a casper.small_fork_has_close_justification casper_axioms)
  then have c0: "close_justification s r rE rM h0 v0 m0"
    using close_fj by blast
  have c1: "close_finalization s r rE rM h1 v1 m1"
    by (meson a casper.small_fork_has_close_justification casper.small_fork_sym casper_axioms)
  have j: "justified s r rE rM"
    using f justification_fork_with_root_def by blast
  assume "v0 > v1"
  then show ?thesis
    using c0 c1 close_justification_and_finalization_cause_slashing dif0 dif1 j by blast
qed

lemma small_accountable_safety :
  "small_fork s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> h v m q. justified s h m v \<and> one_third_of_fwd_or_bwd_slashed s h q"
proof(cases "v0 = v1")
  case True
  moreover assume "small_fork s r rE rM h0 v0 m0 h1 v1 m1"
  ultimately have "small_fork s r rE rM h0 v1 m0 h1 v1 m1" by simp
  then show ?thesis
    using small_accountable_safety_equal by blast
next
  case False
  moreover assume a: "small_fork s r rE rM h0 v0 m0 h1 v1 m1"
  then have b: "small_fork s r rE rM h1 v1 m1 h0 v0 m0"
    by (simp add: justification_fork_with_root_def small_fork_def)
  consider "v0 > v1" | "v1 > v0"
    using calculation nat_neq_iff by blast
  then show ?thesis
  using a b proof cases
    case 1
    then show ?thesis
      using a small_accountable_safety_gt by blast
  next
    case 2
    then show ?thesis
      using b small_accountable_safety_gt by blast
  qed
qed


lemma justification_fork_to_small:
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> r' rE' rM' h0' v0' m0' h1' v1' m1'.
     small_fork s r' rE' rM' h0' v0' m0' h1' v1' m1'"
proof(induct "v0 + v1 - rE" arbitrary: r rE rM h0 v0 m0 h1 v1 m1 rule: less_induct)
  case less
  then show ?case
  proof (cases "\<exists> r' rE' rM' h0' v0' m0' h1' v1' m1'. v0' + v1' - rE' < v0 + v1 - rE \<and>
                justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1'")
    case True
    then show ?thesis
      using less.hyps by blast
  next
    case False
    then have "small_fork s r rE rM h0 v0 m0 h1 v1 m1"
      by (simp add: less.prems small_fork_def)
    then show ?thesis by blast
  qed
qed

lemma justification_accountable_safety :
  "justification_fork_with_root s genesis 0 Usual h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> h v m q. justified s h v m \<and> one_third_of_fwd_or_bwd_slashed s h q"
  using casper.small_accountable_safety casper_axioms justification_fork_to_small by fastforce

lemma nth_parent_is_ancestor:
  "nth_parent n orig h \<Longrightarrow>
   orig \<leftarrow>\<^sup>* h \<or> orig = h"
proof(induct rule: nth_parent.induct)
  case (zeroth_parent h)
  then show ?case
    by simp
next
  case (Sth_parent n oldest mid newest)
  then show ?case
    using hash_ancestor_intro' by blast
qed

lemma voted_by_both_connects_ancestor_descendant:
  "voted_by_both s q0 q1 orig origE new newE \<Longrightarrow>
   orig \<leftarrow>\<^sup>* new \<or> orig = new"
  using nth_parent_is_ancestor voted_by_both_means_ancestor by blast

lemma usual_link_connects_ancestor_descendant:
  "usual_link s q0 q1 orig origE new newE \<Longrightarrow>
   orig \<leftarrow>\<^sup>* new \<or> orig = new"
  using usual_link_def voted_by_both_connects_ancestor_descendant by blast

lemma justification_is_ancestor:
  "justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
   h1 \<leftarrow>\<^sup>* h0 \<or> h1 = h0"
proof(induct rule:justified_with_root.induct)
  case (justified_genesis r rE s)
  then show ?case
    by simp
next
  case (usual_justification r rE s orig origE q0 q1 new newE)
  then show ?case
    using hash_ancestor_trans usual_link_connects_ancestor_descendant by blast
next
  case (justified_on_finalization r rE s p e q0 q1 c h ee)
  then show ?case
    by (metis hash_ancestor_trans validator_changing_link_def voted_by_both_connects_ancestor_descendant)
qed


lemma fork_to_justification_fork_with_root:
  "fork s h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   justification_fork_with_root s genesis 0 Usual h0 v0 m0 h1 v1 m1"
  by (metis fork_def justification_fork_with_root_def justification_is_ancestor justified_genesis)

(** intermediate stuff ends here **)

lemma accountable_safety :
  "fork s h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> h v m q. justified s h v m \<and> one_third_of_fwd_or_bwd_slashed s h q"
  using fork_to_justification_fork_with_root justification_accountable_safety by blast

end
end
