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

theory DynamicValidatorSet

imports Main

begin

section "Definition of the Protocol (Not Skippable)"

text "In this development we do not know much about hashes.  There are many hashes.
Two hashes might be equal or not."

datatype hash = Hash int

text "Views are numbers.  We actually need the fact that views are lines up in a total order.
Otherwise accountable safety can be broken."

type_synonym view = int

text "We have two kinds of messages.  A Commit message contains a hash and a view.  A prepare message contains a hash and two views.
At this point a message is not signed by anybody."

datatype message =
  Commit "hash * view"
| Prepare "hash * view * view"

text "We need a set of validators.  Here, we just define a datatype containing infinitely many
validators.
Afterwards, when we look at a particular situation, the situation would contain a finite set
of validators."

datatype validator = Validator int

text "A message signed by a validator can be represented as a pair of a validator and a message."

type_synonym signed_message = "validator * message"

text "Almost everything in this document depends on situations.  A situation contains a set
of validators, a set of signed messages, and a function specifying parents of hashes."

text "A situation might be seen from a global point of view where every sent messages can be seen,
or more likely seen from a local point of view."

record situation =
  RearValidators :: "hash \<Rightarrow> validator set"
  FwdValidators :: "hash \<Rightarrow> validator set"
  Messages :: "signed_message set"
  PrevHash :: "hash \<Rightarrow> hash option"

text "In the next section, we are going to determine which of the validators are slashed in a situation."

text "We will be talking about two conflicting commits.  To define `conflicting' one needs to look at the
hashes and their parent-children relation.
A situation contains information which hash is the parent of which hash.  We can follow this link n-times.
"

fun nth_ancestor :: "situation \<Rightarrow> nat \<Rightarrow> hash \<Rightarrow> hash option"
where
  "nth_ancestor _ 0 h = Some h"
| "nth_ancestor s (Suc n) h =
   (case PrevHash s h of
      None \<Rightarrow> None
    | Some h' \<Rightarrow> nth_ancestor s n h')"

text "And also we are allowed to talk if two hashes are in ancestor-descendant relation.
It does not matter if there is an algorithm to decide this."

definition is_descendant_or_self :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"is_descendant_or_self s x y = (\<exists> n. nth_ancestor s n x = Some y)"

definition is_descendant :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"is_descendant s x y = (\<exists> n. nth_ancestor s n x = Some y)"

text "We can also talk if two hashes are not in ancestor-descendant relation in whichever ways."

definition not_on_same_chain :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"not_on_same_chain s x y = ((\<not> is_descendant_or_self s x y) \<and> (\<not> is_descendant_or_self s y x))"

definition fork :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"fork s root h1 h2 =
  (not_on_same_chain s h1 h2 \<and> is_descendant s h1 root \<and> is_descendant s h2 root)"

definition fork_of_size :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> nat \<Rightarrow> bool"
where
"fork_of_size s root h1 h2 sz =
  (\<exists> m n.
   not_on_same_chain s h1 h2 \<and> nth_ancestor s m h1 = Some root \<and> nth_ancestor s n h2 = Some root \<and>
   m + n \<le> sz)"

lemma fork_has_size :
  "fork s root h1 h2 = (\<exists> sz. fork_of_size s root h1 h2 sz)"
apply(auto simp add: fork_def is_descendant_def fork_of_size_def)
done

text "In the slashing condition, we will be talking about two-thirds of the validators doing something."

text "We can lift any predicate about a validator into a predicate about a situation:
two thirds of the validators satisfy the predicate."

definition two_thirds :: "validator set \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"two_thirds vs f =
   (2 * card vs \<le> 3 * card ({n. n \<in> vs \<and> f n}))"

text "Similarly for one-third, more-than-two-thirds, and more-than-one-third."

definition one_third :: "validator set \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"one_third vs f =
   (card vs \<le> 3 * card ({n. n \<in> vs \<and> f n}))"

definition more_than_two_thirds :: "validator set \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"more_than_two_thirds vs f =
   (2 * card vs < 3 * card ({n. n \<in> vs \<and> f n}))"

definition more_than_one_third :: "validator set \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"more_than_one_third vs f =
   (card vs < 3 * card ({n. n \<in> vs \<and> f n}))"

definition two_thirds_sent_message :: "situation \<Rightarrow> validator set \<Rightarrow> message \<Rightarrow> bool"
where
"two_thirds_sent_message s vs m =
   two_thirds vs (\<lambda> n. (n, m) \<in> Messages s)"

text "A hash is prepared when two-thirds of the validators have sent a certain message."

definition prepared :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared s vs h v vsrc =
   (two_thirds_sent_message s vs (Prepare (h, v, vsrc)))"

text "A hash is committed when two-thirds of the validators have sent a certain message."

definition committed :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> bool"
where
"committed s vs h = (\<exists> v. two_thirds_sent_message s vs (Commit (h, v)))"

section "Electing the New Validators (not skippable)"

fun transfer_of_power :: "situation \<Rightarrow> validator set \<Rightarrow> validator set \<Rightarrow> bool"
where
"transfer_of_power s vs vs' = 
   (\<exists> h v v_src.
    RearValidators s h = vs \<and>
    FwdValidators s h = vs' \<and>
    prepared s vs h v v_src \<and>
    prepared s vs' h v v_src)"

inductive successor :: "situation \<Rightarrow>
                        validator set \<Rightarrow> 
                        validator set \<Rightarrow> bool"
where
  successor_self : "successor s vs vs"
| successor_elected :
    "successor s vs vs' \<Longrightarrow> transfer_of_power s vs' vs'' \<Longrightarrow>
     successor s vs vs''"

section "The Slashing Conditions (not skippable)"

text "[i] A validator is slashed when it has sent a commit message of a hash
      that is not prepared yet."

definition slashed_one :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_one s n =
    (\<exists> h v.
      ((n, Commit (h, v)) \<in> Messages s \<and>
    (\<not> (\<exists> vs. -1 \<le> vs \<and> vs < v \<and> prepared s (RearValidators s h) h v vs) )))"

text "[ii] A validator is slashed when it has sent a prepare message whose
      view src is not -1 but has no supporting preparation in the view src."

definition validators_match :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_match s h0 h1 =
 (RearValidators s h0 = RearValidators s h1 \<and>
  FwdValidators s h0 = FwdValidators s h1)"

definition validators_transition :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_transition s h0 h1 =
  (FwdValidators s h0 = RearValidators s h1)"

definition slashed_two :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_two s n =
  (\<exists> h v vs.
       ((n, Prepare (h, v, vs)) \<in> Messages s \<and>
       vs \<noteq> -1 \<and>
       (\<not> (\<exists> h_anc vs'.
           -1 \<le> vs' \<and> vs' < vs \<and>
           Some h_anc = nth_ancestor s (nat (v - vs)) h \<and>
           validators_match s h_anc h \<and>
           prepared s (RearValidators s h_anc) h_anc vs vs')) \<and>
       (\<not> (\<exists> h_anc vs'.
           -1 \<le> vs' \<and> vs' < vs \<and>
           Some h_anc = nth_ancestor s (nat (v - vs)) h \<and>
           validators_transition s h_anc h \<and>
           prepared s (RearValidators s h_anc) h_anc vs vs' \<and>
           committed s (RearValidators s h_anc) h_anc \<and>
           committed s (FwdValidators s h_anc) h_anc))))"

text "[iii] A validator is slashed when it has sent a commit message and a prepare message
     containing view numbers in a specific constellation."

definition slashed_three :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_three s n =
    (\<exists> x y v w u.
      (n, Commit (x, v)) \<in> Messages s \<and>
      (n, Prepare (y, w, u)) \<in> Messages s \<and>
      u < v \<and> v < w)"

text "[iv] A validator is slashed when it has signed two different Prepare messages at the same view."

definition slashed_four :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_four s n =
    (\<exists> x1 x2 v vs1 vs2.
      (n, Prepare (x1, v, vs1)) \<in> Messages s \<and>
      (n, Prepare (x2, v, vs2)) \<in> Messages s \<and>
      (x1 \<noteq> x2 \<or> vs1 \<noteq> vs2))"


text "A validator is slashed when at least one of the above conditions [i]--[iv] hold."

definition slashed :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed s n = (slashed_one s n \<or>
                slashed_two s n \<or>
                slashed_three s n \<or>
                slashed_four s n)"

fun hash_of_message :: "message \<Rightarrow> hash"
where
"hash_of_message (Commit (h, v)) = h"
|"hash_of_message (Prepare (h, v, vs)) = h"

definition prepare_commit_only_from_rear_or_fwd :: "situation \<Rightarrow> bool"
where
"prepare_commit_only_from_rear_or_fwd s =
  (\<forall> m. m \<in> Messages s \<longrightarrow>
     (fst m \<in> RearValidators s (hash_of_message (snd m)) \<or>
      fst m \<in> FwdValidators s (hash_of_message (snd m)))
  )"

definition one_third_slashed :: "situation \<Rightarrow> validator set \<Rightarrow> bool"
where
"one_third_slashed s vs = one_third vs (slashed s)"

text "However, since it does not make sense to divide the cardinality of an infinite set by three,
we should be talking
about situations where the set of validators is finite."

section "Useful Lemmas for Accountable Safety (can be skipped)"

lemma card_not [simp] :
  "finite s \<Longrightarrow>
   card {n \<in> s. \<not> f n} = card s - card {n \<in> s. f n}"
proof -
  assume "finite s"
  then have "card (s - {n \<in> s. f n}) = card s - card {n \<in> s. f n}"
    by (rule_tac Finite_Set.card_Diff_subset; auto)
  moreover have "{n \<in> s. \<not> f n} = s - {n \<in> s. f n}"
    by blast
  ultimately show ?thesis by auto
qed


lemma set_conj [simp] :
  "{n \<in> s. f n \<and> g n} = {n \<in> s. f n} \<inter> {n \<in> s. g n}"
by blast

lemma two_more_two_set :
  "finite s \<Longrightarrow>
    2 * card s \<le> 3 * card {n \<in> s. f n} \<Longrightarrow>
    2 * card s < 3 * card {n \<in> s. g n} \<Longrightarrow>
    card s
    < 3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
"
proof -
  assume "finite s"
  then have " card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
            = card {n \<in> s. f n} + card { n \<in> s. g n} - card ({n \<in> s. f n} \<union> {n \<in> s. g n})"
    proof -
      assume "finite s"
      then have "card {n \<in> s. f n} + card { n \<in> s. g n} = card ({n \<in> s. f n} \<union> {n \<in> s. g n}) + card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
        by (rule_tac Finite_Set.card_Un_Int; auto)
      then show ?thesis
        by auto
    qed
  moreover assume "finite s"
  then moreover have "card ({n \<in> s. f n} \<union> {n \<in> s. g n}) \<le> card s"
    by (rule Finite_Set.card_mono; auto)
  ultimately have "card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> card {n \<in> s. f n} + card { n \<in> s. g n} - card s"
    by auto
  then have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> 3 * card {n \<in> s. f n} + 3 * card { n \<in> s. g n} - 3 * card s"
    by auto
  moreover assume "2 * card s \<le> 3 * card {n \<in> s. f n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   \<ge> 3 * card { n \<in> s. g n} - card s"
    by auto
  moreover assume "2 * card s < 3 * card {n \<in> s. g n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   > card s"
    by auto
  then show ?thesis
    by auto
qed


lemma card_nonzero_exists :
"card {n \<in> s. f n} > 0 \<Longrightarrow>
 \<exists> n \<in> s. f n"
(* sledgehammer *)
	by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite not_gr_zero)


lemma card_conj_le :
  "finite s \<Longrightarrow>
     card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
   = card {n \<in> s. f n} + card { n \<in> s. g n} - card ({n \<in> s. f n} \<union> {n \<in> s. g n})"
proof -
 assume "finite s"
 then have "card {n \<in> s. f n} + card { n \<in> s. g n} = card ({n \<in> s. f n} \<union> {n \<in> s. g n}) + card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
   by (rule_tac Finite_Set.card_Un_Int; auto)
 then show ?thesis
   by auto
qed

lemma two_two_set :
 "2 * card s \<le> 3 * card {n \<in> s. f n} \<Longrightarrow>
  2 * card s \<le> 3 * card {n \<in> s. g n} \<Longrightarrow>
  finite s \<Longrightarrow>
  card s \<le> 3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
proof -
  assume "finite s"
  then have " card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
            = card {n \<in> s. f n} + card { n \<in> s. g n} - card ({n \<in> s. f n} \<union> {n \<in> s. g n})"
    proof -
      assume "finite s"
      then have "card {n \<in> s. f n} + card { n \<in> s. g n} = card ({n \<in> s. f n} \<union> {n \<in> s. g n}) + card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
        by (rule_tac Finite_Set.card_Un_Int; auto)
      then show ?thesis
        by auto
    qed
  moreover assume "finite s"
  then moreover have "card ({n \<in> s. f n} \<union> {n \<in> s. g n}) \<le> card s"
    by (rule Finite_Set.card_mono; auto)
  ultimately have "card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> card {n \<in> s. f n} + card { n \<in> s. g n} - card s"
    by auto
  then have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> 3 * card {n \<in> s. f n} + 3 * card { n \<in> s. g n} - 3 * card s"
    by auto
  moreover assume "2 * card s \<le> 3 * card {n \<in> s. f n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   \<ge> 3 * card { n \<in> s. g n} - card s"
    by auto
  moreover assume "2 * card s \<le> 3 * card {n \<in> s. g n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   \<ge> card s"
    by auto
  then show ?thesis
    by auto
qed

lemma dependency_self [simp]:
  "\<not> not_on_same_chain s y y"
apply(simp add: not_on_same_chain_def)
apply(simp add: is_descendant_or_self_def)
apply(rule_tac x = 0 in exI)
apply(simp)
done

lemma prepare_direct_conflict :
 "not_on_same_chain s x y \<Longrightarrow>
  n \<in> Validators s \<Longrightarrow>
  (n, Prepare (x, v2, vs1)) \<in> Messages s \<Longrightarrow>
  (n, Prepare (y, v2, vs2)) \<in> Messages s \<Longrightarrow> slashed_four s n"
apply(auto simp add: slashed_four_def)
by fastforce


lemma inclusion_card_le :
  "\<forall>n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n \<Longrightarrow>
   finite (Validators s) \<Longrightarrow>
   card {n \<in> Validators s. f n} \<le> card {n \<in> Validators s. g n}"
proof -
  assume "\<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n"
  moreover assume "finite (Validators s)"
  ultimately show "card {n \<in> Validators s. f n} \<le> card {n \<in> Validators s. g n}"
    proof -
      assume "\<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n"
      then have "{n \<in> Validators s. f n} \<subseteq> {n \<in> Validators s. g n}"
        by blast
      moreover assume "finite (Validators s)"
      ultimately show ?thesis
        by (simp add: card_mono)
    qed
qed

lemma not_on_same_chain_sym [simp] :
 "not_on_same_chain s x y = not_on_same_chain s y x"
apply(auto simp add: not_on_same_chain_def)
done

lemma ancestors_ancestor : "
  \<forall> m x y.
   nth_ancestor s n x = Some y \<longrightarrow>
   nth_ancestor s m y = nth_ancestor s (n + m) x
"
apply(induction n; auto)
apply(case_tac "PrevHash s x"; auto)
done

lemma nat_min_min :
"    vs1 < v \<Longrightarrow>
    \<not> vs1 < c_view \<Longrightarrow>
   (nat (v - vs1) + nat (vs1 - c_view)) = nat (v - c_view)"
by (simp add: Nat_Transfer.transfer_nat_int_functions(1))

lemma ancestor_ancestor : "
       nth_ancestor s (nat (v - c_view)) x \<noteq> Some y \<Longrightarrow>
       vs1 < v \<Longrightarrow>
       \<not> vs1 < c_view \<Longrightarrow>
       \<not> c_view \<le> - 1 \<Longrightarrow>
       - 1 \<le> vs' \<Longrightarrow>
       vs' < vs1 \<Longrightarrow>
       Some h_anc = nth_ancestor s (nat (v - vs1)) x \<Longrightarrow>
       nth_ancestor s (nat (vs1 - c_view)) h_anc \<noteq> Some y 
"
apply(simp add: ancestors_ancestor nat_min_min)
done


lemma view_total [simp]:
  "(v2 :: view) \<le> v1 \<or> v1 \<le> v2"
apply auto
done


section "Accountable Safety (don't skip)"

text "The statement of accountable safety is simple.  If a situation has a finite number of validators (but not zero),
if two hashes x and y are committed in the situation, but if the two hashes are not on the same chain,
at least one-third of the validators are slashed in the situation."

(* TODO: state it again *)

definition decided :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> bool"
where
"decided s vs h = (committed s vs h \<and> RearValidators s h = vs)"

lemma fork_of_size_zero :
  "\<not> fork_of_size s h h1 h2 0"
apply(auto simp add: fork_of_size_def not_on_same_chain_def is_descendant_or_self_def)
using nth_ancestor.simps(1) by blast

lemma accountable_safety_ind :
       "\<forall>s. prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
           (\<forall>h h1 h2.
               fork_of_size s h h1 h2 sz \<longrightarrow>
               (\<forall>vs. decided s vs h \<longrightarrow>
                     (\<exists>vs1. decided s vs1 h1) \<longrightarrow>
                     (\<exists>vs2. decided s vs2 h2) \<longrightarrow>
                     (\<exists>vs'. successor s vs vs' \<and> one_third_slashed s vs'))) \<Longrightarrow>
       prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
       fork_of_size s h h1 h2 (Suc sz) \<Longrightarrow>
       decided s vs h \<Longrightarrow>
       decided s vs1 h1 \<Longrightarrow> decided s vs2 h2 \<Longrightarrow> \<exists>vs'. successor s vs vs' \<and> one_third_slashed s vs'"
sorry

lemma accountable_safety' :
"\<forall> s h h1 h2 vs vs1 vs2.
 prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
 fork_of_size s h h1 h2 sz \<longrightarrow>
 decided s vs h \<longrightarrow>
 decided s vs1 h1 \<longrightarrow>
 decided s vs2 h2 \<longrightarrow>
 (\<exists> vs'.
   successor s vs vs' \<and>
   one_third_slashed s vs')"
apply(induction sz; auto simp add: fork_of_size_zero accountable_safety_ind)
done

lemma accountable_safety :
"prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
 fork s h h1 h2 \<Longrightarrow>
 decided s vs h \<Longrightarrow>
 decided s vs1 h1 \<Longrightarrow>
 decided s vs2 h2 \<Longrightarrow>
 \<exists> vs'.
   successor s vs vs' \<and>
   one_third_slashed s vs'"
by (meson accountable_safety' fork_has_size)

end
