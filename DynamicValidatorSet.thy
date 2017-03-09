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

theory MinimumAlgo

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
  Validators :: "validator set"
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

text "We can also talk if two hashes are not in ancestor-descendant relation in whichever ways."

definition not_on_same_chain :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"not_on_same_chain s x y = ((\<not> is_descendant_or_self s x y) \<and> (\<not> is_descendant_or_self s y x))"

text "In the slashing condition, we will be talking about two-thirds of the validators doing something."

text "We can lift any predicate about a validator into a predicate about a situation:
two thirds of the validators satisfy the predicate."

definition two_thirds :: "situation \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"two_thirds s f =
   (2 * card (Validators s) \<le> 3 * card ({n. n \<in> Validators s \<and> f n}))"

text "Similarly for one-third, more-than-two-thirds, and more-than-one-third."

definition one_third :: "situation \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"one_third s f =
   (card (Validators s) \<le> 3 * card ({n. n \<in> Validators s \<and> f n}))"

definition more_than_two_thirds :: "situation \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"more_than_two_thirds s f =
   (2 * card (Validators s) < 3 * card ({n. n \<in> Validators s \<and> f n}))"

definition more_than_one_third :: "situation \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"more_than_one_third s f =
   (card (Validators s) < 3 * card ({n. n \<in> Validators s \<and> f n}))"

definition two_thirds_sent_message :: "situation \<Rightarrow> message \<Rightarrow> bool"
where
"two_thirds_sent_message s m =
   two_thirds s (\<lambda> n. (n, m) \<in> Messages s)"

text "A hash is prepared when two-thirds of the validators have sent a certain message."

definition prepared :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared s h v vs =
   (two_thirds_sent_message s (Prepare (h, v, vs)))"

text "A hash is committed when two-thirds of the validators have sent a certain message."

definition committed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"committed s h = (\<exists> v. two_thirds_sent_message s (Commit (h, v)))"

section "The Slashing Conditions (not skippable)"

text "[i] A validator is slashed when it has sent a commit message of a hash
      that is not prepared yet."

definition slashed_one :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_one s n =
 (n \<in> Validators s \<and>
    (\<exists> h v.
      ((n, Commit (h, v)) \<in> Messages s \<and>
    (\<not> (\<exists> vs. -1 \<le> vs \<and> vs < v \<and> prepared s h v vs) ))))"

text "[ii] A validator is slashed when it has sent a prepare message whose
      view src is not -1 but has no supporting preparation in the view src."

definition slashed_two :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_two s n =
  (n \<in> Validators s \<and>
     (\<exists> h v vs.
       ((n, Prepare (h, v, vs)) \<in> Messages s \<and>
       vs \<noteq> -1 \<and>
       (\<not> (\<exists> h_anc vs'.
           -1 \<le> vs' \<and> vs' < vs \<and>
           Some h_anc = nth_ancestor s (nat (v - vs)) h \<and>
           prepared s h_anc vs vs')))))"

text "[iii] A validator is slashed when it has sent a commit message and a prepare message
     containing view numbers in a specific constellation."

definition slashed_three :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_three s n =
  (n \<in> Validators s \<and>
    (\<exists> x y v w u.
      (n, Commit (x, v)) \<in> Messages s \<and>
      (n, Prepare (y, w, u)) \<in> Messages s \<and>
      u < v \<and> v < w))"

text "[iv] A validator is slashed when it has signed two different Prepare messages at the same view."

definition slashed_four :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_four s n =
  (n \<in> Validators s \<and>
    (\<exists> x1 x2 v vs1 vs2.
      (n, Prepare (x1, v, vs1)) \<in> Messages s \<and>
      (n, Prepare (x2, v, vs2)) \<in> Messages s \<and>
      (x1 \<noteq> x2 \<or> vs1 \<noteq> vs2)))"


text "A validator is slashed when at least one of the above conditions [i]--[iv] hold."

definition slashed :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed s n = (slashed_one s n \<or>
                slashed_two s n \<or>
                slashed_three s n \<or>
                slashed_four s n)"

definition one_third_slashed :: "situation \<Rightarrow> bool"
where
"one_third_slashed s = one_third s (slashed s)"

text "However, since it does not make sense to divide the cardinality of an infinite set by three,
we should be talking
about situations where the set of validators is finite."

definition situation_has_finitely_many_validators :: "situation \<Rightarrow> bool"
where
"situation_has_finitely_many_validators s = (Validators s \<noteq> {} \<and> finite (Validators s))"


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

lemma not_one_third [simp] :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   (\<not> one_third s f) = (more_than_two_thirds s (\<lambda> n. \<not> f n))"
apply(auto simp add: one_third_def more_than_two_thirds_def situation_has_finitely_many_validators_def)
done

lemma condition_one_positive :
   "\<exists> n. (n, Commit (x, v)) \<in> Messages s \<and>
    n \<in> Validators s \<and>
    \<not> slashed s n \<Longrightarrow>
    (\<exists>v vs.
     two_thirds s (\<lambda>n. (n, Prepare (x, v, vs)) \<in> Messages s)
     \<and> - 1 \<le> vs \<and> vs < v)"
using slashed_def slashed_one_def two_thirds_sent_message_def prepared_def
by blast

lemma condition_one_positive' :
   "\<exists> n. (n, Commit (x, v)) \<in> Messages s \<and>
    n \<in> Validators s \<and>
    \<not> slashed s n \<Longrightarrow>
    (\<exists>vs.
     two_thirds s (\<lambda>n. (n, Prepare (x, v, vs)) \<in> Messages s)
     \<and> - 1 \<le> vs \<and> vs < v)"
using slashed_def slashed_one_def two_thirds_sent_message_def prepared_def
by blast

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


lemma two_more_two :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   two_thirds s f \<Longrightarrow>
   more_than_two_thirds s g \<Longrightarrow>
   more_than_one_third s (\<lambda> n. f n \<and> g n)
  "
apply(simp add: two_thirds_def situation_has_finitely_many_validators_def more_than_two_thirds_def more_than_one_third_def)
apply(rule two_more_two_set; simp)
done

lemma card_nonzero_exists :
"card {n \<in> s. f n} > 0 \<Longrightarrow>
 \<exists> n \<in> s. f n"
(* sledgehammer *)
	by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite not_gr_zero)

lemma more_than_one_third_exists :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   more_than_one_third s f \<Longrightarrow>
   \<exists> n \<in> Validators s. f n
  "
apply(rule card_nonzero_exists)
apply(simp add: situation_has_finitely_many_validators_def more_than_one_third_def)
done


lemma two_more_two_ex :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   two_thirds s f \<Longrightarrow>
   more_than_two_thirds s g \<Longrightarrow>
   \<exists> n \<in> Validators s. f n \<and> g n "
apply(rule more_than_one_third_exists)
 apply simp
apply(rule two_more_two; simp)
done

lemma commit_expand:
  "situation_has_finitely_many_validators s \<Longrightarrow> 
   two_thirds_sent_message s (Commit (x, v)) \<Longrightarrow>
   (\<exists> vs. prepared s x v vs \<and> -1 \<le> vs \<and> vs < v) \<or> one_third_slashed s"
apply(auto simp add: committed_def prepared_def two_thirds_sent_message_def one_third_slashed_def)
apply(rule condition_one_positive')
using two_more_two_ex by blast

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

lemma two_two :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   two_thirds s f \<Longrightarrow>
   two_thirds s g \<Longrightarrow>
   one_third s (\<lambda> n. f n \<and> g n)"
apply(auto simp add: two_thirds_def one_third_def situation_has_finitely_many_validators_def two_two_set)
done

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

lemma mp_one_third :
  "finite (Validators s) \<Longrightarrow>
   \<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n \<Longrightarrow>
   one_third s f \<Longrightarrow> one_third s g"
proof (simp add: one_third_def)
  assume "\<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n"
  moreover assume "finite (Validators s)"
  ultimately have "card {n \<in> Validators s. f n} \<le> card {n \<in> Validators s. g n}"
    using inclusion_card_le by blast
  moreover assume "card (Validators s) \<le> 3 * card {n \<in> Validators s. f n}"
  ultimately show "card (Validators s) \<le> 3 * card {n \<in> Validators s. g n}"
    by auto
qed

lemma mp_two_thirds :
  "finite (Validators s) \<Longrightarrow>
   \<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n \<Longrightarrow>
   two_thirds s f \<Longrightarrow> two_thirds s g"
proof (simp add: two_thirds_def)
  assume "\<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n"
  moreover assume "finite (Validators s)"
  ultimately have "card {n \<in> Validators s. f n} \<le> card {n \<in> Validators s. g n}"
    using inclusion_card_le by blast
  moreover assume "2 * card (Validators s) \<le> 3 * card {n \<in> Validators s. f n}"
  ultimately show "2 * card (Validators s) \<le> 3 * card {n \<in> Validators s. g n}"
    by auto
qed


lemma safety_case1' :
   "situation_has_finitely_many_validators s \<Longrightarrow>
    not_on_same_chain s x y \<Longrightarrow>
    two_thirds s (\<lambda>n. (n, Prepare (x, v2, vs1)) \<in> Messages s) \<Longrightarrow>
    two_thirds s (\<lambda>n. (n, Prepare (y, v2, vs2)) \<in> Messages s) \<Longrightarrow> one_third s (slashed s)"
proof -
  assume "situation_has_finitely_many_validators s"
  moreover assume "two_thirds s (\<lambda>n. (n, Prepare (x, v2, vs1)) \<in> Messages s)"
  moreover assume "two_thirds s (\<lambda>n. (n, Prepare (y, v2, vs2)) \<in> Messages s)"
  ultimately have
    "one_third s (\<lambda>n. (n, Prepare (x, v2, vs1)) \<in> Messages s
                   \<and> (n, Prepare (y, v2, vs2)) \<in> Messages s)"
    using two_two by blast
  moreover assume "not_on_same_chain s x y"
  moreover assume "situation_has_finitely_many_validators s"
  ultimately show "one_third s (slashed s)"
    by (rule_tac mp_one_third; auto simp add: situation_has_finitely_many_validators_def
        prepare_direct_conflict slashed_def)
qed

lemma safety_case1 :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   not_on_same_chain s x y \<Longrightarrow>
   prepared s x v2 vs1 \<Longrightarrow>
   prepared s y v2 vs2 \<Longrightarrow>
   one_third_slashed s"
apply(auto simp add: one_third_slashed_def prepared_def two_thirds_sent_message_def
     safety_case1')
done

lemma not_on_same_chain_sym [simp] :
 "not_on_same_chain s x y = not_on_same_chain s y x"
apply(auto simp add: not_on_same_chain_def)
done

lemma commit_prepare :
 "situation_has_finitely_many_validators s \<Longrightarrow>
  two_thirds s (\<lambda>n. (n, Commit (y, v)) \<in> Messages s) \<Longrightarrow>
  (\<exists>vs. prepared s y v vs \<and> -1 \<le> vs \<and> vs < v) \<or> one_third_slashed s"
apply(auto simp add: committed_def prepared_def two_thirds_sent_message_def one_third_slashed_def)
apply(rule condition_one_positive')
using two_more_two_ex by blast

lemma one_third_prepared_conflict :
 "x \<noteq> y \<Longrightarrow>
  one_third s
     (\<lambda>n. (n, Prepare (y, c_view, vs)) \<in> Messages s \<and> (n, Prepare (x, c_view, vs1)) \<in> Messages s) \<Longrightarrow>
  situation_has_finitely_many_validators s \<Longrightarrow>
  one_third s (slashed s)"
apply(rule mp_one_third; blast?)
 apply(simp add: situation_has_finitely_many_validators_def)
using slashed_def slashed_four_def by blast

lemma prepared_conflict :
"prepared s y c_view vs \<Longrightarrow>
 situation_has_finitely_many_validators s \<Longrightarrow>
 x \<noteq> y \<Longrightarrow>
 prepared s x c_view vs1 \<Longrightarrow>
 one_third_slashed s"
proof(simp add: prepared_def two_thirds_sent_message_def one_third_slashed_def)
 assume "situation_has_finitely_many_validators s"
 moreover assume "two_thirds s (\<lambda>n. (n, Prepare (y, c_view, vs)) \<in> Messages s)"
 moreover assume "two_thirds s (\<lambda>n. (n, Prepare (x, c_view, vs1)) \<in> Messages s)"
 ultimately have "one_third s (\<lambda>n. (n, Prepare (y, c_view, vs)) \<in> Messages s \<and>
                                   (n, Prepare (x, c_view, vs1)) \<in> Messages s)"
   using two_two by blast
 moreover assume "situation_has_finitely_many_validators s"
 moreover assume "x \<noteq> y"
 ultimately show "one_third s (slashed s)"
  by (metis (no_types, lifting) mp_one_third situation_has_finitely_many_validators_def slashed_def slashed_four_def)
qed

lemma commit_prepared :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
   prepared s x c_view vs1 \<Longrightarrow>
   one_third_slashed s"
proof(simp add: two_thirds_sent_message_def)
 assume "situation_has_finitely_many_validators s"
 moreover assume "two_thirds s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s)"
 ultimately have "(\<exists> vs. prepared s y c_view vs \<and> -1 \<le> vs \<and> vs < c_view) \<or> one_third_slashed s"
   using commit_prepare by blast
 moreover assume "situation_has_finitely_many_validators s"
 moreover assume "x \<noteq> y"
 moreover assume "prepared s x c_view vs1"
 ultimately show "one_third_slashed s"
   using prepared_conflict by blast
qed

lemma condition_three_again :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   vs1 < c_view \<Longrightarrow>
   c_view < v \<Longrightarrow>
   one_third s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s \<and> (n, Prepare (x, v, vs1)) \<in> Messages s) \<Longrightarrow>
   one_third_slashed s"
apply(simp add: one_third_slashed_def)
apply(rule mp_one_third; blast?)
 apply(simp add: situation_has_finitely_many_validators_def)
using slashed_def slashed_three_def by blast

lemma between_concrete :
  "c_view < v \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
   prepared s x v vs1 \<Longrightarrow>
   vs1 < c_view \<Longrightarrow>
   situation_has_finitely_many_validators s \<Longrightarrow>
   one_third_slashed s"
proof(simp add: prepared_def two_thirds_sent_message_def)
  assume "situation_has_finitely_many_validators s"
  moreover assume "two_thirds s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s)"
  moreover assume "two_thirds s (\<lambda>n. (n, Prepare (x, v, vs1)) \<in> Messages s)"
  ultimately have "one_third s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s \<and>
                                 (n, Prepare (x, v, vs1)) \<in> Messages s)"
    using two_two by blast
  moreover assume "situation_has_finitely_many_validators s"
  moreover assume "c_view < v"
  moreover assume "vs1 < c_view"
  ultimately show "one_third_slashed s"
    using condition_three_again by blast
qed

lemma between_case :
  "c_view \<le> v \<Longrightarrow>
   situation_has_finitely_many_validators s \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
   prepared s x v vs1 \<Longrightarrow> - 1 \<le> vs1 \<Longrightarrow> c_view \<noteq> v \<Longrightarrow> vs1 < c_view \<Longrightarrow> one_third_slashed s"
proof -
  assume "c_view \<noteq> v"
  moreover assume "c_view \<le> v"
  ultimately have "c_view < v"
    by linarith
  moreover assume "two_thirds_sent_message s (Commit (y, c_view))"
  moreover assume "prepared s x v vs1"
  moreover assume "vs1 < c_view"
  moreover assume "situation_has_finitely_many_validators s"
  ultimately show ?thesis
    using between_concrete by blast
qed


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

lemma the_induction :
      "nat (v - c_view) \<le> Suc n \<Longrightarrow>
       situation_has_finitely_many_validators s \<Longrightarrow>
       nth_ancestor s (nat (v - c_view)) x \<noteq> Some y \<Longrightarrow>
       two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
       prepared s x v vs1 \<Longrightarrow>
       vs1 < v \<Longrightarrow>
       \<not> vs1 < c_view \<Longrightarrow>
       \<not> c_view \<le> - 1 \<Longrightarrow>
       \<forall>x y v.
          nat (v - c_view) \<le> n \<longrightarrow>
          c_view \<le> v \<longrightarrow>
          situation_has_finitely_many_validators s \<longrightarrow>
          nth_ancestor s (nat (v - c_view)) x \<noteq> Some y \<longrightarrow>
          two_thirds_sent_message s (Commit (y, c_view)) \<longrightarrow>
          (\<forall>vs1. prepared s x v vs1 \<longrightarrow> - 1 \<le> vs1 \<longrightarrow> vs1 < v \<longrightarrow> one_third_slashed s) \<Longrightarrow>
       one_third_slashed s"
apply(case_tac "vs1 = -1")
 apply simp
apply(subgoal_tac "
       (\<exists> h_anc vs'.
           -1 \<le> vs' \<and> vs' < vs1 \<and>
           Some h_anc = nth_ancestor s (nat (v - vs1)) x \<and>
           prepared s h_anc vs1 vs') \<or> one_third_slashed s")
 apply clarsimp
 apply(drule_tac x = h_anc in spec)
 apply(drule_tac x = y in spec)
 apply(drule_tac x = vs1 in spec)
 apply clarsimp
 apply(case_tac "nat (vs1 - c_view) \<le> n")
  apply simp
  apply(case_tac "nth_ancestor s (nat (vs1 - c_view)) h_anc \<noteq> Some y")
   apply simp
  apply(simp add: ancestor_ancestor)
 apply linarith
apply(subgoal_tac
  "(\<exists> somebody. \<not> slashed s somebody \<and> somebody \<in> Validators s \<and> (somebody, Prepare (x, v, vs1)) \<in> Messages s) \<or> one_third_slashed s")
 apply clarify
 apply(subgoal_tac "\<not> slashed_two s somebody")
  defer
  apply(simp add: slashed_def)
 apply (metis (mono_tags, lifting) not_one_third one_third_slashed_def prepared_def two_more_two_ex two_thirds_sent_message_def)
apply(simp add: slashed_two_def)
by fastforce

text "The following lemma is a core of the accountable safety proof.
It requires the mathematical induction."

lemma safety_sub_ind' :
  "\<forall> c_view s x y v vs1.
   n \<ge> nat (v - c_view) \<longrightarrow>
   v \<ge> c_view \<longrightarrow>
   situation_has_finitely_many_validators s \<longrightarrow>
   nth_ancestor s (nat (v - c_view)) x \<noteq> Some y \<longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<longrightarrow>
   prepared s x v vs1 \<longrightarrow>
   - 1 \<le> vs1 \<longrightarrow> vs1 < v \<longrightarrow> one_third_slashed s"
apply(induction n; auto)
 using commit_prepared apply blast
apply(case_tac "\<not> (v > c_view)")
 apply clarsimp
 using commit_prepared apply blast 
apply(case_tac "vs1 < c_view")
 apply clarsimp
 using between_case apply blast
apply(case_tac "c_view \<le> -1")
 apply(clarsimp)
 using commit_expand apply fastforce
using the_induction by blast

lemma safety_sub_ind'' :
  "n = nat (v - c_view) \<Longrightarrow>
   v \<ge> c_view \<Longrightarrow>
   situation_has_finitely_many_validators s \<Longrightarrow>
   nth_ancestor s n x \<noteq> Some y \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
   prepared s x v vs1 \<Longrightarrow>
   - 1 \<le> vs1 \<Longrightarrow> vs1 < v \<Longrightarrow> one_third_slashed s"
using safety_sub_ind' by blast

lemma not_on_chain_not_ancestor [simp] :
 "not_on_same_chain s x y \<Longrightarrow>
  nth_ancestor s m x \<noteq> Some y"
apply(simp add: not_on_same_chain_def is_descendant_or_self_def)
done

lemma safety_sub_ind :
  "situation_has_finitely_many_validators s \<longrightarrow>
   not_on_same_chain s x y \<longrightarrow>
   two_thirds_sent_message s (Commit (x, v1)) \<longrightarrow>
   two_thirds_sent_message s (Commit (y, v2)) \<longrightarrow>
   prepared s x v1' vs1 \<longrightarrow>
   prepared s y v2' vs2 \<longrightarrow>
   v1' \<ge> v2 \<or> v2' \<ge> v1 \<longrightarrow>
   - 1 \<le> vs1 \<longrightarrow> vs1 < v1' \<longrightarrow> - 1 \<le> vs2 \<longrightarrow> vs2 < v2' \<longrightarrow> one_third_slashed s"
apply(auto)
 apply(rule_tac s = s and c_view = v2 and v = v1' and n = "nat (v1' - v2)"
       in safety_sub_ind''; simp?)
apply(rule_tac s = s and c_view = v1 and v = v2' and n = "nat (v2' - v1)"
       in safety_sub_ind''; simp?)
done
 

lemma safety_sub_closer :
  "situation_has_finitely_many_validators s \<longrightarrow>
   not_on_same_chain s x y \<longrightarrow>
   two_thirds_sent_message s (Commit (x, v1)) \<longrightarrow>
   two_thirds_sent_message s (Commit (y, v2)) \<longrightarrow>
   prepared s x v1 vs1 \<longrightarrow>
   prepared s y v2 vs2 \<longrightarrow>
   v2 \<le> v1 \<or> v1 \<le> v2 \<longrightarrow>
   - 1 \<le> vs1 \<longrightarrow> vs1 < v1 \<longrightarrow> - 1 \<le> vs2 \<longrightarrow> vs2 < v2 \<longrightarrow> one_third_slashed s"
using safety_sub_ind by blast

lemma view_total [simp]:
  "(v2 :: view) \<le> v1 \<or> v1 \<le> v2"
apply auto
done

lemma safety_sub' :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   not_on_same_chain s x y \<Longrightarrow>
   two_thirds_sent_message s (Commit (x, v1)) \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, v2)) \<Longrightarrow>
   prepared s x v1 vs1 \<Longrightarrow>
   prepared s y v2 vs2 \<Longrightarrow>
   - 1 \<le> vs1 \<Longrightarrow> vs1 < v1 \<Longrightarrow> - 1 \<le> vs2 \<Longrightarrow> vs2 < v2 \<Longrightarrow> one_third_slashed s"
using safety_sub_closer by auto

lemma accountable_safety_sub :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   \<exists> v1 vs1. two_thirds_sent_message s (Commit (x, v1)) \<and> prepared s x v1 vs1 \<and> -1 \<le> vs1 \<and> vs1 < v1 \<Longrightarrow>
   \<exists> v2 vs2. two_thirds_sent_message s (Commit (y, v2)) \<and> prepared s y v2 vs2 \<and> -1 \<le> vs2 \<and> vs2 < v2 \<Longrightarrow>
   not_on_same_chain s x y \<Longrightarrow>
   one_third_slashed s
  "
apply(auto simp add: safety_sub')
done


section "Accountable Safety (don't skip)"

text "The statement of accountable safety is simple.  If a situation has a finite number of validators (but not zero),
if two hashes x and y are committed in the situation, but if the two hashes are not on the same chain,
at least one-third of the validators are slashed in the situation."

lemma accountable_safety :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   committed s x \<Longrightarrow> committed s y \<Longrightarrow>
   not_on_same_chain s x y \<Longrightarrow> one_third_slashed s"
apply(auto simp add: committed_def)
using accountable_safety_sub commit_expand by blast

(* what happens with half_slashed? *)

section "More Terminology for Liveness (not skippable)"

text "For plausible liveness, one needs to construct a new set of messages that are to be added to
a situation.  For doing that, it's convenient to look at the view numbers of the existing messages."

definition view_of_message :: "message \<Rightarrow> view"
where
"view_of_message m = (case m of
   Commit (h, v) \<Rightarrow> v
 | Prepare (h, v, v_src) \<Rightarrow> v)"

text "The proof gets complicated when we have a Commit with -2 view, so we just choose to ignore such
messages in a situation.  For ignoring messages with invalid view numbers, we need a predicate."

definition message_has_valid_view :: "message \<Rightarrow> bool"
where
"message_has_valid_view m = (case m of 
   Commit (h,v) \<Rightarrow> 0 \<le> v
 | Prepare (h, v, v_src) \<Rightarrow> -1 \<le> v \<and> v < v_src)"

text "We frequently talk about the view number of a signed message.  So here is a function for doing that."

definition view_of_signed_message :: "(validator * message) \<Rightarrow> view"
where
"view_of_signed_message = view_of_message o snd"

text "
This condition says the situation does not contain certain messages with invalid view numbers.
Practically, this can be achieved by ignoring all unqualified messages in the situation."

definition no_invalid_view :: "situation \<Rightarrow> bool"
where
"no_invalid_view s =
  (\<forall> n m. (n, m) \<in> Messages s \<longrightarrow>
          message_has_valid_view m)"

text "Sometimes we want to say there are only finitely many messages in a situation.  Otherwise all views might have been occupied."

definition finite_messages :: "situation \<Rightarrow> bool"
where
"finite_messages s = finite (Messages s)"

text "For liveness we need new hashes to be committed."

definition new_descendant_available :: "situation \<Rightarrow> bool"
where
"new_descendant_available s =
  (\<forall> n h v diff.
    (n, Commit (h, v)) \<in> Messages s \<longrightarrow>
    (\<exists> h_new. nth_ancestor s diff h_new = Some h \<and> \<not> committed s h_new))"

text "Authors of a set of sent messages:"

definition authors :: "(validator * message) set \<Rightarrow> validator set"
where
  "authors ms = {n. \<exists> m. (n, m) \<in> ms}"

text "The set of validators not slashed in a situation:"

definition unslashed_validators :: "situation \<Rightarrow> validator set"
where
  "unslashed_validators s = {n \<in> Validators s. \<not> slashed s n}"

text "Sometimes those unslashed validators can send messages and turn a situation into another."

definition unslashed_can_extend :: "situation \<Rightarrow> situation \<Rightarrow> bool"
where
"unslashed_can_extend s s_new =
 (\<exists> new_messages.
  authors new_messages \<subseteq> unslashed_validators s \<and>
  Validators s_new = Validators s \<and>
  Messages s_new = Messages s \<union> new_messages \<and>
  PrevHash s_new = PrevHash s_new)"

text "In that case, it's desirable none of these validators are slashed."

definition no_new_slashed :: "situation \<Rightarrow> situation \<Rightarrow> bool"
where
"no_new_slashed s s_new =
  (\<forall> n. n \<in> Validators s \<longrightarrow> slashed s_new n \<longrightarrow> slashed s n)"

section "Useful Lemmas for Plausible Liveness (skippable)"

definition no_commits_by_honest :: "situation \<Rightarrow> bool"
where
"no_commits_by_honest s =
  (\<forall> n \<in> Validators s. (\<forall> h v.
     (n, Commit (h, v)) \<in> Messages s \<longrightarrow> slashed s n
  ))
"

definition no_messages_by_honest :: "situation \<Rightarrow> bool"
where
"no_messages_by_honest s =
  (\<forall> n \<in> Validators s. (\<forall> m. (n, m) \<in> Messages s \<longrightarrow> slashed s n))"

definition some_commits_by_honest_at :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"some_commits_by_honest_at s v =
  (\<exists> n \<in> Validators s.
     \<not> slashed s n \<and>
     (\<exists> h. (n, Commit (h, v)) \<in> Messages s))
"

definition some_messages_by_honest_at :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"some_messages_by_honest_at s v =
  (\<exists> n \<in> Validators s.
     \<not> slashed s n \<and>
     (\<exists> m. view_of_message m = v \<and> 
       (n, m) \<in> Messages s))"

definition no_commits_by_honest_after :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"no_commits_by_honest_after s v_latest =
   (\<forall> n \<in> Validators s. (\<forall> h v.
     (n, Commit (h, v)) \<in> Messages s \<longrightarrow>
     v \<le> v_latest \<or> slashed s n
     ))"

definition no_messages_by_honest_after :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"no_messages_by_honest_after s v_latest =
  (\<forall> n \<in> Validators s. (\<forall> m.
    (n, m) \<in> Messages s \<longrightarrow>
    view_of_message m \<le> v_latest \<or> slashed s n))"

lemma some_commits_by_honest_intro :
  "\<exists>n\<in>Validators s. (\<exists>h v. (n, Commit (h, v)) \<in> Messages s) \<and> \<not> slashed s n \<Longrightarrow>
   {M1. some_commits_by_honest_at s M1} \<noteq> {}"
apply(auto simp add: some_commits_by_honest_at_def)
done

lemma some_messages_by_honest_intro :
  "\<exists>n\<in>Validators s. (\<exists>m. (n, m) \<in> Messages s) \<and> \<not> slashed s n \<Longrightarrow>
   {M1. some_messages_by_honest_at s M1} \<noteq> {}"
apply(auto simp add: some_messages_by_honest_at_def)
done


lemma finite_commits_by_honest :
  "finite_messages s \<Longrightarrow>
   finite {M1. some_commits_by_honest_at s M1}"
proof -
 assume "finite_messages s"
 then have "finite (Messages s)"
   by (simp add: finite_messages_def)
 moreover have "{m \<in> Messages s. \<exists> n h v. m = (n, Commit (h, v))} \<subseteq> Messages s"
   by blast
 ultimately have "finite {m \<in> Messages s. \<exists> n h v. m = (n, Commit (h, v))}"
   by auto
 moreover have "{m \<in> Messages s. \<exists> n h v. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, Commit (h, v))} \<subseteq>
                {m \<in> Messages s. \<exists> n h v. m = (n, Commit (h, v))}"
   by blast
 then have "finite {m \<in> Messages s. \<exists> n h v. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, Commit (h, v))}"
   using calculation infinite_super by auto
 then have "finite {view_of_signed_message m | m. m \<in> Messages s \<and> (\<exists> n h v. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, Commit (h, v)))}"
   by(rule Finite_Set.finite_image_set)
 moreover have " {view_of_signed_message m | m. m \<in> Messages s \<and> (\<exists> n h v. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, Commit (h, v)))}
               = {M1. some_commits_by_honest_at s M1}"
   apply (auto simp add: some_commits_by_honest_at_def view_of_signed_message_def view_of_message_def)
    apply auto[1]
   by force   
 ultimately show "finite {M1. some_commits_by_honest_at s M1}"
   by auto
qed

lemma finite_messages_by_honest :
  "finite_messages s \<Longrightarrow>
   finite {M1. some_messages_by_honest_at s M1}"
proof -
 assume "finite_messages s"
 then have "finite (Messages s)"
   by (simp add: finite_messages_def)
 moreover have "{m \<in> Messages s. \<exists> n p. m = (n, p)} \<subseteq> Messages s"
   by blast
 ultimately have "finite {m \<in> Messages s. \<exists> n p. m = (n, p)}"
   by auto
 moreover have "{m \<in> Messages s. \<exists> n p. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, p)} \<subseteq>
                {m \<in> Messages s. \<exists> n p. m = (n, p)}"
   by blast
 then have "finite {m \<in> Messages s. \<exists> n p. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, p)}"
   using calculation infinite_super by auto
 then have "finite {view_of_signed_message m | m. m \<in> Messages s \<and> (\<exists> n p. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, p))}"
   by(rule Finite_Set.finite_image_set)
 moreover have " {view_of_signed_message m | m. m \<in> Messages s \<and> (\<exists> n p. n \<in> Validators s \<and> (\<not> slashed s n) \<and> m = (n, p))}
               = {M1. some_messages_by_honest_at s M1}"
   by (auto simp add: some_messages_by_honest_at_def view_of_signed_message_def view_of_message_def)
 ultimately show "finite {M1. some_messages_by_honest_at s M1}"
   by auto
qed


lemma view_some_arithmetics :
  "(v :: view) \<le> x \<or> v \<noteq> x"
	by blast

lemma finite_views_have_max :
 "finite (views :: view set) \<Longrightarrow> views \<noteq> {} \<Longrightarrow>
  \<exists> v_max.
    v_max \<in> views \<and> (\<forall> v. v \<le> v_max \<or> v \<notin> views)"
apply(induct rule: finite_induct)
 apply blast
apply(case_tac "F = {}")
 apply (clarsimp)
apply clarsimp
apply(case_tac "x > v_max")
 apply(rule_tac x = x in exI)
 apply(clarsimp)
 apply(erule disjE)
  apply clarsimp
 apply force
apply(rule_tac x = v_max in exI)
apply clarsimp
apply force
done

lemma M1_prop_sub2 :
"\<exists> v_max. v_max \<in> {M1. some_commits_by_honest_at s M1}
    \<and> (\<forall> v. v \<le> v_max \<or> v \<notin> {M1. some_commits_by_honest_at s M1})
 \<Longrightarrow>
 \<exists>M1. M1 = - 1 \<and> (\<forall>n\<in>Validators s. (\<exists>h v. (n, Commit (h, v)) \<in> Messages s) \<longrightarrow> slashed s n) \<or>
     some_commits_by_honest_at s M1 \<and> no_commits_by_honest_after s M1"
 apply(clarsimp)
 apply(rule_tac x = v_max in exI)
 apply(rule disjI2)
 apply(rule conjI)
  apply(auto)
 apply(auto simp add: no_commits_by_honest_after_def some_commits_by_honest_at_def)
done

lemma M1_properties :
  "finite_messages s \<Longrightarrow>
   \<exists> M1.
     (M1 = -1 \<and> no_commits_by_honest s)
   \<or> (some_commits_by_honest_at s M1 \<and> no_commits_by_honest_after s M1)
   "
apply(case_tac "no_commits_by_honest s")
 apply(rule_tac x = "-1" in exI)
 apply simp
apply(simp add: no_commits_by_honest_def)
apply(drule some_commits_by_honest_intro)
apply(drule finite_commits_by_honest)
using M1_prop_sub2 finite_views_have_max by presburger


lemma M2_prop_sub2 :
"\<exists> v_max. v_max \<in> {M1. some_messages_by_honest_at s M1}
    \<and> (\<forall> v. v \<le> v_max \<or> v \<notin> {M1. some_messages_by_honest_at s M1})
 \<Longrightarrow>
 \<exists>M2. M2 = - 1 \<and> (\<forall>n\<in>Validators s. (\<exists>m. (n, m) \<in> Messages s) \<longrightarrow> slashed s n) \<or>
         some_messages_by_honest_at s M2 \<and> no_messages_by_honest_after s M2"
 apply(clarsimp)
 apply(rule_tac x = v_max in exI)
 apply(rule disjI2)
 apply(rule conjI)
  apply(auto)
 apply(auto simp add: no_messages_by_honest_after_def some_messages_by_honest_at_def)
done


lemma M2_properties:
  "finite_messages s \<Longrightarrow>
   \<exists> M2.
     (M2 = -1 \<and> no_messages_by_honest s)
   \<or> (some_messages_by_honest_at s M2 \<and> no_messages_by_honest_after s M2)
  "
apply(case_tac "no_messages_by_honest s")
 apply(rule_tac x = "-1" in exI)
 apply clarsimp
apply(simp add: no_messages_by_honest_def)
apply(drule some_messages_by_honest_intro)
apply(drule finite_messages_by_honest)
apply(rule_tac M2_prop_sub2)
using finite_views_have_max by blast

lemma no_messages_no_commits [simp] :
 "no_messages_by_honest s \<Longrightarrow> no_commits_by_honest s"
apply(simp add: no_messages_by_honest_def no_commits_by_honest_def)
apply blast
done

lemma no_messages_then_no_messages_after [simp] :
  "no_messages_by_honest s \<Longrightarrow> no_messages_by_honest_after s m"
apply(simp add: no_messages_by_honest_def no_messages_by_honest_after_def)
by blast

lemma no_messages_denies_somit_commits_at [simp] :
  "no_messages_by_honest s \<Longrightarrow>
       \<not> some_commits_by_honest_at s m"
by(auto simp add: no_messages_by_honest_def some_commits_by_honest_at_def)

lemma no_messages_denies_some_messages_at [simp] :
  "no_messages_by_honest s \<Longrightarrow>
   \<not> some_messages_by_honest_at s m"
apply(auto simp add: no_messages_by_honest_def some_messages_by_honest_at_def)
done

lemma no_commits_denies_some_commits_at [simp] :
  "no_commits_by_honest s \<Longrightarrow>
   no_commits_by_honest_after s M1"
apply(auto simp add: no_commits_by_honest_def no_commits_by_honest_after_def)
done

definition liveness_witness :: "hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> validator set \<Rightarrow> (validator * message) set"
where
"liveness_witness h M1 M2 ns =
   {(n, Prepare (h, M2 + 1, M1)) | n. n \<in> ns} \<union>
   {(n, Commit  (h, M2 + 1))     | n. n \<in> ns}"

lemma author_of_witness [simp] :
  "authors (liveness_witness h_new M1 M2 ns) = ns"
apply(simp add: authors_def liveness_witness_def)
by blast

lemma unslashed_can_use_witness [simp]:
 "unslashed_can_extend s
  \<lparr>Validators = Validators s,
   Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
   PrevHash = PrevHash s\<rparr>"
apply(simp add: unslashed_can_extend_def)
apply(rule_tac x  = " liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n}" in exI)
apply(simp add: unslashed_validators_def)
done

lemma more_than_two_thirds_mp :
  "finite (Validators s) \<Longrightarrow>
   \<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n \<Longrightarrow>
   more_than_two_thirds s f \<Longrightarrow> more_than_two_thirds s g"
proof (simp add: more_than_two_thirds_def)
 assume "\<forall>n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n"
 then have "{n \<in> Validators s. f n} \<subseteq> {n \<in> Validators s. g n}"
  by blast
 moreover assume "finite (Validators s)"
 then have "finite {n \<in> Validators s. g n}"
  by simp
 ultimately have "card {n \<in> Validators s. f n} \<le> card {n \<in> Validators s. g n}"
  by (simp add: card_mono)
 then show "2 * card (Validators s) < 3 * card {n \<in> Validators s. f n} \<Longrightarrow>
    2 * card (Validators s) < 3 * card {n \<in> Validators s. g n}"
  by linarith
qed

lemma witness_commits_inner :
  "Validators s \<noteq> {} \<and> finite (Validators s) \<Longrightarrow>
    more_than_two_thirds s (\<lambda>n. \<not> slashed s n) \<Longrightarrow>
    2 * card (Validators s)
    \<le> 3 * card {n \<in> Validators s. (n, Commit (h_new, M2 + 1)) \<in> Messages s \<or> n \<in> Validators s \<and> \<not> slashed s n}"
proof -
  assume "more_than_two_thirds s (\<lambda>n. \<not> slashed s n)"
  moreover assume "Validators s \<noteq> {} \<and> finite (Validators s)"
  ultimately have "more_than_two_thirds s (\<lambda> n. (n, Commit (h_new, M2 + 1)) \<in> Messages s \<or> \<not> slashed s n)"
    by (metis (no_types, lifting) more_than_two_thirds_mp)
  then have "
     (2 * card (Validators s) < 3 * card ({n. n \<in> Validators s \<and> ((n, Commit (h_new, M2 + 1)) \<in> Messages s \<or> \<not> slashed s n)}))
  "
    by (auto simp add: more_than_two_thirds_def)
  moreover have "
    {n \<in> Validators s. (n, Commit (h_new, M2 + 1)) \<in> Messages s \<or> n \<in> Validators s \<and> \<not> slashed s n} =
    {n. n \<in> Validators s \<and> ((n, Commit (h_new, M2 + 1)) \<in> Messages s \<or> \<not> slashed s n)}"
    by blast
  ultimately have " 2 * card (Validators s)
    < 3 * card {n \<in> Validators s. (n, Commit (h_new, M2 + 1)) \<in> Messages s \<or> n \<in> Validators s \<and> \<not> slashed s n}
  "
    by auto
  then show " 2 * card (Validators s)
    \<le> 3 * card {n \<in> Validators s. (n, Commit (h_new, M2 + 1)) \<in> Messages s \<or> n \<in> Validators s \<and> \<not> slashed s n}"
    by auto
qed

lemma witness_commits [simp] :
 "situation_has_finitely_many_validators s \<Longrightarrow>
   \<not> one_third_slashed s \<Longrightarrow>
  committed
  \<lparr>Validators = Validators s,
   Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
   PrevHash = PrevHash s\<rparr>
   h_new"
apply(simp add: committed_def one_third_slashed_def)
apply(rule_tac x = "M2 + 1"in exI)
apply(simp add: two_thirds_sent_message_def liveness_witness_def two_thirds_def one_third_def situation_has_finitely_many_validators_def)
using witness_commits_inner by blast

lemma two_thirds_transfer [simp] :
 "two_thirds \<lparr> Validators = Validators s, Messages = X, PrevHash = Y \<rparr> g =
  two_thirds s g"
apply(simp add: two_thirds_def)
done

lemma prepared_transfer :
 "finite (Validators s) \<Longrightarrow>
  prepared s ha v vs \<Longrightarrow>
  prepared
     \<lparr>Validators = Validators s,
      Messages = Messages s \<union> X,
      PrevHash = PrevHash s\<rparr>
     ha v vs"
apply(simp add: prepared_def two_thirds_sent_message_def)
apply(rule mp_two_thirds; simp)
done

lemma witness_has_certain_view :
 "(na, Commit (ha, v)) \<in> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n} \<Longrightarrow>
  v = M2 + 1
 "
apply(simp add: liveness_witness_def)
done

lemma witness_has_certain_hash :
 "(na, Commit (ha, v)) \<in> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n} \<Longrightarrow>
  ha = h_new
 "
apply(simp add: liveness_witness_def)
done

lemma more_than_two_thirds_imply_two_thirds :
 "more_than_two_thirds s f \<Longrightarrow>
  two_thirds s f"
apply(simp add: more_than_two_thirds_def two_thirds_def)
done

lemma witness_prepares:
  "situation_has_finitely_many_validators s \<Longrightarrow>
   \<not> one_third_slashed s \<Longrightarrow>
   prepared
        \<lparr>Validators = Validators s,
           Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
           PrevHash = PrevHash s\<rparr>
        h_new (M2 + 1) M1"
apply(simp add: prepared_def one_third_slashed_def liveness_witness_def
      two_thirds_sent_message_def)
apply(drule more_than_two_thirds_imply_two_thirds)
by (metis (no_types, lifting) mp_two_thirds situation_has_finitely_many_validators_def)


lemma commit_can_be_after_neg_one:
"situation_has_finitely_many_validators s \<Longrightarrow>
 n \<in> Validators s \<Longrightarrow>
 \<not> slashed s n \<Longrightarrow>
 (n, Commit (h, M1)) \<in> Messages s \<Longrightarrow>
 - 1 \<le> M1
"
	using condition_one_positive' by fastforce

lemma witness_not_slashed_one :
 "situation_has_finitely_many_validators s \<Longrightarrow>
  \<not> one_third_slashed s \<Longrightarrow>
  no_messages_by_honest_after s M2 \<Longrightarrow>
  n \<in> Validators s \<Longrightarrow>
  \<not> slashed s n \<Longrightarrow>
  (n, Commit (h, M1)) \<in> Messages s \<Longrightarrow>
  na \<in> Validators s \<Longrightarrow>
  slashed_one
  \<lparr>Validators = Validators s,
   Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
   PrevHash = PrevHash s\<rparr>
   na \<Longrightarrow>
  slashed_one s na"
apply(simp add: slashed_one_def)
apply clarsimp
apply(case_tac "(na, Commit (ha, v)) \<in> Messages s")
 apply(simp)
 apply(rule_tac x = ha in exI)
 apply(rule_tac x = v in exI)
 apply(clarsimp)
 apply(drule_tac x = vs in spec)
 apply(simp)
 using prepared_transfer situation_has_finitely_many_validators_def apply blast
apply(simp)
apply(drule_tac x = M1 in spec)
apply(subgoal_tac "v = M2 + 1"; simp add: witness_has_certain_view)
apply(subgoal_tac "ha = h_new"; simp add: witness_has_certain_hash)
apply clarsimp
apply (simp add: witness_prepares)
using commit_can_be_after_neg_one no_messages_by_honest_after_def view_of_message_def by fastforce

lemma nth_ancestor_transfers [simp] :
 "\<forall> N M s ha.
  nth_ancestor
  \<lparr>Validators = N,
   Messages = M,
   PrevHash = PrevHash s\<rparr>
   n ha =
   nth_ancestor s n ha"
apply(induction n; auto)
apply(case_tac "PrevHash s ha"; auto)
done

lemma witness_prepares_certain_hash :
  "(na, Prepare (ha, v, vs)) \<in> liveness_witness h_new M1 M2 validators \<Longrightarrow>
   ha = h_new"
apply(simp add: liveness_witness_def)
done

lemma witness_prepares_certain_view :
  "(na, Prepare (ha, v, vs)) \<in> liveness_witness h_new M1 M2 validators \<Longrightarrow>
   v = M2 + 1"
apply(simp add: liveness_witness_def)
done

lemma witness_commits_certain_view :
  "(n, Commit (h, v)) \<in> liveness_witness h_new M1 M2 validators \<Longrightarrow>
   v = M2 + 1"
apply(simp add: liveness_witness_def)
done

lemma witness_prepares_certain_view_src :
  "(na, Prepare (ha, v, vs)) \<in> liveness_witness h_new M1 M2 validators \<Longrightarrow>
   vs = M1"
apply(simp add: liveness_witness_def)
done

lemma it_is_somebody_that_prepares :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   \<not> one_third_slashed s \<Longrightarrow>
   prepared s h v v_src \<Longrightarrow>
   \<exists> n. n \<in> Validators s \<and>
     \<not> slashed s n \<and>
     (n, Prepare (h, v, v_src)) \<in> Messages s
  "
apply(auto simp add: situation_has_finitely_many_validators_def one_third_slashed_def prepared_def
      two_thirds_sent_message_def)
using situation_has_finitely_many_validators_def two_more_two_ex by force

lemma slashed_two_transfers :
   "situation_has_finitely_many_validators s \<Longrightarrow>
          \<not> one_third_slashed s \<Longrightarrow>
          no_messages_by_honest_after s M2 \<Longrightarrow>
          n \<in> Validators s \<Longrightarrow>
          \<not> slashed s n \<Longrightarrow>
          (n, Commit (h, M1)) \<in> Messages s \<Longrightarrow>
          nth_ancestor s (nat (M2 + 1 - M1)) h_new = Some h \<Longrightarrow>
          na \<in> Validators s \<Longrightarrow>
          slashed_two
           \<lparr>Validators = Validators s,
              Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
              PrevHash = PrevHash s\<rparr>
           na \<Longrightarrow>
          slashed_two s na"
apply(simp add: slashed_two_def)
apply clarsimp
apply(case_tac "(na, Prepare (ha, v, vs)) \<in> Messages s")
 apply(simp)
 apply(rule_tac x = ha in exI)
 apply(rule_tac x = v in exI)
 apply(rule_tac x = vs in exI)
 apply clarsimp
 apply(drule_tac x = h_anc in spec)
 apply clarsimp
 apply(drule_tac x = vs' in spec)
 apply clarsimp
 using prepared_transfer situation_has_finitely_many_validators_def apply blast
apply clarsimp
apply(subgoal_tac "ha = h_new")
 defer
 apply(simp add: witness_prepares_certain_hash)
apply(clarsimp)
apply(subgoal_tac "v = M2 + 1")
 defer
 apply(simp add: witness_prepares_certain_view)
apply(clarsimp)
apply(subgoal_tac "vs = M1")
 defer
 apply(simp add: witness_prepares_certain_view_src)
apply(clarsimp)
(* since h is committed, it is prepared at view M1 *)
apply(subgoal_tac "\<exists> h_src. -1 \<le> h_src \<and> h_src < M1 \<and> prepared s h M1 h_src")
 defer
 using slashed_def slashed_one_def apply blast
apply(clarsimp)
apply(drule_tac x = h_src in spec)
apply clarsimp
using prepared_transfer situation_has_finitely_many_validators_def by blast

lemma no_prepare_after :
  "no_messages_by_honest_after s M2 \<Longrightarrow>
   na \<in> Validators s \<Longrightarrow>
   (na, Prepare (y, w, u)) \<in> Messages s \<Longrightarrow>
   \<not> slashed s na \<Longrightarrow> w \<le> M2"
apply(simp add: no_messages_by_honest_after_def view_of_message_def)
by fastforce

lemma slashed_intro_three :
  "slashed_three s n \<Longrightarrow> slashed s n"
apply(simp add: slashed_def)
done

lemma no_commit_after :
  "    no_commits_by_honest_after s M1 \<Longrightarrow>
       na \<in> Validators s \<Longrightarrow>
       (na, Commit (x, v)) \<in> Messages s \<Longrightarrow> \<not> slashed s na \<Longrightarrow> v \<le> M1"
apply(simp add: no_commits_by_honest_after_def view_of_message_def)
by fastforce



lemma slashed_three_transfers :
 " situation_has_finitely_many_validators s \<Longrightarrow>
          \<not> one_third_slashed s \<Longrightarrow>
          no_commits_by_honest_after s M1 \<Longrightarrow>
          no_messages_by_honest_after s M2 \<Longrightarrow>
          na \<in> Validators s \<Longrightarrow>
          slashed_three
           \<lparr>Validators = Validators s,
              Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
              PrevHash = PrevHash s\<rparr>
           na \<Longrightarrow>
          slashed s na
"
apply(simp add: slashed_three_def)
apply clarsimp
apply(case_tac "(na, Prepare (y, w, u)) \<in> Messages s")
 apply(simp)
 apply(case_tac "(na, Commit (x, v)) \<in> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n}")
  apply simp
  apply(subgoal_tac "v = M2 + 1")
   apply clarsimp
   apply(subgoal_tac "\<not> slashed s na \<Longrightarrow> w \<le> M2")
    apply linarith
   using no_prepare_after apply blast
  apply(drule witness_commits_certain_view; simp)
 apply clarsimp
 apply(rule slashed_intro_three)
 apply(simp add: slashed_three_def)
 apply(rule_tac x = x in exI)
 apply(rule_tac x = y in exI)
 apply(rule_tac x = v in exI)
 apply blast
apply clarsimp
apply(subgoal_tac "w = M2 + 1")
 apply clarsimp
 apply(subgoal_tac "u = M1")
  apply clarsimp
  apply(case_tac "(na, Commit (x, v)) \<in> Messages s")
   apply(subgoal_tac "\<not> slashed s na \<Longrightarrow> v \<le> M1")
    apply linarith
   using no_commit_after apply blast
  apply clarsimp
  apply (subgoal_tac "v = M2 + 1")
   apply clarsimp
  using witness_commits_certain_view apply blast
 using witness_prepares_certain_view_src apply blast
using witness_prepares_certain_view by blast

lemma slashed_four_transfers :
"no_messages_by_honest_after s M2 \<Longrightarrow>
 na \<in> Validators s \<Longrightarrow>
    slashed_four
    \<lparr>Validators = Validators s,
              Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
              PrevHash = PrevHash s\<rparr>
           na \<Longrightarrow>
          slashed s na"
apply(simp add: slashed_four_def)
apply clarsimp
apply(case_tac "(na, Prepare (x1, v, vs1)) \<in> Messages s")
 apply clarsimp
 apply(subgoal_tac "\<not> slashed s na \<Longrightarrow> v \<le> M2")
  apply(case_tac "slashed s na"; simp)
  apply(case_tac "(na, Prepare (x2, v, vs2)) \<in> Messages s"; simp)
   apply(simp add: slashed_def)
   apply(simp add: slashed_four_def)
  apply(subgoal_tac "v = M2 + 1")
   apply linarith
  apply (simp add: witness_prepares_certain_view)
 using no_prepare_after apply blast
apply clarsimp
apply(subgoal_tac "v = M2 + 1")
 apply clarsimp
 apply(case_tac "(na, Prepare (x2, M2 + 1, vs2)) \<in> Messages s")
  apply clarsimp
  apply(subgoal_tac "\<not> slashed s na \<Longrightarrow> M2 + 1 \<le> M2")
   apply linarith
  using no_prepare_after apply blast
 apply clarsimp
 apply(subgoal_tac "vs1 = M1")
  apply clarsimp
  apply(subgoal_tac "vs2 = M1")
   apply clarsimp
   apply(subgoal_tac "x1 = h_new")
    apply clarsimp
    apply (subgoal_tac "x2 = h_new")
     apply clarsimp
    using witness_prepares_certain_hash apply blast
   using witness_prepares_certain_hash apply blast
  using witness_prepares_certain_view_src apply blast
 using witness_prepares_certain_view_src apply blast
using witness_prepares_certain_view apply blast
done


lemma slashed_destruct :
  "slashed s n \<Longrightarrow>
   slashed_one s n \<or> slashed_two s n \<or> slashed_three s n \<or> slashed_four s n"
apply(simp add: slashed_def)
done

lemma slashed_intro_two :
  "slashed_two s na \<Longrightarrow> slashed s na"
apply(simp add: slashed_def)
done

lemma slashed_intro_four :
  "slashed_four s na \<Longrightarrow> slashed s na"
apply(simp add: slashed_def)
done

lemma witness_not_guilty [simp]:
      "situation_has_finitely_many_validators s \<Longrightarrow>
       finite_messages s \<Longrightarrow>
       \<not> one_third_slashed s \<Longrightarrow>
       \<not> no_messages_by_honest s \<Longrightarrow>
       \<not> no_commits_by_honest s \<Longrightarrow>
       no_commits_by_honest_after s M1 \<Longrightarrow>
       some_messages_by_honest_at s M2 \<Longrightarrow>
       no_messages_by_honest_after s M2 \<Longrightarrow>
       n \<in> Validators s \<Longrightarrow>
       \<not> slashed s n \<Longrightarrow>
       (n, Commit (h, M1)) \<in> Messages s \<Longrightarrow>
       nth_ancestor s (nat (M2 + 1 - M1)) h_new = Some h \<Longrightarrow>
       \<not> committed s h_new \<Longrightarrow>
       no_new_slashed s
        \<lparr>Validators = Validators s,
           Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n},
           PrevHash = PrevHash s\<rparr>"
apply(auto simp add: no_new_slashed_def)
apply(drule slashed_destruct)
apply(auto)
   apply(subgoal_tac "slashed_one s na")
    apply(simp add: slashed_def)
   apply(rule_tac witness_not_slashed_one; blast)
  apply(rule slashed_intro_two)
  apply(rule_tac slashed_two_transfers; blast)
 apply(rule_tac slashed_three_transfers; blast)
apply(rule_tac slashed_four_transfers; blast)
done

lemma no_messages_cannot_commit :
  "situation_has_finitely_many_validators s \<Longrightarrow>
    \<not> one_third_slashed s \<Longrightarrow> no_messages_by_honest s \<Longrightarrow> \<not> committed s h"
	by (meson commit_expand committed_def it_is_somebody_that_prepares no_messages_by_honest_def)

lemma corner_kick :
  "situation_has_finitely_many_validators s \<Longrightarrow>
    finite_messages s \<Longrightarrow>
    \<not> one_third_slashed s \<Longrightarrow>
    no_messages_by_honest s \<Longrightarrow>
    no_new_slashed s
     \<lparr>Validators = Validators s,
        Messages = Messages s \<union> liveness_witness (Hash 0) (- 1) (- 1) {n \<in> Validators s. \<not> slashed s n},
        PrevHash = PrevHash s\<rparr>"
apply(simp add: no_new_slashed_def)
apply clarsimp
apply(case_tac "slashed s n"; simp)
apply(drule slashed_destruct)
apply auto
   apply(simp add: slashed_one_def)
   apply clarsimp
   apply(case_tac "(n, Commit (h, v)) \<in> Messages s")
    apply simp
    using no_messages_by_honest_def apply blast
   apply simp
   apply(simp add: liveness_witness_def)
   apply clarsimp
   apply(drule_tac x = "-1" in spec)
   apply clarsimp
   apply(simp add: prepared_def two_thirds_sent_message_def)
   apply (metis (no_types, lifting) more_than_two_thirds_imply_two_thirds mp_two_thirds not_one_third one_third_slashed_def situation_has_finitely_many_validators_def)
  apply(simp add: slashed_two_def)
  apply clarsimp
  apply(case_tac "(n, Prepare (h, v, vs)) \<in> Messages s")
   apply simp
   using no_messages_by_honest_def apply blast
  apply clarsimp
  apply(simp add: liveness_witness_def)
 apply(simp add: slashed_three_def)
 apply clarsimp
 apply(case_tac "(n, Commit (x, v)) \<in> Messages s")
  using no_messages_by_honest_def apply blast
 apply clarsimp
 apply(case_tac "(n, Prepare (y, w, u)) \<in> Messages s")
  using no_messages_by_honest_def apply blast
 apply clarsimp
 apply(simp add: liveness_witness_def)
apply(simp add: slashed_four_def)
apply clarsimp
apply(case_tac "(n, Prepare (x1, v, vs1)) \<in> Messages s")
 using no_messages_by_honest_def apply blast
apply(case_tac "(n, Prepare (x2, v, vs2)) \<in> Messages s")
 using no_messages_by_honest_def apply blast
apply clarsimp
apply(simp add: liveness_witness_def)
done

lemma at_least_neg_one :
        "no_invalid_view s \<Longrightarrow>
         some_messages_by_honest_at s M2 \<Longrightarrow>
         - 1 \<le> M2"
apply(auto simp add:
       no_invalid_view_def some_messages_by_honest_at_def message_has_valid_view_def
       view_of_message_def)
apply(drule_tac x = n in spec)
apply(drule_tac x = m in spec)
apply(case_tac m; auto)
done

lemma no_commit_new_slashed_three:
  "no_invalid_view s \<Longrightarrow>
         situation_has_finitely_many_validators s \<Longrightarrow>
         \<not> one_third_slashed s \<Longrightarrow>
         no_commits_by_honest s \<Longrightarrow>
         no_messages_by_honest_after s M2 \<Longrightarrow>
         n \<in> Validators s \<Longrightarrow>
         \<not> slashed s n \<Longrightarrow>
         slashed_three
          \<lparr>Validators = Validators s,
             Messages = Messages s \<union> liveness_witness (Hash 0) (- 1) M2 {n \<in> Validators s. \<not> slashed s n},
             PrevHash = PrevHash s\<rparr>
          n \<Longrightarrow>
         False"
apply(simp add: slashed_three_def)
apply clarsimp
 apply(case_tac "(n, Commit (x, v)) \<in> Messages s"; simp)
 using no_commits_by_honest_def apply blast
apply(case_tac "(n, Prepare (y, w, u)) \<in> Messages s"; simp)
 apply(simp add: liveness_witness_def)
 apply clarsimp
 using no_prepare_after apply fastforce
apply(simp add: liveness_witness_def)
done

lemma no_commit_new_slashed_four:
  "no_invalid_view s \<Longrightarrow>
   situation_has_finitely_many_validators s \<Longrightarrow>
   \<not> one_third_slashed s \<Longrightarrow>
   no_commits_by_honest s \<Longrightarrow>
   no_messages_by_honest_after s M2 \<Longrightarrow>
   n \<in> Validators s \<Longrightarrow>
   \<not> slashed s n \<Longrightarrow>
   slashed_four
    \<lparr>Validators = Validators s,
       Messages = Messages s \<union> liveness_witness (Hash 0) (- 1) M2 {n \<in> Validators s. \<not> slashed s n},
       PrevHash = PrevHash s\<rparr>
    n \<Longrightarrow>
   False"
apply(simp add: slashed_four_def)
apply clarsimp
apply(erule disjE)
 apply(erule disjE)
  apply(simp add: slashed_def slashed_four_def)
 apply(simp add: liveness_witness_def)
 apply clarsimp
 using no_prepare_after apply fastforce
apply(erule disjE)
 apply(simp add: liveness_witness_def)
 using no_prepare_after apply fastforce
apply(simp add: liveness_witness_def)
done


lemma two_thirds_sent_message_transfers :
  "finite (Validators s) \<Longrightarrow>
   two_thirds_sent_message s m \<Longrightarrow>
   two_thirds_sent_message
           \<lparr>Validators = Validators s,
              Messages =
                Messages s \<union> X,
              PrevHash = PrevHash s\<rparr> m"
apply(simp add: two_thirds_sent_message_def)
apply(rule mp_two_thirds; simp)
done

lemma no_commit_new_slashed_two:
  "no_invalid_view s \<Longrightarrow>
         situation_has_finitely_many_validators s \<Longrightarrow>
         \<not> one_third_slashed s \<Longrightarrow>
         no_commits_by_honest s \<Longrightarrow>
         some_messages_by_honest_at s M2 \<Longrightarrow>
         no_messages_by_honest_after s M2 \<Longrightarrow>
         n \<in> Validators s \<Longrightarrow>
         \<not> slashed s n \<Longrightarrow>
         slashed_two
          \<lparr>Validators = Validators s,
             Messages = Messages s \<union> liveness_witness (Hash 0) (- 1) M2 {n \<in> Validators s. \<not> slashed s n},
             PrevHash = PrevHash s\<rparr>
          n \<Longrightarrow>
         False"
apply(simp add: slashed_two_def)
apply clarsimp
apply(case_tac "(n, Prepare (h, v, vs)) \<in> Messages s"; simp)
 apply(simp add: slashed_def slashed_two_def)
 apply clarsimp
 apply(subgoal_tac "vs = - 1 \<or>
          (\<exists>h_anc. Some h_anc = nth_ancestor s (nat (v - vs)) h \<and>
                   (\<exists>vs'<vs. - 1 \<le> vs' \<and> prepared s h_anc vs vs'))")
  apply auto
  apply(drule_tac x = h_anc in spec)
  apply simp
  apply(drule_tac x = vs' in spec)
  apply clarsimp
  apply(simp add: prepared_def situation_has_finitely_many_validators_def two_thirds_sent_message_transfers)
 apply fastforce
apply(simp add: liveness_witness_def)
done

lemma corner_kick2 :
  "no_invalid_view s \<Longrightarrow>
   situation_has_finitely_many_validators s \<Longrightarrow>
   new_descendant_available s \<Longrightarrow>
   \<not> one_third_slashed s \<Longrightarrow>
   no_commits_by_honest s \<Longrightarrow>
   some_messages_by_honest_at s M2 \<Longrightarrow>
   no_messages_by_honest_after s M2 \<Longrightarrow>
   \<exists>s_new h_new.
      \<not> committed s h_new \<and>
      unslashed_can_extend s s_new \<and> committed s_new h_new \<and> no_new_slashed s s_new "
apply(rule_tac x =
   "\<lparr> Validators = Validators s
    , Messages = Messages s \<union> liveness_witness (Hash 0) (-1) M2 {n \<in> Validators s. \<not> slashed s n}
    , PrevHash = PrevHash s
    \<rparr>" in
 exI)
apply(rule_tac x = "Hash 0" in exI)
apply auto
 using committed_def no_commits_by_honest_def one_third_slashed_def two_more_two_ex two_thirds_sent_message_def apply fastforce
apply(auto simp add: no_new_slashed_def)
apply(drule slashed_destruct)
apply(case_tac "slashed s n"; auto)
   apply(simp add: slashed_one_def)
   apply clarsimp
   apply(case_tac "(n, Commit (h, v)) \<in> Messages s")
    using no_commits_by_honest_def apply blast
   apply clarsimp
   apply(simp add: liveness_witness_def)
   apply clarsimp
   apply(drule_tac x = "-1" in spec)
   apply clarsimp
   apply(subgoal_tac "- 1 \<le> M2")
    apply simp
    apply(simp add: prepared_def two_thirds_sent_message_def)
    apply (metis (no_types, lifting) more_than_two_thirds_imply_two_thirds more_than_two_thirds_mp not_one_third one_third_slashed_def situation_has_finitely_many_validators_def)
   using at_least_neg_one apply blast
  using no_commit_new_slashed_two apply blast
 using no_commit_new_slashed_three apply blast
using no_commit_new_slashed_four apply blast
done

section "Plausible Liveness (don't skip)"

text "The plausible liveness has a more complicated statement than account safety's.
If a situation has a finite number of validators (but not zero),
and if the situation contains no messages of invalid view numbers,
and if a new hash is available,
and if the situation does not contain infinitely many messages,
and if at most one-third of the validators are slashed,
there is a set of messages that the not-yet-slashed validators can send,
after which a new hash is committed but no new validator is slashed."

lemma plausible_liveness :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   no_invalid_view s \<Longrightarrow>
   new_descendant_available s \<Longrightarrow>
   finite_messages s \<Longrightarrow>
   \<not> one_third_slashed s \<Longrightarrow>
   \<exists> s_new h_new.
     \<not> committed s h_new \<and>
     unslashed_can_extend s s_new \<and>
     committed s_new h_new \<and>
     no_new_slashed s s_new
  "
apply(subgoal_tac "
   \<exists> M1.
     (M1 = -1 \<and> no_commits_by_honest s)
   \<or> (some_commits_by_honest_at s M1 \<and> no_commits_by_honest_after s M1)")
 defer
 apply(rule M1_properties; simp)
apply(subgoal_tac "\<exists> M2.
     (M2 = -1 \<and> no_messages_by_honest s)
   \<or> (some_messages_by_honest_at s M2 \<and> no_messages_by_honest_after s M2)")
 defer
 apply(rule M2_properties; simp)
apply clarsimp
apply(case_tac "no_messages_by_honest s")
 apply simp
 apply(rule_tac x =
   "\<lparr> Validators = Validators s
    , Messages = Messages s \<union> liveness_witness (Hash 0) M1 M2 {n \<in> Validators s. \<not> slashed s n}
    , PrevHash = PrevHash s
    \<rparr>" in
 exI)
 apply(rule_tac x = "Hash 0" in exI)
 apply(simp add: no_messages_cannot_commit)
 using corner_kick apply auto[1]
apply simp
apply(case_tac "no_commits_by_honest s")
 apply simp
 apply(case_tac "some_commits_by_honest_at s M1")
  using no_commits_by_honest_def some_commits_by_honest_at_def apply blast
 apply clarsimp
 apply(rule corner_kick2; blast)
apply clarsimp
apply(simp add: some_commits_by_honest_at_def)
apply clarsimp
apply(subgoal_tac
  "\<exists> h_new. nth_ancestor s (nat (M2 + 1 - M1)) h_new = Some h \<and>
            \<not> committed s h_new")
 apply clarsimp
 apply(rule_tac x =
   "\<lparr> Validators = Validators s
    , Messages = Messages s \<union> liveness_witness h_new M1 M2 {n \<in> Validators s. \<not> slashed s n}
    , PrevHash = PrevHash s
    \<rparr>" in
 exI)
 apply(rule_tac x = h_new in exI; simp)
apply(simp add: new_descendant_available_def)
apply(drule_tac x = n in spec)
apply(drule_tac x = h in spec)
apply(subgoal_tac " (\<exists>v. (n, Commit (h, v)) \<in> Messages s)")
 apply blast
apply blast
done

end
