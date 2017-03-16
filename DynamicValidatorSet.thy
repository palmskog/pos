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

definition validators_match :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_match s h0 h1 =
  (RearValidators s h0 = RearValidators s h1 \<and>
   FwdValidators s h0 = FwdValidators s h1)"

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

(* TODO: consider allow changing the FWD set during this. *)
definition prev_hash_under_same_validators :: "situation \<Rightarrow> hash \<Rightarrow> hash option"
where
  "prev_hash_under_same_validators s h =
    (case PrevHash s h of
       None \<Rightarrow> None
     | Some h' \<Rightarrow>
        (if RearValidators s h = RearValidators s h' \<and> FwdValidators s h = FwdValidators s h' then
            Some h'
         else
            None))"

fun nth_ancestor_under_same_validators  :: "situation \<Rightarrow> nat \<Rightarrow> hash \<Rightarrow> hash option"
where
  "nth_ancestor_under_same_validators _ 0 h = Some h"
| "nth_ancestor_under_same_validators s (Suc n) h =
    (case prev_hash_under_same_validators s h of
       None \<Rightarrow> None
     | Some h' \<Rightarrow> nth_ancestor_under_same_validators s n h')"

text "And also we are allowed to talk if two hashes are in ancestor-descendant relation.
It does not matter if there is an algorithm to decide this."

definition is_descendant_or_self :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"is_descendant_or_self s x y = (\<exists> n. nth_ancestor s n x = Some y)"

definition is_descendant_under_same_validators :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"is_descendant_under_same_validators s x y =
   (\<exists> n. nth_ancestor_under_same_validators s n x = Some y)"

text "We can also talk if two hashes are not in ancestor-descendant relation in whichever ways."

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

definition prepared_by_rear :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_rear s h v vsrc =
   (prepared s (RearValidators s h) h v vsrc)"

definition prepared_by_fwd :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_fwd s h v vsrc =
   (prepared s (FwdValidators s h) h v vsrc)"

(* This thing is necessary; consider change-no-change conflict.  *)
definition prepared_by_both :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_both s h v vsrc =
  (prepared_by_rear s h v vsrc \<and> prepared_by_fwd s h v vsrc)"

text "A hash is committed when two-thirds of the validators have sent a certain message."

definition committed :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed s vs h v = two_thirds_sent_message s vs (Commit (h, v))"

definition committed_by_rear :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_rear s h v =
   (committed s (RearValidators s h) h v)"

definition committed_by_fwd :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_fwd s h v =
   (committed s (FwdValidators s h) h v)"

definition committed_by_both :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_both s h v =
   (committed_by_rear s h v \<and>
    committed_by_fwd s h v)"

section "Electing the New Validators (not skippable)"

fun sourcing_normal :: "situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing_normal s h (h', v', v_src) =
  (\<exists> v_ss.
   prepared_by_both s h v_src v_ss \<and>
   -1 \<le> v_src \<and>
   v_src < v' \<and>
   nth_ancestor s (nat (v' - v_src)) h' = Some h \<and>
   validators_match s h h' )"

definition validators_change :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_change s ancient next =
   (FwdValidators s next = RearValidators s ancient)"

fun sourcing_switching_validators ::
"situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing_switching_validators s h (h', v', v_src) =
  (\<exists> v_ss.
   prepared_by_both s h v_src v_ss \<and>
   committed_by_both s h v_src \<and>
   -1 \<le> v_src \<and>
   v_src < v' \<and>
   nth_ancestor s (nat (v' - v_src)) h' = Some h \<and>
   validators_change s h h')"

definition sourcing :: "situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing s h_new tri = (sourcing_normal s h_new tri \<or> sourcing_switching_validators s h_new tri)"

(* TODO: I'm wondering if I should keep v and v_src in an existential quantifier here, or
   expose it as an argument. *)

(* The two very similar definitions are not combined
 * just for easily counting the number of switching.
 *)
fun inherit_normal :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"inherit_normal s (h_old, v_src) (h_new, v) =
   (prepared_by_both s h_new v v_src \<and>
    sourcing_normal s h_old (h_new, v, v_src))"

lemma inherit_normal_view_increase :
  "inherit_normal s (h_old, v_src) (h_new, v) \<Longrightarrow>
   (v_src < v)"
apply(simp)
done

fun inherit_switching_validators ::
  "situation \<Rightarrow> (hash \<times> view) \<Rightarrow>
                (hash \<times> view) \<Rightarrow> bool"
where
"inherit_switching_validators s (h_old, v_old) (h_new, v_new) =
   (prepared_by_both s h_new v_new v_old \<and>
    sourcing_switching_validators s h_old (h_new, v_new, v_old))"

lemma inherit_switching_validators_increase_view :
 "inherit_switching_validators s (h_old,v_old) (h_new, v_new) \<Longrightarrow>
  v_old < v_new"
apply(simp)
done


inductive heir :: "situation \<Rightarrow>
                   (hash \<times> view) \<Rightarrow> 
                   (hash \<times> view) \<Rightarrow> bool"
where
  heir_self : "prepared_by_both s h v v_src \<Longrightarrow> heir s (h, v) (h, v)"
| heir_normal_step : "heir s (h, v) (h', v') \<Longrightarrow>
                 inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
                 heir s (h, v) (h'', v'')"
| heir_switching_step : "heir s (h, v) (h', v') \<Longrightarrow>
                 inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
                 heir s (h, v) (h'', v'')"

definition on_same_heir_chain :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"on_same_heir_chain s x y = (heir s x y \<or> heir s y x)"


lemma heir_decomposition :
  "heir s (h, v) (h'', v'') \<Longrightarrow>
    ((\<exists> v_src. h = h'' \<and> v = v'' \<and> prepared_by_both s h v v_src) \<or>
     (\<exists> h' v'. heir s (h, v) (h', v') \<and> inherit_normal s (h', v') (h'', v'')) \<or>
     (\<exists> h' v'. heir s (h, v) (h', v') \<and> inherit_switching_validators s (h', v') (h'', v''))
    )"
apply(erule_tac DynamicValidatorSet.heir.cases)
  apply(rule disjI1)
  apply blast
 apply(rule disjI2)
 apply(rule disjI1)
 apply blast
apply(rule disjI2)
apply(rule disjI2)
by blast


lemma heir_increases_view :
  "heir s t t' \<Longrightarrow> snd t \<le> snd t'"
apply(induction rule: heir.induct; auto)
done

inductive heir_after_n_switching ::
   "nat \<Rightarrow> situation \<Rightarrow>
    (hash \<times> view) \<Rightarrow>
    (hash \<times> view) \<Rightarrow> bool"
where
  heir_n_self : "prepared_by_both s h v v_src \<Longrightarrow> heir_after_n_switching 0 s (h, v) (h, v)"
| heir_n_normal_step :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
    heir_after_n_switching n s (h, v) (h'', v'')"
| heir_n_switching_step :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
    heir_after_n_switching (Suc n) s (h, v) (h'', v'')"

lemma every_heir_is_after_n_switching :
"heir s p0 p1 \<Longrightarrow> \<exists> n. heir_after_n_switching n s p0 p1"
apply(induction rule: heir.induct)
  apply(rule_tac x = 0 in exI)
  apply (simp add: heir_n_self)
 apply clarify
 apply(rule_tac x = n in exI)
 apply(rule heir_n_normal_step; blast)
apply clarify
using heir_n_switching_step by blast

fun fork :: "situation \<Rightarrow>
                    (hash \<times> view) \<Rightarrow>
                    (hash \<times> view) \<Rightarrow>
                    (hash \<times> view) \<Rightarrow> bool"
where
"fork s (root, v) (h1, v1) (h2, v2) =
  (\<not> on_same_heir_chain s (h1, v1) (h2, v2) \<and> heir s (root, v) (h1, v1) \<and> heir s (root, v) (h2, v2))"

fun fork_with_n_switching :: "situation \<Rightarrow>
             (hash \<times> view) \<Rightarrow>
             nat \<Rightarrow> (hash \<times> view) \<Rightarrow>
             nat \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"fork_with_n_switching
   s (root, v) n1 (h1, v1) n2 (h2, v2) =
   (\<not> on_same_heir_chain s (h1, v1) (h2, v2) \<and>
    heir_after_n_switching n1 s (root, v) (h1, v1) \<and>
    heir_after_n_switching n2 s (root, v) (h2, v2))"

lemma fork_has_n_switching :
  "fork s (r, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> n1 n2. fork_with_n_switching s (r, v) n1 (h1, v1) n2 (h2, v2)"
apply(simp)
using every_heir_is_after_n_switching by blast

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

definition validators_transition :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_transition s h0 h1 =
  (FwdValidators s h0 = RearValidators s h1)"

definition slashed_two :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_two s n =
  (\<exists> h v v_src.
       ((n, Prepare (h, v, v_src)) \<in> Messages s \<and>
       v_src \<noteq> -1 \<and>
       (\<not> (\<exists> h_anc.
               sourcing s h_anc (h, v, v_src)))))"

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


definition on_same_chain :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"on_same_chain s x y = (is_descendant_or_self s x y \<or> is_descendant_or_self s y x)"


lemma dependency_self [simp]:
  "on_same_chain s y y"
apply(simp add: on_same_chain_def)
apply(simp add: is_descendant_or_self_def)
apply(rule_tac x = 0 in exI)
apply(simp)
done

lemma prepare_direct_conflict :
 "\<not> on_same_chain s x y \<Longrightarrow>
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
 "on_same_chain s x y = on_same_chain s y x"
apply(auto simp add: on_same_chain_def)
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

lemma heir_same_height :
 "heir s (h', v) (h, v) \<Longrightarrow>
  h' = h"
apply(drule heir_decomposition)
using heir_increases_view apply force
done

section "Accountable Safety (don't skip)"

text "The statement of accountable safety is simple.  If a situation has a finite number of validators (but not zero),
if two hashes x and y are committed in the situation, but if the two hashes are not on the same chain,
at least one-third of the validators are slashed in the situation."


lemma sum_is_suc_dest :
   "Suc n = n1 + n2 \<Longrightarrow>
    ((\<exists> n1'. n1 = Suc n1' \<and> n = n1' + n2) \<or>
     (\<exists> n2'. n2 = Suc n2' \<and> n = n1 + n2'))
   "
apply (case_tac n1; auto)
done

definition one_third_of_rear_slashed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"one_third_of_rear_slashed s h = one_third (RearValidators s h) (slashed s)"

definition one_third_of_fwd_slashed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"one_third_of_fwd_slashed s h = one_third (FwdValidators s h) (slashed s)"

definition one_third_of_rear_or_fwd_slashed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"one_third_of_rear_or_fwd_slashed s h =
   (one_third_of_rear_slashed s h \<or> one_third_of_fwd_slashed s h)"

fun fork_with_center :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) =
   (fork s (h, v) (h1, v1) (h2, v2) \<and>
    heir s (h_orig, v_orig) (h, v) \<and> (* This is used to connect the whole setup with the original statement *)
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"

fun fork_with_center_with_n_switching :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow>
      (hash \<times> view) \<Rightarrow> nat \<Rightarrow> (hash \<times> view) \<Rightarrow> nat \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"fork_with_center_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2) =
   (fork_with_n_switching s (h, v) n1 (h1, v1) n2 (h2, v2) \<and>
    heir s (h_orig, v_orig) (h, v) \<and> (* This is used to connect the whole setup with the original statement *)
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"

lemma fork_with_center_has_n_switching :
  "fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> n1 n2.
    fork_with_center_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2)"
apply simp
using every_heir_is_after_n_switching by blast

fun fork_with_commits :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"fork_with_commits s (h, v) (h1, v1) (h2, v2) =
   (fork s (h, v) (h1, v1) (h2, v2) \<and>
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"

(* Finding a max element in a set of integers *)
lemma find_max_ind_step :
  "\<forall>u. n = nat (u - s) \<longrightarrow> s \<in> (S :: int set) \<longrightarrow> (\<forall>x. x \<in> S \<longrightarrow> x \<le> u)
                         \<longrightarrow> (\<exists>m. m \<in> S \<and> (\<forall>y>m. y \<notin> S)) \<Longrightarrow>
   Suc n = nat (u - s) \<Longrightarrow> s \<in> S \<Longrightarrow> \<forall>x. x \<in> S \<longrightarrow> x \<le> u \<Longrightarrow> \<exists>m. m \<in> S \<and> (\<forall>y>m. y \<notin> S)"
apply(case_tac "\<forall> x. x \<in> S \<longrightarrow> x \<le> u - 1")
 apply(drule_tac x = "u - 1" in spec)
 apply simp
by force


lemma find_max_ind :
  "\<forall> u.
   n = nat (u - s) \<longrightarrow>
   s \<in> (S :: int set) \<longrightarrow>
   (\<forall> x. x \<in> S \<longrightarrow> x \<le> u) \<longrightarrow>
   (\<exists> m. m \<in> S \<and>
      (\<forall> y. y > m \<longrightarrow> y \<notin> S))"
apply(induction n; auto)
 apply force
apply(rule_tac n = n and u = u and S = S and s = s in find_max_ind_step; auto)
done

lemma find_max :
  "s \<in> (S :: int set) \<Longrightarrow>
   \<forall> x. x \<in> S \<longrightarrow> x \<le> u \<Longrightarrow>
   \<exists> m. m \<in> S \<and>
      (\<forall> y. y > m \<longrightarrow> y \<notin> S)"
using find_max_ind by auto

fun fork_root_views :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> view set"
where
"fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2) =
  { v. (\<exists> h. fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2)) }"

(* It's convenient to have a fork's root as the latest commit immediately before the fork.
 * Otherwise the induction has hairier case analysis.
 *)
fun fork_with_center_with_high_root ::
  "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
  "fork_with_center_with_high_root s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) =
     (fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<and>
      (\<forall> h' v'. v' > v \<longrightarrow>
        \<not> fork_with_center s (h_orig, v_orig) (h', v') (h1, v1) (h2, v2)))"

fun fork_with_center_with_high_root_with_n_switching ::
  "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> nat \<Rightarrow> (hash \<times> view) \<Rightarrow>
                nat \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
  "fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2) =
     (fork_with_center_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2) \<and>
      (\<forall> h' v'. v' > v \<longrightarrow>
        \<not> fork_with_center s (h_orig, v_orig) (h', v') (h1, v1) (h2, v2)))"

lemma fork_with_center_with_high_root_has_n_switching :
  "fork_with_center_with_high_root s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> n1 n2.
     fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2)"
apply simp
using every_heir_is_after_n_switching by blast

lemma fork_with_center_choose_high_root :
  "fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> h' v'. fork_with_center_with_high_root s (h_orig, v_orig) (h', v') (h1, v1) (h2, v2)"
proof -
 assume "fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2)"
 then have "v \<in> fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2)"
   by auto
 moreover have "\<forall> x. x \<in> fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2) \<longrightarrow> x \<le> v1"
   using heir_increases_view by auto
 ultimately have "\<exists> m. m \<in> fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2) \<and>
                   (\<forall> y. y > m \<longrightarrow> y \<notin> fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2))"
   by(rule_tac find_max; auto)
 then show ?thesis
   by (clarsimp; blast)
qed

lemma forget_number_of_switching:
 "heir_after_n_switching n s (h_twoa, v_twoa) (h_one, v_one)
  \<Longrightarrow> heir s (h_twoa, v_twoa) (h_one, v_one)"
apply(induction rule: heir_after_n_switching.induct)
  apply (simp add: heir_self)
 using heir_normal_step apply blast
using heir_switching_step by blast

lemma accountable_safety_from_fork_with_high_root_base :
"n_one \<le> 1 \<and>
 n_two \<le> 1 \<and>
 prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
(* the forward set of h should have one-third slashed here. *)
sorry

lemma sum_suc_disj :
 "n_one + n_two \<le> Suc k \<Longrightarrow>
  n_one + n_two \<le> k \<or>
  n_one + n_two = Suc k"
using le_SucE by blast

lemma sum_eq_disj :
"((n_one :: nat) \<le> 1 \<and> (n_two :: nat) \<le> 1) \<or>
  n_one > 1 \<or> n_two > 1
"
by auto

lemma sum_eq_case1 :
  "n_one + n_two = Suc k \<Longrightarrow>
   n_one > 1 \<Longrightarrow>
   \<exists> n_one_pre. n_one_pre \<ge> 1 \<and> n_one = Suc n_one_pre \<and> n_one_pre + n_two = k"
using less_imp_Suc_add by fastforce

lemma sum_eq_case2 :
  "n_one + n_two = Suc k \<Longrightarrow>
   n_two > 1 \<Longrightarrow>
   \<exists> n_two_pre. n_two_pre \<ge> 1 \<and> n_two = Suc n_two_pre \<and> n_one + n_two_pre = k"
by presburger
 

lemma sum_suc :
 "n_one + n_two \<le> Suc k \<Longrightarrow>
  n_one + n_two \<le> k \<or>
  n_one \<le> 1 \<and> n_two \<le> 1 \<or>
  (\<exists> n_one_pre. n_one_pre \<ge> 1 \<and> n_one = Suc n_one_pre \<and> n_one_pre + n_two = k) \<or>
  (\<exists> n_two_pre. n_two_pre \<ge> 1 \<and> n_two = Suc n_two_pre \<and> n_one + n_two_pre = k)
 "
using sum_eq_case1 sum_eq_case2 by auto

lemma heir_normal_extend :
      "(\<exists>h_one v_one h_two v_two.
           heir_after_n_switching n s (h, v) (h_one, v_one) \<and>
           inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
           heir_after_n_switching 0 s (h_two, v_two) (h', v')) \<Longrightarrow>
       inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
       (\<exists>h_one v_one h_two v_two.
           heir_after_n_switching n s (h, v) (h_one, v_one) \<and>
           inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
           heir_after_n_switching 0 s (h_two, v_two) (h'', v''))"
apply clarify
apply(rule_tac x = h_one in exI)
apply(rule_tac x = v_one in exI)
apply(rule_tac x = h_two in exI)
apply(rule_tac x = v_two in exI)
apply simp
using heir_n_normal_step inherit_normal.simps sourcing_normal.simps by blast

lemma heir_found_switching :
  "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
   inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
   0 < Suc n \<Longrightarrow>
   \<exists>h_one v_one h_two v_two.
      heir_after_n_switching (Suc n - 1) s (h, v) (h_one, v_one) \<and>
      inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
      heir_after_n_switching 0 s (h_two, v_two) (h'', v'')"
apply(rule_tac x = h' in exI)
apply(rule_tac x = v' in exI)
apply(rule_tac x = h'' in exI)
apply(rule_tac x = v'' in exI)
apply simp
using heir_n_self by blast

lemma heir_trans :
  "heir s (h_r, v_r) (h', v') \<Longrightarrow>
   heir s (h, v) (h_r, v_r) \<Longrightarrow>
   heir s (h, v) (h', v')"
apply(induction rule: heir.induct; auto)
 apply(rule_tac h' = h' and v' = v' in heir_normal_step; auto)
apply(rule_tac h' = h' and v' = v' in heir_switching_step; auto)
done


lemma heir_after_one_or_more_switching_dest :
  "heir_after_n_switching na s (h, v) (h_three, v_three) \<Longrightarrow>
   na > 0 \<Longrightarrow>
   (\<exists> h_one v_one h_two v_two.
    heir_after_n_switching (na - 1) s (h, v) (h_one, v_one) \<and>
    inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
    heir_after_n_switching 0 s (h_two, v_two) (h_three, v_three))
  "
apply(induction rule: heir_after_n_switching.induct)
  apply simp
 using heir_normal_extend apply blast
using heir_found_switching by blast

lemma high_point_still_high :
(* remove unnecessary assumptions *)
      "1 \<le> n_one_pre \<Longrightarrow>
       \<forall>h' v'. v < v' \<longrightarrow> \<not> fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
       \<not> on_same_heir_chain s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
       heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
       heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
       committed_by_both s h v \<Longrightarrow>
       committed_by_both s h_one v_one \<Longrightarrow>
       committed_by_both s h_two v_two \<Longrightarrow>
       heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
       inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
       heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
       \<forall>h' v'. v < v' \<longrightarrow> \<not> fork_with_center s (h_orig, v_orig) (h', v') (h_onea, v_onea) (h_two, v_two)"
sorry

lemma at_least_one_switching_means_higher :
  "heir_after_n_switching n_one_pre s (h, v) (h_onea, v_onea) \<Longrightarrow>
   Suc 0 \<le> n_one_pre \<Longrightarrow>
   snd (h, v) < snd (h_onea, v_onea)"
apply(induction rule: heir_after_n_switching.induct; auto)
using forget_number_of_switching heir_increases_view by fastforce

lemma shallower_fork :
   "heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_one v_one \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
    inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_two, v_two) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir s (h_onea, v_onea) (h_two, v_two) \<Longrightarrow>
    v < v_onea \<Longrightarrow> fork_with_center s (h_orig, v_orig) (h_onea, v_onea) (h_one, v_one) (h_two, v_two)"
apply(simp only: fork_with_center.simps)
apply(rule conjI)
 apply(simp only:fork.simps)
  apply (meson forget_number_of_switching heir_self heir_switching_step heir_trans inherit_switching_validators.simps on_same_heir_chain_def sourcing_switching_validators.simps)
by (meson forget_number_of_switching heir_trans inherit_switching_validators.simps sourcing_switching_validators.simps)

lemma use_highness :
 "1 \<le> n_one_pre \<Longrightarrow>
    \<forall>h' v'. v < v' \<longrightarrow> \<not> fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_one v_one \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
    inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_two, v_two) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_one, v_one) (h_two, v_two) \<Longrightarrow> heir s (h_onea, v_onea) (h_two, v_two) \<Longrightarrow> False"
apply(drule_tac x = h_onea in spec)
apply(drule_tac x = v_onea in spec)
apply(subgoal_tac "v < v_onea")
 defer
 apply (metis One_nat_def at_least_one_switching_means_higher diff_Suc_1 snd_conv)
apply(subgoal_tac "fork_with_center s (h_orig, v_orig) (h_onea, v_onea) (h_one, v_one) (h_two, v_two)")
 apply blast
using shallower_fork by blast

lemma confluence_should_not:
  "1 \<le> n_one_pre \<Longrightarrow>
    \<forall>h' v'. v < v' \<longrightarrow> \<not> fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_one v_one \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
    inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_two, v_two) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_one, v_one) (h_two, v_two) \<Longrightarrow> heir s (h_two, v_two) (h_onea, v_onea) \<Longrightarrow> False"
proof -
  assume "inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa)"
  then have "heir s (h_onea, v_onea) (h_twoa, v_twoa)"
    by (meson heir_self heir_switching_step inherit_switching_validators.simps sourcing_switching_validators.simps)
  moreover assume "heir s (h_two, v_two) (h_onea, v_onea)"
  ultimately have "heir s (h_two, v_two) (h_twoa, v_twoa)"
    using \<open>inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa)\<close> heir_switching_step by blast
  moreover assume "heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one)"
  then have "heir s (h_twoa, v_twoa) (h_one, v_one)"
    using forget_number_of_switching by blast
  ultimately have "heir s (h_two, v_two) (h_one, v_one)"
    using heir_trans by blast
  moreover assume " \<not> heir s (h_two, v_two) (h_one, v_one)"
  ultimately show "False"
    by blast
qed

lemma prev_switch_not_on_same_heir_chain :
"1 \<le> n_one_pre \<Longrightarrow>
\<forall>h' v'. v < v' \<longrightarrow> \<not> fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
 \<not> on_same_heir_chain s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
 heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
 heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
 committed_by_both s h v \<Longrightarrow>
 committed_by_both s h_one v_one \<Longrightarrow>
 committed_by_both s h_two v_two \<Longrightarrow>
 heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
 inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
 heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
 \<not> on_same_heir_chain s (h_onea, v_onea) (h_two, v_two)"
apply(auto simp only: on_same_heir_chain_def)
  using use_highness apply blast
using confluence_should_not by blast

lemma reduce_fork :
   "fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) (Suc n_one_pre) (h_one, v_one)
     n_two (h_two, v_two) \<Longrightarrow>
    1 \<le> n_one_pre \<Longrightarrow>
    \<exists>h_one' v_one'.
       fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one_pre (h_one', v_one')
        n_two (h_two, v_two)"
apply (simp only: fork_with_center_with_high_root_with_n_switching.simps)
apply (simp only: fork_with_center_with_n_switching.simps)
apply (simp only: fork_with_n_switching.simps)
apply clarify
apply(drule
 heir_after_one_or_more_switching_dest)
 apply simp
apply clarify
apply(rule_tac x = "h_onea" in exI)
apply(rule_tac x = "v_onea" in exI)
apply(rule conjI)
 apply(rule conjI)
  apply(rule conjI)
   using prev_switch_not_on_same_heir_chain apply blast
  apply auto[1]
 apply auto[1]
using high_point_still_high by blast

lemma switching_induction_case_one :
  "\<forall>n_one n_twoa h_one v_one h_two v_two.
    n_one + n_twoa \<le> n_one_pre + n_two \<longrightarrow>
    prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
    fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_twoa
     (h_two, v_two) \<longrightarrow>
     (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
    prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
    fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) (Suc n_one_pre) (h_one, v_one)
    n_two (h_two, v_two) \<Longrightarrow>
    1 \<le> n_one_pre \<Longrightarrow>
    k = n_one_pre + n_two \<Longrightarrow>
    \<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h'"
apply (subgoal_tac
"\<exists> h_one' v_one'.
 fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one_pre (h_one', v_one')
  n_two (h_two, v_two)")
 apply blast
using reduce_fork by blast

lemma on_same_heir_chain_sym :
 "on_same_heir_chain s (h_one, v_one) (h_two, v_two) =
  on_same_heir_chain s (h_two, v_two) (h_one, v_one)"
	using on_same_heir_chain_def by auto

lemma fork_with_center_with_high_root_with_n_switching_sym :
   "fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one)
     n_two (h_two, v_two) \<Longrightarrow>
    fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_two (h_two, v_two)
     n_one (h_one, v_one)"
apply auto
using on_same_heir_chain_sym by blast

lemma some_symmetry :
  "\<forall>n_onea n_two h_one v_one h_two v_two.
       n_onea + n_two \<le> n_one + n_two_pre \<longrightarrow>
       prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
       fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_two
        (h_two, v_two) \<longrightarrow>
       (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
    \<forall>n_onea n_twoa h_one v_one h_two v_two.
       n_onea + n_twoa \<le> n_two_pre + n_one \<longrightarrow>
       prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
       fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_twoa
        (h_two, v_two) \<longrightarrow>
       (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h')"
apply clarify
apply (drule_tac x = n_onea in spec)
apply (drule_tac x = n_twoa in spec)
apply(drule_tac x = h_one in spec)
apply(drule_tac x = v_one in spec)
apply(drule_tac x = h_two in spec)
apply(drule_tac x = v_two in spec)
apply(erule impE)
 apply auto[1]
apply(erule impE)
 apply simp
apply(erule impE)
 apply blast
apply blast
done


lemma switching_induction_case_two :
"       \<forall>n_onea n_two h_one v_one h_two v_two.
          n_onea + n_two \<le> n_one + n_two_pre \<longrightarrow>
          prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
          fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_two
           (h_two, v_two) \<longrightarrow>
          (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
       prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
       fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one)
        (Suc n_two_pre) (h_two, v_two) \<Longrightarrow>
       1 \<le> n_two_pre \<Longrightarrow>
       k = n_one + n_two_pre \<Longrightarrow>
       \<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h'"
apply(rule_tac k = k and n_two = n_one and n_one_pre = n_two_pre and h = h and v = v
      and h_one = h_two and v_one = v_two and h_two = h_one and v_two = v_one
 in switching_induction_case_one)
defer
apply simp
using fork_with_center_with_high_root_with_n_switching_sym apply blast
using add.commute apply blast
apply simp
by (simp add: add.commute)

lemma switching_induction :
  "\<forall>n_one n_two h_one v_one h_two v_two.
            n_one + n_two \<le> k \<longrightarrow>
            prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
            fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two
             (h_two, v_two) \<longrightarrow>
            (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
         \<forall>n_one n_two h_one v_one h_two v_two.
            n_one + n_two \<le> Suc k \<longrightarrow>
            prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
            fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two
             (h_two, v_two) \<longrightarrow>
            (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h')"
apply clarify
apply (drule sum_suc)
apply (erule disjE)
 apply blast
apply (erule disjE)
  using accountable_safety_from_fork_with_high_root_base apply blast
apply (erule disjE)
 apply clarify
 using switching_induction_case_one apply blast
apply clarify
using switching_induction_case_two apply blast
done

lemma accountable_safety_from_fork_with_high_root_with_n_ind :
"\<forall> n_one n_two h_one v_one h_two v_two.
 n_one + n_two \<le> k \<longrightarrow>
 prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<longrightarrow>
 (\<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h')"
apply(induction k)
 using accountable_safety_from_fork_with_high_root_base apply blast
using switching_induction by blast

lemma accountable_safety_from_fork_with_high_root_with_n :
"prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
using accountable_safety_from_fork_with_high_root_with_n_ind by blast

lemma accountable_safety_from_fork_with_high_root :
"prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
 fork_with_center_with_high_root s (h_orig, v_orig) (h, v) (h_one, v_one) (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
by (meson accountable_safety_from_fork_with_high_root_with_n fork_with_center_with_high_root_has_n_switching)


lemma accountable_safety_center :
"prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
 fork_with_center s (h, v) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h, v) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
apply(drule fork_with_center_choose_high_root)
apply(clarify)
using accountable_safety_from_fork_with_high_root by blast

lemma heir_initial :
   "heir s (h, v) (h1, v1)  \<Longrightarrow>
    heir s (h, v) (h, v)"
apply(induction rule: heir.induct)
  using heir_self apply auto[1]
 apply simp
apply simp
done

lemma fork_with_center_and_root :
  " fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
    fork_with_center s (h, v) (h, v) (h1, v1) (h2, v2)
  "
apply simp
using heir_initial by blast

lemma accountable_safety :
"prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
 fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h, v) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
using accountable_safety_center fork_with_center_and_root by blast


end
