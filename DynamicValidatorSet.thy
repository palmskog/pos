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

definition not_on_same_chain :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"not_on_same_chain s x y = ((\<not> is_descendant_or_self s x y) \<and> (\<not> is_descendant_or_self s y x))"

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

definition prepared_by_rear :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_rear s vs h v vsrc =
   (RearValidators s h = vs \<and> prepared s vs h v vsrc)"

text "A hash is committed when two-thirds of the validators have sent a certain message."

definition committed :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed s vs h v = two_thirds_sent_message s vs (Commit (h, v))"

definition committed_by_rear :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_rear s vs h v =
   (RearValidators s h = vs \<and> committed s vs h v)"

definition committed_by_fwd :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_fwd s vs h v =
   (FwdValidators s h = vs \<and> committed s vs h v)"

section "Electing the New Validators (not skippable)"

fun sourcing_normal :: "situation \<Rightarrow> (hash \<times> validator set) \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing_normal s (h, vs) (h', v', v_src) =
  (\<exists> v_ss.
   prepared_by_rear s vs h v_src v_ss \<and>
   -1 \<le> v_src \<and>
   v_src < v' \<and>
   nth_ancestor s (nat (v' - v_src)) h' = Some h \<and>
   validators_match s h h' )"

definition validators_change :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_change s ancient next =
   (FwdValidators s next = RearValidators s ancient)"

fun sourcing_switching_validators ::
"situation \<Rightarrow> (hash \<times> validator set) \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing_switching_validators s (h, vs) (h', v', v_src) =
  (\<exists> v_ss new.
   prepared_by_rear s vs h v_src v_ss \<and>
   committed_by_rear s vs h v_src \<and>
   committed_by_fwd s new h v_src \<and>
   -1 \<le> v_src \<and>
   v_src < v' \<and>
   nth_ancestor s (nat (v' - v_src)) h' = Some h \<and>
   validators_change s h h')"

definition sourcing :: "situation \<Rightarrow> (hash \<times> validator set) \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing s p0 tri = (sourcing_normal s p0 tri \<or> sourcing_switching_validators s p0 tri)"

(* TODO: I'm wondering if I should keep v and v_src in an existential quantifier here, or
   expose it as an argument. *)

(* The two very similar definitions are not combined
 * just for easily counting the number of switching.
 *)
fun inherit_normal :: "situation \<Rightarrow> (hash \<times> validator set \<times> view) \<Rightarrow>
                       (hash \<times> validator set \<times> view) \<Rightarrow> bool"
where
"inherit_normal s (h_old, vs_old, v_src) (h_new, vs_new, v) =
   (prepared_by_rear s vs_new h_new v v_src \<and>
    sourcing_normal s (h_old, vs_old) (h_new, v, v_src))"

lemma inherit_normal_view_increase :
  "inherit_normal s (h_old, vs_old, v_src) (h_new, vs_new, v) \<Longrightarrow>
   (v_src < v)"
apply(simp)
done

fun inherit_switching_validators ::
  "situation \<Rightarrow> (hash \<times> validator set \<times> view) \<Rightarrow>
                (hash \<times> validator set \<times> view) \<Rightarrow> bool"
where
"inherit_switching_validators s (h_old, vs_old, v_old) (h_new, vs_new, v_new) =
   (prepared_by_rear s vs_new h_new v_new v_old \<and>
    sourcing_switching_validators s (h_old, vs_old) (h_new, v_new, v_old))"

lemma inherit_switching_validators_increase_view :
 "inherit_switching_validators s (h_old, vs_old, v_old) (h_new, vs_new, v_new) \<Longrightarrow>
  v_old < v_new"
apply(simp)
done


inductive heir :: "situation \<Rightarrow>
                   (hash \<times> validator set \<times> view) \<Rightarrow> 
                   (hash \<times> validator set \<times> view) \<Rightarrow> bool"
where
  heir_self : "heir s (h, vs, v) (h, vs, v)"
| heir_normal_step : "heir s (h, vs, v) (h', vs', v') \<Longrightarrow>
                 inherit_normal s (h', vs', v') (h'', vs'', v'') \<Longrightarrow>
                 heir s (h, vs, v) (h'', vs'', v'')"
| heir_switching_step : "heir s (h, vs, v) (h', vs', v') \<Longrightarrow>
                 inherit_switching_validators s (h', vs', v') (h'', vs'', v'') \<Longrightarrow>
                 heir s (h, vs, v) (h'', vs'', v'')"

lemma heir_increases_view :
  "heir s t t' \<Longrightarrow> snd (snd t) \<le> snd (snd t')"
apply(induction rule: heir.induct; auto)
done

inductive heir_after_n_switching ::
   "nat \<Rightarrow> situation \<Rightarrow>
    (hash \<times> validator set \<times> view) \<Rightarrow>
    (hash \<times> validator set \<times> view) \<Rightarrow> bool"
where
  heir_n_self : "heir_after_n_switching 0 s (h, vs, v) (h, vs, v)"
| heir_n_normal_step :
   "heir_after_n_switching n s (h, vs, v) (h', vs', v') \<Longrightarrow>
    inherit_normal s (h', vs', v') (h'', vs'', v'') \<Longrightarrow>
    heir_after_n_switching n s (h, vs, v) (h'', vs'', v'')"
| heir_n_switching_step :
   "heir_after_n_switching n s (h, vs, v) (h', vs', v') \<Longrightarrow>
    inherit_switching_validators s (h', vs', v') (h'', vs'', v'') \<Longrightarrow>
    heir_after_n_switching (Suc n) s (h, vs, v) (h'', vs'', v'')"

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
                    (hash \<times> validator set \<times> view) \<Rightarrow>
                    (hash \<times> validator set \<times> view) \<Rightarrow>
                    (hash \<times> validator set \<times> view) \<Rightarrow> bool"
where
"fork s (root, vs, v) (h1, vs1, v1) (h2, vs2, v2) =
  (not_on_same_chain s h1 h2 \<and> heir s (root, vs, v) (h1, vs1, v1) \<and> heir s (root, vs, v) (h2, vs2, v2))"

fun fork_with_n_switching :: "nat \<Rightarrow> situation \<Rightarrow>
             (hash \<times> validator set \<times> view) \<Rightarrow>
             (hash \<times> validator set \<times> view) \<Rightarrow>
             (hash \<times> validator set \<times> view) \<Rightarrow> bool"
where
"fork_with_n_switching
    n s (root, vs, v) (h1, vs1, v1) (h2, vs2, v2) =
   (\<exists> n1 n2.
    n = n1 + n2 \<and>
    not_on_same_chain s h1 h2 \<and>
    heir_after_n_switching n1 s (root, vs, v) (h1, vs1, v1) \<and>
    heir_after_n_switching n2 s (root, vs, v) (h2, vs2, v2))"

lemma fork_has_n_switching :
  "fork s (r, vs, v) (h1, vs1, v1) (h2, vs2, v2) \<Longrightarrow>
   \<exists> n. fork_with_n_switching n s (r, vs, v) (h1, vs1, v1) (h2, vs2, v2)"
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
       (\<not> (\<exists> h_anc vs_anc.
               sourcing s (h_anc, vs_anc) (h, v, v_src)))))"

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


lemma sum_is_suc_dest :
   "Suc n = n1 + n2 \<Longrightarrow>
    ((\<exists> n1'. n1 = Suc n1' \<and> n = n1' + n2) \<or>
     (\<exists> n2'. n2 = Suc n2' \<and> n = n1 + n2'))
   "
apply (case_tac n1; auto)
done

lemma heir_after_suc_switching_dest:
 "heir_after_n_switching sn s (h, vs, v) (h1, vs1, v1) \<Longrightarrow>
  sn = Suc n \<Longrightarrow>
  \<exists> h' vs' v' h'' vs'' v''.
  heir_after_n_switching n s (h, vs, v) (h', vs', v') \<and>
  inherit_switching_validators s (h', vs', v') (h'', vs'', v'') \<and>
  heir_after_n_switching 0 s (h'', vs'', v'') (h1, vs1, v1) "
apply(induction rule: heir_after_n_switching.induct; auto)
 apply(rule_tac x = "h'a" in exI)
 apply(rule_tac x = "vs'a" in exI)
 apply(rule_tac x = "v'a" in exI)
 apply auto
 apply(rule_tac x = "h''a" in exI)
 apply(rule_tac x = "vs''a" in exI)
 apply(rule_tac x = "v''a" in exI)
 apply auto
 apply(rule_tac h' = h' and vs' = vs' in heir_n_normal_step)
  apply blast
 apply simp
 apply(rule_tac x = v_ss in exI)
 apply blast
apply(rule_tac x = h' in exI)
apply(rule_tac x = vs' in exI)
apply(rule_tac x = v' in exI)
apply auto
apply(rule_tac x = h'' in exI)
apply(rule_tac x = vs'' in exI)
apply auto
using heir_n_self by blast

lemma accountable_safety_with_size :
"\<forall> n s h vs v h1 vs1 v1 h2 vs2 v2.
 n \<le> switch_number \<longrightarrow>
 prepare_commit_only_from_rear_or_fwd s \<longrightarrow>
 fork_with_n_switching n s (h, vs, v) (h1, vs1, v1) (h2, vs2, v2) \<longrightarrow>
 committed_by_rear s vs h v \<longrightarrow>
 committed_by_rear s vs1 h1 v1 \<longrightarrow>
 committed_by_rear s vs2 h2 v2 \<longrightarrow>
 (\<exists> vs' h' v'.
   heir s (h, vs, v) (h', vs', v') \<and>
   one_third_slashed s vs')"
sorry

lemma accountable_safety :
"prepare_commit_only_from_rear_or_fwd s \<Longrightarrow>
 fork s (h, vs, v) (h1, vs1, v1) (h2, vs2, v2) \<Longrightarrow>
 committed_by_rear s vs h v \<Longrightarrow>
 committed_by_rear s vs1 h1 v1 \<Longrightarrow>
 committed_by_rear s vs2 h2 v2 \<Longrightarrow>
 \<exists> vs' h' v'.
   heir s (h, vs, v) (h', vs', v') \<and>
   one_third_slashed s vs'"
by (meson accountable_safety_with_size fork_has_n_switching order_refl)


end
