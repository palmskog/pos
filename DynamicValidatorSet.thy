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

section "Definitions Necessary to Understand Accountable Safety (not skippable)"

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

text "A hash's previous hash's previous hash is a second-ancestor.  Later, we will see that an honest
validator will send a prepare message only after seeing enough prepare messages for an ancestor of a
particular degree."

fun nth_ancestor :: "situation \<Rightarrow> nat \<Rightarrow> hash \<Rightarrow> hash option"
where
  "nth_ancestor _ 0 h = Some h"
| "nth_ancestor s (Suc n) h =
   (case PrevHash s h of
      None \<Rightarrow> None
    | Some h' \<Rightarrow> nth_ancestor s n h')"

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

text "It matters when two-thirds of validators are saying something."

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

definition committed :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed s vs h v = two_thirds_sent_message s vs (Commit (h, v))"

subsection "Prepare Messages' Sources"

text "As we will see, honest validators should send a prepare message only when
it has enough prepare messages at a particular view.  Those prepare messages need
to be signed by two-thirds of both the rear and the forward validators."

text "A hash at a view and a view source is prepared by the rear validators when
two-thirds of the rear validators have signed the prepare message."

definition prepared_by_rear :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_rear s h v vsrc =
   (prepared s (RearValidators s h) h v vsrc)"

text "Similarly for the forward validators."

definition prepared_by_fwd :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_fwd s h v vsrc =
   (prepared s (FwdValidators s h) h v vsrc)"

text "When both of these happens, a prepare is signed by both the rear and the forward validator sets."

definition prepared_by_both :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_both s h v vsrc =
  (prepared_by_rear s h v vsrc \<and> prepared_by_fwd s h v vsrc)"

text "Similar definitions for commit messages."

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
   (committed_by_rear s h v \<and> committed_by_fwd s h v)"

text "One type of prepare source is the normal one.  The normal source needs to have the same 
rear validator set and the same forward validator set."

definition validators_match :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_match s h0 h1 =
  (RearValidators s h0 = RearValidators s h1 \<and>
   FwdValidators s h0 = FwdValidators s h1)"

fun sourcing_normal :: "situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing_normal s h (h', v', v_src) =
  (\<exists> v_ss.
   prepared_by_both s h v_src v_ss \<and>
   -1 \<le> v_src \<and>
   v_src < v' \<and>
   nth_ancestor s (nat (v' - v_src)) h' = Some h \<and>
   validators_match s h h' )"

text "Another type of sourcing allows changing the validator sets.
The forward validator set of the source needs to coincide with the
rear validator set of the newly prepared hash.
"

definition validators_change :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_change s ancient next =
   (FwdValidators s ancient = RearValidators s next)"

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

text "A prepare message's source needs to be one of these two types."

definition sourcing :: "situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing s h_new tri = (sourcing_normal s h_new tri \<or> sourcing_switching_validators s h_new tri)"

subsection "Slashing Conditions"

text "In a situation, a validator might be slashed or not.  A validator is slashed individually
although later we will be often talking ``unless one-third of the validators are slashed.''
"

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

definition slashed_two :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_two s n =
  (\<exists> h v v_src.
       ((n, Prepare (h, v, v_src)) \<in> Messages s \<and>
       v_src \<noteq> -1 \<and>
       (\<not> (\<exists> h_anc. sourcing s h_anc (h, v, v_src)))))"

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

definition one_third_slashed :: "situation \<Rightarrow> validator set \<Rightarrow> bool"
where
"one_third_slashed s vs = one_third vs (slashed s)"

text "However, since it does not make sense to divide the cardinality of an infinite set by three,
we should be talking
about situations where the set of validators is finite."

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

subsection "Validator History Tracking"

text "In the statement of accountable safety, we need to be a bit specific about
which validator set the slashed validators belong to.  A singleton is also a validator set
and the 2/3 of a random singleton being slashed should not be significant.
So, when we have a fork, we start from the root of the fork and identify the heirs of the initial
validator sets.  Our statement says 2/3 of a heir validator set are slashed.
"

text "There are two ways of inheriting the title of relevant validator set.
These correspond to the two ways of sourcing a prepare message."

fun inherit_normal :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"inherit_normal s (h_old, v_src) (h_new, v) =
   (prepared_by_both s h_new v v_src \<and>  sourcing_normal s h_old (h_new, v, v_src))"

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

text "The heir relation is just zero-or-more repetition of the inheritance."

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

text "When two hashes are not in the inheritance relation in either direction,
the two hashes are not on the same heir chain.  In the statement of accountable safety,
we use this concept to detect conflicts (which should not happen until 2/3 of a legitimate
heir are slashed)."

definition on_same_heir_chain :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"on_same_heir_chain s x y = (heir s x y \<or> heir s y x)"

text "When heirs are not on the same chain of legitimacy, they have forked."

fun fork :: "situation \<Rightarrow>
                    (hash \<times> view) \<Rightarrow>
                    (hash \<times> view) \<Rightarrow>
                    (hash \<times> view) \<Rightarrow> bool"
where
"fork s (root, v) (h1, v1) (h2, v2) =
  (\<not> on_same_heir_chain s (h1, v1) (h2, v2) \<and> heir s (root, v) (h1, v1) \<and> heir s (root, v) (h2, v2))"

text "A fork is particularly bad when the end points are committed, not only prepared."

fun fork_with_commits :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"fork_with_commits s (h, v) (h1, v1) (h2, v2) =
   (fork s (h, v) (h1, v1) (h2, v2) \<and>
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"


section "Auxiliary Things (skippable)"

subsection "Sets and Arithmetics"

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

lemma nat_min_min :
"    vs1 < v \<Longrightarrow>
    \<not> vs1 < c_view \<Longrightarrow>
   (nat (v - vs1) + nat (vs1 - c_view)) = nat (v - c_view)"
by (simp add: Nat_Transfer.transfer_nat_int_functions(1))

lemma view_total [simp]:
  "(v2 :: view) \<le> v1 \<or> v1 \<le> v2"
apply auto
done


lemma sum_is_suc_dest :
   "Suc n = n1 + n2 \<Longrightarrow>
    ((\<exists> n1'. n1 = Suc n1' \<and> n = n1' + n2) \<or>
     (\<exists> n2'. n2 = Suc n2' \<and> n = n1 + n2'))
   "
apply (case_tac n1; auto)
done

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

lemma one_third_mp :
  "finite X \<Longrightarrow>
   \<forall> v. p v \<longrightarrow> q v \<Longrightarrow>
   one_third X p \<Longrightarrow> one_third X q"
apply(simp add: one_third_def)
 apply(subgoal_tac "card {n \<in> X. p n} \<le> card {n \<in> X. q n}")
 apply linarith
apply(subgoal_tac "finite {n \<in> X. q n}")
 apply(subgoal_tac "{n \<in> X. p n} \<subseteq> {n \<in> X. q n}")
  using card_mono apply blast
 apply blast
by simp

lemma two_thirds_two_thirds_one_third :
  "finite X \<Longrightarrow>
    two_thirds X p \<Longrightarrow>
    two_thirds X q \<Longrightarrow>
    one_third X (\<lambda> x. p x \<and> q x)
  "
apply(simp add: two_thirds_def one_third_def)
apply(rule_tac two_two_set)
  apply simp
 apply simp
apply simp
done

subsection "Validator History Tracking"

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



lemma inherit_switching_validators_increase_view :
 "inherit_switching_validators s (h_old,v_old) (h_new, v_new) \<Longrightarrow>
  v_old < v_new"
apply(simp)
done

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


lemma heir_same_height :
 "heir s (h', v) (h, v) \<Longrightarrow>
  h' = h"
apply(drule heir_decomposition)
using heir_increases_view apply force
done


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


lemma inherit_normal_means_heir :
  "inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
   heir s (h', v') (h'', v'')"
by (meson heir_normal_step heir_self inherit_normal.simps sourcing_normal.simps)


lemma chain_and_inherit :
   "inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
    v_two \<le> snd (h'', v'') \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
    v_two \<le> snd (h', v') \<Longrightarrow>
    on_same_heir_chain s (h', v') (h_two, v_two) \<Longrightarrow> False"
apply(subgoal_tac "heir s (h', v') (h'', v'')")
 apply(simp only: on_same_heir_chain_def)
 apply(erule disjE)
  using heir_increases_view heir_same_height apply fastforce
 using heir_normal_step apply blast
using inherit_normal_means_heir by blast

lemma one_validator_change_leaves_one_set :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n = 0 \<and> FwdValidators s (fst (h, v)) = FwdValidators s (fst (h', v')) \<or>
    n = 1 \<and> FwdValidators s (fst (h, v)) = RearValidators s (fst (h', v'))"
apply(induction rule: heir_after_n_switching.induct)
  apply blast
 apply (simp add: validators_match_def)
apply(subgoal_tac "n = 0")
 defer
 apply linarith
by (simp add: validators_change_def)

lemma prepared_by_fwd_of_origin :
"   n \<le> Suc 0 \<Longrightarrow>
    heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
    prepared s (FwdValidators s h) h'' v'' v'
"
apply(simp only: inherit_normal.simps prepared_by_both_def prepared_by_fwd_def prepared_by_rear_def)
apply(subgoal_tac " (FwdValidators s h) = (FwdValidators s h'') \<or>
                    (FwdValidators s h) = (RearValidators s h'')")
 apply auto[1]
by (metis fst_conv one_validator_change_leaves_one_set sourcing_normal.simps validators_match_def)

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

lemma heir_after_one_or_more_switching_dest :
  "heir_after_n_switching na s (h, v) (h_three, v_three) \<Longrightarrow>
   na > 0 \<Longrightarrow>
   (\<exists> h_one v_one h_two v_two.
    heir_after_n_switching (na - 1) s (h, v) (h_one, v_one) \<and>
    inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
    heir_after_n_switching 0 s (h_two, v_two) (h_three, v_three))"
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
apply(rule allI)
apply(rule allI)
apply(drule_tac x = h' in spec)
apply(drule_tac x = v' in spec)
apply(rule impI)
by (metis forget_number_of_switching fork.simps fork_with_center.simps heir_switching_step heir_trans)

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

subsection "Slashing Related"

lemma slashed_four_means_slashed_on_a_group:
   "finite X \<Longrightarrow> one_third X (slashed_four s) \<Longrightarrow> one_third X (slashed s)"
using one_third_mp slashed_def by blast

lemma slashed_four_on_a_group:
  " finite (FwdValidators s h) \<Longrightarrow>
    prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow>
    \<exists>v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src \<Longrightarrow> h'' \<noteq> h_two \<Longrightarrow>
    one_third (FwdValidators s h) (slashed_four s)"
apply(simp only: prepared_def two_thirds_sent_message_def)
apply(erule exE)
apply(subgoal_tac
       "one_third (FwdValidators s h)
           (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and>
                (n, Prepare (h_two, v'', v_two_src)) \<in> Messages s)
       ")
 apply(subgoal_tac "\<forall> n. 
               ((n, Prepare (h'', v'', v')) \<in> Messages s \<and>
                (n, Prepare (h_two, v'', v_two_src)) \<in> Messages s) \<longrightarrow>
               slashed_four s n")
  apply (simp add: one_third_mp)
 using slashed_four_def apply blast
by (simp add: two_thirds_two_thirds_one_third)

lemma committed_so_prepared :
  " finite (FwdValidators s h) \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v'') \<Longrightarrow>
    committed_by_both s h_two v'' \<Longrightarrow>
    \<not> one_third (FwdValidators s h) (slashed s) \<Longrightarrow> prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow> \<exists>v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src"
apply(subgoal_tac "committed s (FwdValidators s h) h_two v''")
 apply (metis eq_fst_iff forget_number_of_switching heir_decomposition inherit_normal.simps inherit_switching_validators.simps one_validator_change_leaves_one_set prepared_by_both_def prepared_by_fwd_def prepared_by_rear_def)
using committed_by_both_def committed_by_fwd_def committed_by_rear_def one_validator_change_leaves_one_set by fastforce



lemma slashed_three_on_a_group :
 "finite X \<Longrightarrow>
  one_third X (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and> (n, Commit (h_two, v_two)) \<in> Messages s) \<Longrightarrow>
  v' < v_two \<Longrightarrow> v_two < v'' \<Longrightarrow> one_third X (slashed_three s)"
apply(rule one_third_mp; auto simp add: slashed_three_def)
apply blast
done

lemma slashed_three_on_group:
  " finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    one_third (FwdValidators s h) (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and> (n, Commit (h_two, v_two)) \<in> Messages s) \<Longrightarrow>
    v' < v_two \<Longrightarrow>
    v_two < v'' \<Longrightarrow>
    one_third (FwdValidators s h) (slashed_three s)"
proof -
  assume a1: "v' < v_two"
  assume a2: "v_two < v''"
  assume a3: "one_third (FwdValidators s h) (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and> (n, Commit (h_two, v_two)) \<in> Messages s)"
  assume a4: "finite (FwdValidators s (fst (h, v)))"
  have f5: "\<not> 0 \<le> v' + - 1 * v_two"
    using a1 by force
  have f6: "\<not> v'' + - 1 * v_two \<le> 0"
    using a2 by auto
  have f7: "\<forall>V p pa. (infinite V \<or> (\<exists>v. p v \<and> \<not> pa v) \<or> \<not> one_third V p) \<or> one_third V pa"
    by (meson one_third_mp)
  obtain vv :: "(validator \<Rightarrow> bool) \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> validator" where
    "\<forall>x0 x1. (\<exists>v3. x1 v3 \<and> \<not> x0 v3) = (x1 (vv x0 x1) \<and> \<not> x0 (vv x0 x1))"
    by moura
  then have f8: "\<forall>V p pa. (infinite V \<or> p (vv pa p) \<and> \<not> pa (vv pa p) \<or> \<not> one_third V p) \<or> one_third V pa"
    using f7 by presburger
  have f9: "\<forall>x1 x2. ((x2::int) < x1) = (\<not> x1 + - 1 * x2 \<le> 0)"
    by auto
  have "\<forall>x0 x2. ((x0::int) < x2) = (\<not> 0 \<le> x0 + - 1 * x2)"
    by linarith
  then have "\<not> ((vv (slashed_three s) (\<lambda>v. (v, Prepare (h'', v'', v')) \<in> Messages s \<and> (v, Commit (h_two, v_two)) \<in> Messages s), Prepare (h'', v'', v')) \<in> Messages s \<and> (vv (slashed_three s) (\<lambda>v. (v, Prepare (h'', v'', v')) \<in> Messages s \<and> (v, Commit (h_two, v_two)) \<in> Messages s), Commit (h_two, v_two)) \<in> Messages s) \<or> slashed_three s (vv (slashed_three s) (\<lambda>v. (v, Prepare (h'', v'', v')) \<in> Messages s \<and> (v, Commit (h_two, v_two)) \<in> Messages s))"
    using f9 f6 f5 slashed_three_def by blast
  then show ?thesis
  using f8 a4 a3 by fastforce
qed

lemma smaller_induction_same_height_violation :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    finite (FwdValidators s h) \<Longrightarrow>
    prepared_by_both s h'' v'' v' \<and>
    (\<exists>v_ss. prepared_by_both s h' v' v_ss) \<and> - 1 \<le> v' \<and> v' < v'' \<and> nth_ancestor s (nat (v'' - v')) h'' = Some h' \<and> validators_match s h' h'' \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v'') \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v'') \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_two v'' \<Longrightarrow> \<not> one_third (FwdValidators s h) (slashed s) \<Longrightarrow> 
    prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow>  False"
apply(subgoal_tac "\<exists> v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src")
 apply(subgoal_tac "h'' \<noteq> h_two")
  apply(subgoal_tac "one_third (FwdValidators s h) (slashed_four s)")
   using slashed_four_means_slashed_on_a_group apply blast
  using slashed_four_on_a_group apply blast
 using heir_self on_same_heir_chain_def apply blast
using committed_so_prepared by blast

lemma smaller_induction_skipping_violation :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    finite (FwdValidators s h) \<Longrightarrow>
    prepared_by_both s h'' v'' v' \<and> (\<exists>v_ss. prepared_by_both s h' v' v_ss) \<and> - 1 \<le> v' \<and> nth_ancestor s (nat (v'' - v')) h'' = Some h' \<and> validators_match s h' h'' \<Longrightarrow>
    v_two \<le> v'' \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    \<not> one_third (FwdValidators s h) (slashed s) \<Longrightarrow> \<not> v_two \<le> v' \<Longrightarrow> prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow>
    v_two \<noteq> v'' \<Longrightarrow> False"
apply(subgoal_tac "one_third (FwdValidators s h) (slashed_three s)")
 using one_third_mp slashed_def apply blast
apply(subgoal_tac "committed s (FwdValidators s h) h_two v_two")
 apply(simp add: prepared_def committed_def two_thirds_sent_message_def)
 apply(subgoal_tac "one_third (FwdValidators s h)
         (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and>
               (n, Commit (h_two, v_two)) \<in> Messages s)")
  apply(subgoal_tac "v_two > v'")
   apply(subgoal_tac "v_two < v''")
    using slashed_three_on_a_group apply blast
   apply linarith
  apply linarith
 apply(rule two_thirds_two_thirds_one_third; simp)
by (metis committed_by_both_def committed_by_fwd_def committed_by_rear_def fst_conv one_validator_change_leaves_one_set)

lemma smaller_induction_case_normal:
  "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
   (finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h', v') \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h', v') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False) \<Longrightarrow>
   inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
   finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
   v_two \<le> snd (h'', v'') \<Longrightarrow>
   n \<le> Suc 0 \<Longrightarrow>
   n_two \<le> Suc 0 \<Longrightarrow>
   \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
   heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
   committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False"
apply(case_tac "v_two \<le> snd (h', v')")
 apply(case_tac "on_same_heir_chain s (h', v') (h_two, v_two)")
	using chain_and_inherit apply blast
 apply blast
(* The group in question has prepared at v'' *)
apply(subgoal_tac "prepared s (FwdValidators s h) h'' v'' v'")
 defer
 using prepared_by_fwd_of_origin apply blast
apply(case_tac "v_two = v''")
 apply simp
 using smaller_induction_same_height_violation apply blast
apply simp
using smaller_induction_skipping_violation by blast

lemma some_h :
    "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
    heir s (h', v') (h'', v'')"
apply(subgoal_tac "\<exists> x. prepared_by_both s h' v' x")
 using heir_self heir_switching_step apply blast
by simp

lemma smaller_induction_switching_case:
  "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
   (finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h', v') \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h', v') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False) \<Longrightarrow>
    inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
    finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h'', v'') \<Longrightarrow>
    Suc n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False"
apply(case_tac "v_two < v'")
 apply(case_tac "\<not> on_same_heir_chain s (h', v') (h_two, v_two)")
  apply simp
 apply(subgoal_tac "heir s (h', v') (h_two, v_two)")
  using heir_increases_view apply force
 using heir_switching_step on_same_heir_chain_def apply blast
apply(case_tac "v' = v_two")
 apply(subgoal_tac "heir s (h', v') (h'', v'')")
  apply simp
  apply(subgoal_tac "\<exists> v'_src. prepared s (FwdValidators s h) h' v_two v'_src")
   apply(subgoal_tac "\<exists> v_two_src. prepared s (FwdValidators s h) h_two v_two v_two_src")
    apply(subgoal_tac "h' \<noteq> h_two")
     apply (meson slashed_four_means_slashed_on_a_group slashed_four_on_a_group)
    using on_same_heir_chain_def apply blast
   using committed_so_prepared apply blast
  using heir_same_height on_same_heir_chain_def apply blast
 using some_h apply blast
apply(subgoal_tac "v' < v_two")
 apply(subgoal_tac "prepared s (FwdValidators s h) h'' v'' v'")
  apply(subgoal_tac "committed s (FwdValidators s h) h_two v_two")
   apply(case_tac "v_two < v''")
    apply(subgoal_tac "one_third (FwdValidators s h)
         (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and>
              (n, Commit (h_two, v_two)) \<in> Messages s)")
     apply(subgoal_tac "one_third (FwdValidators s h) (slashed_three s)")
      apply (metis fst_conv one_third_mp slashed_def)
     apply(rule slashed_three_on_group)
        apply simp
       apply simp
      apply simp
     apply simp
    apply(simp only: prepared_def committed_def two_thirds_sent_message_def)
    apply(rule two_thirds_two_thirds_one_third; simp)
   apply simp
   apply(subgoal_tac "\<exists> v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src")
    apply(subgoal_tac "h'' \<noteq> h_two")
     apply (simp add: slashed_four_means_slashed_on_a_group slashed_four_on_a_group)
    using heir_self on_same_heir_chain_def apply blast
   using committed_so_prepared apply blast
  apply (metis committed_by_both_def committed_by_fwd_def committed_by_rear_def fst_conv one_validator_change_leaves_one_set)
 apply simp
 apply (metis One_nat_def Suc_neq_Zero fst_conv le_numeral_extra(1) one_validator_change_leaves_one_set prepared_by_both_def prepared_by_rear_def validators_change_def)
apply linarith
done


lemma accountable_safety_smaller_induction:
   "heir_after_n_switching n_one s (h, v) (h_one, v_one) \<Longrightarrow>
    finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h_one, v_one) \<Longrightarrow>
    n_one \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) (* maybe not necessary *) \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False"
apply(induction rule: heir_after_n_switching.induct)
  apply (simp add: forget_number_of_switching on_same_heir_chain_def)
 using smaller_induction_case_normal apply blast
using smaller_induction_switching_case by blast

lemma accountable_safety_from_fork_with_high_root_base_one_longer :
"n_one \<le> 1 \<and>
 n_two \<le> 1 \<and>
 v_one \<ge> v_two \<Longrightarrow>
 finite (FwdValidators s h) \<Longrightarrow>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
apply(simp only: fork_with_center_with_high_root_with_n_switching.simps)
apply(simp only: fork_with_center_with_n_switching.simps)
apply(simp only: fork_with_n_switching.simps)
apply clarify
apply(rule_tac x = h in exI)
apply(rule_tac x = v in exI)
apply(rule conjI)
 apply simp
apply(simp only: one_third_of_rear_or_fwd_slashed_def)
apply(rule disjI2)
apply(case_tac "one_third_of_fwd_slashed s h")
 apply simp
apply(simp add: one_third_of_fwd_slashed_def)
using accountable_safety_smaller_induction by fastforce

lemma accountable_safety_from_fork_with_high_root_base_two_longer :
"n_one \<le> 1 \<and>
 n_two \<le> 1 \<and>
 v_one \<le> v_two \<Longrightarrow>
 finite (FwdValidators s h) \<Longrightarrow>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
apply(rule_tac
      n_one = n_two
      and n_two = n_one
      and v_one = v_two
      and v_two = v_one
      and h_two = h_one
      and h_one = h_two
      and h = h and v = v
      in
      accountable_safety_from_fork_with_high_root_base_one_longer)
  apply blast
 apply simp
using on_same_heir_chain_def by auto

lemma accountable_safety_from_fork_with_high_root_base :
"n_one \<le> 1 \<and>
 n_two \<le> 1 \<and>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 finite (FwdValidators s h) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
(* the forward set of h should have one-third slashed here. *)
(* Take the longer chain and do an induction
   and so, (prepared_view, prepared) and (committed, committed_view) is not in the relation
   make prepared shorter and shorter...!
 *)
apply(subgoal_tac "v_one \<le> v_two \<or> v_two \<le> v_one")
 apply (meson accountable_safety_from_fork_with_high_root_base_one_longer accountable_safety_from_fork_with_high_root_base_two_longer)
by linarith


subsection "Mainline Arguments for Accountable Safety"

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
    finite (FwdValidators s h) \<longrightarrow>
    fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_twoa
     (h_two, v_two) \<longrightarrow>
     (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
    finite (FwdValidators s h) \<Longrightarrow>
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

lemma some_symmetry :
  "\<forall>n_onea n_two h_one v_one h_two v_two.
       n_onea + n_two \<le> n_one + n_two_pre \<longrightarrow>
       finite (FwdValidators s h) \<longrightarrow>
       fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_two
        (h_two, v_two) \<longrightarrow>
       (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
    \<forall>n_onea n_twoa h_one v_one h_two v_two.
       n_onea + n_twoa \<le> n_two_pre + n_one \<longrightarrow>
       finite (FwdValidators s h) \<longrightarrow>
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
          finite (FwdValidators s h) \<longrightarrow>
          fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_two
           (h_two, v_two) \<longrightarrow>
          (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
       finite (FwdValidators s h) \<Longrightarrow>
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
 using fork_with_center_with_high_root_with_n_switching_sym apply blast
 using add.commute apply blast
apply simp
by (simp add: add.commute)

lemma switching_induction :
  "\<forall>n_one n_two h_one v_one h_two v_two.
            n_one + n_two \<le> k \<longrightarrow>
            finite (FwdValidators s h) \<longrightarrow>
            fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two
             (h_two, v_two) \<longrightarrow>
            (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_rear_or_fwd_slashed s h') \<Longrightarrow>
         \<forall>n_one n_two h_one v_one h_two v_two.
            n_one + n_two \<le> Suc k \<longrightarrow>
            finite (FwdValidators s h) \<longrightarrow>
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
 finite (FwdValidators s h) \<longrightarrow>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<longrightarrow>
 (\<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h')"
apply(induction k)
 using accountable_safety_from_fork_with_high_root_base apply blast
using switching_induction by blast

lemma accountable_safety_from_fork_with_high_root_with_n :
"finite (FwdValidators s h) \<Longrightarrow>
 fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
using accountable_safety_from_fork_with_high_root_with_n_ind by blast

lemma accountable_safety_from_fork_with_high_root :
"finite (FwdValidators s h) \<Longrightarrow>
 fork_with_center_with_high_root s (h_orig, v_orig) (h, v) (h_one, v_one) (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
by (meson accountable_safety_from_fork_with_high_root_with_n fork_with_center_with_high_root_has_n_switching)

definition validator_sets_finite :: "situation \<Rightarrow> bool"
  where "validator_sets_finite s = (\<forall> h. finite (FwdValidators s h))"

lemma accountable_safety_center :
"validator_sets_finite s \<Longrightarrow>
 fork_with_center s (h, v) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h, v) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
apply(drule fork_with_center_choose_high_root)
apply(clarify)
	using accountable_safety_from_fork_with_high_root validator_sets_finite_def by blast

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

section "Accountable Safety (don't skip)"

text "The statement of accountable safety is simple.  If a situation has a finite number of
      validators on each hash, a fork means some validator set suffers 1/3 slashing.
      A fork is defined using the @{term heir} relation.  The slashed validator set
      is also a heir of the original validator set.
     "

lemma accountable_safety :
"validator_sets_finite s \<Longrightarrow>
 fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h, v) (h', v') \<and>
   one_third_of_rear_or_fwd_slashed s h'"
using accountable_safety_center fork_with_center_and_root by blast


end
