theory MinimumAlgo

imports Main

begin

datatype hash = Hash int
type_synonym view = int

datatype message =
  Commit "hash * view"
| Prepare "hash * view * view"

definition view_of_message :: "message \<Rightarrow> view"
where
"view_of_message m = (case m of
   Commit (h, v) \<Rightarrow> v
 | Prepare (h, v, v_src) \<Rightarrow> v)"

datatype node = Node int

type_synonym sent = "node * message"

record situation =
  Nodes :: "node set"
  Messages :: "sent set"
  PrevHash :: "hash \<Rightarrow> hash option"
(* The slashing condition should be a function of the situation *)

definition situation_has_nodes :: "situation \<Rightarrow> bool"
where
"situation_has_nodes s = (Nodes s \<noteq> {} \<and> finite (Nodes s))"

fun nth_ancestor :: "situation \<Rightarrow> nat \<Rightarrow> hash \<Rightarrow> hash option"
where
  "nth_ancestor _ 0 h = Some h"
| "nth_ancestor s (Suc n) h =
   (case PrevHash s h of
      None \<Rightarrow> None
    | Some h' \<Rightarrow> nth_ancestor s n h')"

definition is_descendant :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"is_descendant s x y = (\<exists> n. nth_ancestor s n x = Some y)"

definition not_on_same_chain :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"not_on_same_chain s x y = ((\<not> is_descendant s x y) \<and> (\<not> is_descendant s y x))"



definition two_thirds :: "situation \<Rightarrow> (node \<Rightarrow> bool) \<Rightarrow> bool"
where
"two_thirds s f =
   (2 * card (Nodes s) \<le> 3 * card ({n. n \<in> Nodes s \<and> f n}))"

definition more_than_two_thirds :: "situation \<Rightarrow> (node \<Rightarrow> bool) \<Rightarrow> bool"
where
"more_than_two_thirds s f =
   (2 * card (Nodes s) < 3 * card ({n. n \<in> Nodes s \<and> f n}))"

definition more_than_one_third :: "situation \<Rightarrow> (node \<Rightarrow> bool) \<Rightarrow> bool"
where
"more_than_one_third s f =
   (card (Nodes s) < 3 * card ({n. n \<in> Nodes s \<and> f n}))"

definition one_third :: "situation \<Rightarrow> (node \<Rightarrow> bool) \<Rightarrow> bool"
where
"one_third s f =
   (card (Nodes s) \<le> 3 * card ({n. n \<in> Nodes s \<and> f n}))"

lemma mp_one_third :
  "finite (Nodes s) \<Longrightarrow>
   \<forall> n. n \<in> Nodes s \<longrightarrow> f n \<longrightarrow> g n \<Longrightarrow>
   one_third s f \<Longrightarrow> one_third s g"
proof (simp add: one_third_def)
  assume "\<forall> n. n \<in> Nodes s \<longrightarrow> f n \<longrightarrow> g n"
  moreover assume "finite (Nodes s)"
  ultimately have "card {n \<in> Nodes s. f n} \<le> card {n \<in> Nodes s. g n}"
    proof -
      assume "\<forall> n. n \<in> Nodes s \<longrightarrow> f n \<longrightarrow> g n"
      then have "{n \<in> Nodes s. f n} \<subseteq> {n \<in> Nodes s. g n}"
        by blast
      moreover assume "finite (Nodes s)"
      ultimately show ?thesis
        by (simp add: card_mono)
    qed
  moreover assume "card (Nodes s) \<le> 3 * card {n \<in> Nodes s. f n}"
  ultimately show "card (Nodes s) \<le> 3 * card {n \<in> Nodes s. g n}"
    by auto
qed

definition two_thirds_sent_message :: "situation \<Rightarrow> message \<Rightarrow> bool"
where
"two_thirds_sent_message s m =
   two_thirds s (\<lambda> n. (n, m) \<in> Messages s)"

definition prepared :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared s h v vs = (two_thirds_sent_message s (Prepare (h, v, vs)))"

definition slashed_one :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashed_one s n =
 (n \<in> Nodes s \<and>
    (\<exists> h v.
      ((n, Commit (h, v)) \<in> Messages s \<and>
    (\<not> (\<exists> vs. -1 \<le> vs \<and> vs < v \<and> prepared s h v vs) ))))"

definition slashed_two :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashed_two s n =
  (n \<in> Nodes s \<and>
     (\<exists> h v vs.
       ((n, Prepare (h, v, vs)) \<in> Messages s \<and>
       vs \<noteq> -1 \<and>
       (\<not> (\<exists> h_anc vs'.
           -1 \<le> vs' \<and> vs' < vs \<and>
           Some h_anc = nth_ancestor s (nat (v - vs)) h \<and>
           prepared s h_anc vs vs')))))"

definition slashed_three :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashed_three s n =
  (n \<in> Nodes s \<and>
    (\<exists> x y v w u.
      (n, Commit (x, v)) \<in> Messages s \<and>
      (n, Prepare (y, w, u)) \<in> Messages s \<and>
      u < v \<and> v < w))"

definition slashed_four :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashed_four s n =
  (n \<in> Nodes s \<and>
    (\<exists> x1 x2 v vs1 vs2.
      (n, Prepare (x1, v, vs1)) \<in> Messages s \<and>
      (n, Prepare (x2, v, vs2)) \<in> Messages s \<and>
      (x1 \<noteq> x2 \<or> vs1 \<noteq> vs2)))"

definition slashed :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashed s n = (slashed_one s n \<or>
                slashed_two s n \<or>
                slashed_three s n \<or>
                slashed_four s n)"

definition committed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"committed s h = (\<exists> v. two_thirds_sent_message s (Commit (h, v)))"

definition one_third_slashed :: "situation \<Rightarrow> bool"
where
"one_third_slashed s = one_third s (slashed s)"

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
  "situation_has_nodes s \<Longrightarrow>
   (\<not> one_third s f) = (more_than_two_thirds s (\<lambda> n. \<not> f n))"
apply(auto simp add: one_third_def more_than_two_thirds_def situation_has_nodes_def)
done

lemma condition_one_positive :
   "\<exists> n. (n, Commit (x, v)) \<in> Messages s \<and>
    n \<in> Nodes s \<and>
    \<not> slashed s n \<Longrightarrow>
    (\<exists>v vs.
     two_thirds s (\<lambda>n. (n, Prepare (x, v, vs)) \<in> Messages s)
     \<and> - 1 \<le> vs \<and> vs < v)"
using slashed_def slashed_one_def two_thirds_sent_message_def prepared_def
by blast

lemma condition_one_positive' :
   "\<exists> n. (n, Commit (x, v)) \<in> Messages s \<and>
    n \<in> Nodes s \<and>
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
  "situation_has_nodes s \<Longrightarrow>
   two_thirds s f \<Longrightarrow>
   more_than_two_thirds s g \<Longrightarrow>
   more_than_one_third s (\<lambda> n. f n \<and> g n)
  "
apply(simp add: two_thirds_def situation_has_nodes_def more_than_two_thirds_def more_than_one_third_def)
apply(rule two_more_two_set; simp)
done

lemma card_nonzero_exists :
"card {n \<in> s. f n} > 0 \<Longrightarrow>
 \<exists> n \<in> s. f n"
(* sledgehammer *)
	by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite not_gr_zero)

lemma more_than_one_third_exists :
  "situation_has_nodes s \<Longrightarrow>
   more_than_one_third s f \<Longrightarrow>
   \<exists> n \<in> Nodes s. f n
  "
apply(rule card_nonzero_exists)
apply(simp add: situation_has_nodes_def more_than_one_third_def)
done


lemma two_more_two_ex :
  "situation_has_nodes s \<Longrightarrow>
   two_thirds s f \<Longrightarrow>
   more_than_two_thirds s g \<Longrightarrow>
   \<exists> n \<in> Nodes s. f n \<and> g n
  "
apply(rule more_than_one_third_exists)
 apply simp
apply(rule two_more_two; simp)
done


lemma committed_implies_prepare :
  "situation_has_nodes s \<Longrightarrow>
   committed s x \<Longrightarrow> (\<exists> v vs. prepared s x v vs \<and> -1 \<le> vs \<and> vs < v) \<or> one_third_slashed s"
apply(auto simp add: committed_def prepared_def two_thirds_sent_message_def one_third_slashed_def)
apply(rule condition_one_positive)
using two_more_two_ex by blast

lemma commit_expand:
  "situation_has_nodes s \<Longrightarrow> 
   two_thirds_sent_message s (Commit (x, v)) \<Longrightarrow>
   (\<exists> vs. prepared s x v vs \<and> -1 \<le> vs \<and> vs < v) \<or> one_third_slashed s"
apply(auto simp add: committed_def prepared_def two_thirds_sent_message_def one_third_slashed_def)
apply(rule condition_one_positive')
using two_more_two_ex by blast


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
  "situation_has_nodes s \<Longrightarrow>
   two_thirds s f \<Longrightarrow>
   two_thirds s g \<Longrightarrow>
   one_third s (\<lambda> n. f n \<and> g n)"
apply(auto simp add: two_thirds_def one_third_def situation_has_nodes_def two_two_set)
done

lemma dependency_self [simp]:
  "\<not> not_on_same_chain s y y"
apply(simp add: not_on_same_chain_def)
apply(simp add: is_descendant_def)
apply(rule_tac x = 0 in exI)
apply(simp)
done

lemma prepare_direct_conflict' :
 "not_on_same_chain s x y \<Longrightarrow>
  finite (Nodes s) \<Longrightarrow>
  n \<in> Nodes s \<Longrightarrow>
  (n, Prepare (x, v2, vs1)) \<in> Messages s \<Longrightarrow>
  (n, Prepare (y, v2, vs2)) \<in> Messages s \<Longrightarrow> slashed_four s n"
apply(auto simp add: slashed_four_def)
apply(rule_tac x = x in exI)
apply(rule_tac x = y in exI)
apply(rule_tac x = v2 in exI)
apply(rule_tac x = vs1 in exI)
apply(simp)
apply(rule_tac x = vs2 in exI)
apply(auto)
done


lemma prepare_direct_conflict :
 "not_on_same_chain s x y \<Longrightarrow>
  finite (Nodes s) \<Longrightarrow>
  n \<in> Nodes s \<Longrightarrow>
  (n, Prepare (x, v2, vs1)) \<in> Messages s \<Longrightarrow>
  (n, Prepare (y, v2, vs2)) \<in> Messages s \<Longrightarrow> slashed s n"
apply(auto simp add: slashed_def prepare_direct_conflict')
done

lemma safety_case1' :
   "situation_has_nodes s \<Longrightarrow>
    not_on_same_chain s x y \<Longrightarrow>
    two_thirds s (\<lambda>n. (n, Prepare (x, v2, vs1)) \<in> Messages s) \<Longrightarrow>
    two_thirds s (\<lambda>n. (n, Prepare (y, v2, vs2)) \<in> Messages s) \<Longrightarrow> one_third s (slashed s)"
proof -
  assume "situation_has_nodes s"
  moreover assume "two_thirds s (\<lambda>n. (n, Prepare (x, v2, vs1)) \<in> Messages s)"
  moreover assume "two_thirds s (\<lambda>n. (n, Prepare (y, v2, vs2)) \<in> Messages s)"
  ultimately have
    "one_third s (\<lambda>n. (n, Prepare (x, v2, vs1)) \<in> Messages s
                   \<and> (n, Prepare (y, v2, vs2)) \<in> Messages s)"
    using two_two by blast
  moreover assume "not_on_same_chain s x y"
  moreover assume "situation_has_nodes s"
  ultimately show "one_third s (slashed s)"
    by (rule_tac mp_one_third; auto simp add: situation_has_nodes_def prepare_direct_conflict)
qed

lemma safety_case1 :
  "situation_has_nodes s \<Longrightarrow>
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
 "situation_has_nodes s \<Longrightarrow>
  two_thirds s (\<lambda>n. (n, Commit (y, v)) \<in> Messages s) \<Longrightarrow>
  (\<exists>vs. prepared s y v vs \<and> -1 \<le> vs \<and> vs < v) \<or> one_third_slashed s"
apply(auto simp add: committed_def prepared_def two_thirds_sent_message_def one_third_slashed_def)
apply(rule condition_one_positive')
using two_more_two_ex by blast

lemma commit_prepared :
 "situation_has_nodes s \<Longrightarrow>
  not_on_same_chain s x y \<Longrightarrow>
  two_thirds_sent_message s (Commit (y, v2)) \<Longrightarrow>
  prepared s x v2 vs1 \<Longrightarrow>
  - 1 \<le> vs1 \<Longrightarrow> vs1 < v2 \<Longrightarrow> one_third_slashed s"
proof(simp add: two_thirds_sent_message_def)
 assume "situation_has_nodes s"
 moreover assume "two_thirds s (\<lambda>n. (n, Commit (y, v2)) \<in> Messages s)"
 ultimately have "(\<exists> vs. prepared s y v2 vs \<and> -1 \<le> vs \<and> vs < v2) \<or> one_third_slashed s"
   using commit_prepare by blast
 moreover assume "situation_has_nodes s"
 moreover assume "not_on_same_chain s x y"
 moreover assume "prepared s x v2 vs1"
 ultimately show "one_third_slashed s"
   	using safety_case1 by blast
qed

lemma negone_commit :
  "situation_has_nodes s \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, v2)) \<Longrightarrow>
   v2 \<le> - 1 \<Longrightarrow> one_third_slashed s"
	using commit_expand by fastforce


lemma one_third_prepared_conflict :
 "x \<noteq> y \<Longrightarrow>
  one_third s
     (\<lambda>n. (n, Prepare (y, c_view, vs)) \<in> Messages s \<and> (n, Prepare (x, c_view, vs1)) \<in> Messages s) \<Longrightarrow>
  situation_has_nodes s \<Longrightarrow>
  one_third s (slashed s)"
apply(rule mp_one_third; blast?)
 apply(simp add: situation_has_nodes_def)
using slashed_def slashed_four_def by blast

lemma prepared_conflict :
"prepared s y c_view vs \<Longrightarrow>
 situation_has_nodes s \<Longrightarrow>
 x \<noteq> y \<Longrightarrow>
 prepared s x c_view vs1 \<Longrightarrow>
 one_third_slashed s"
proof(simp add: prepared_def two_thirds_sent_message_def one_third_slashed_def)
 assume "situation_has_nodes s"
 moreover assume "two_thirds s (\<lambda>n. (n, Prepare (y, c_view, vs)) \<in> Messages s)"
 moreover assume "two_thirds s (\<lambda>n. (n, Prepare (x, c_view, vs1)) \<in> Messages s)"
 ultimately have "one_third s (\<lambda>n. (n, Prepare (y, c_view, vs)) \<in> Messages s \<and>
                                   (n, Prepare (x, c_view, vs1)) \<in> Messages s)"
   using two_two by blast
 moreover assume "situation_has_nodes s"
 moreover assume "x \<noteq> y"
 ultimately show "one_third s (slashed s)"
  by (metis (no_types, lifting) mp_one_third situation_has_nodes_def slashed_def slashed_four_def)
qed

lemma commit_prepared_again :
  "situation_has_nodes s \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
   prepared s x c_view vs1 \<Longrightarrow>
   one_third_slashed s"
proof(simp add: two_thirds_sent_message_def)
 assume "situation_has_nodes s"
 moreover assume "two_thirds s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s)"
 ultimately have "(\<exists> vs. prepared s y c_view vs \<and> -1 \<le> vs \<and> vs < c_view) \<or> one_third_slashed s"
   using commit_prepare by blast
 moreover assume "situation_has_nodes s"
 moreover assume "x \<noteq> y"
 moreover assume "prepared s x c_view vs1"
 ultimately show "one_third_slashed s"
   using prepared_conflict by blast
qed

lemma condition_three_again :
  "situation_has_nodes s \<Longrightarrow>
   vs1 < c_view \<Longrightarrow>
   c_view < v \<Longrightarrow>
   one_third s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s \<and> (n, Prepare (x, v, vs1)) \<in> Messages s) \<Longrightarrow>
   one_third_slashed s"
apply(simp add: one_third_slashed_def)
apply(rule mp_one_third; blast?)
 apply(simp add: situation_has_nodes_def)
using slashed_def slashed_three_def by blast

lemma between_concrete :
  "c_view < v \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
   prepared s x v vs1 \<Longrightarrow>
   vs1 < c_view \<Longrightarrow>
   situation_has_nodes s \<Longrightarrow>
   one_third_slashed s"
proof(simp add: prepared_def two_thirds_sent_message_def)
  assume "situation_has_nodes s"
  moreover assume "two_thirds s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s)"
  moreover assume "two_thirds s (\<lambda>n. (n, Prepare (x, v, vs1)) \<in> Messages s)"
  ultimately have "one_third s (\<lambda>n. (n, Commit (y, c_view)) \<in> Messages s \<and>
                                 (n, Prepare (x, v, vs1)) \<in> Messages s)"
    using two_two by blast
  moreover assume "situation_has_nodes s"
  moreover assume "c_view < v"
  moreover assume "vs1 < c_view"
  ultimately show "one_third_slashed s"
    using condition_three_again by blast
qed

lemma between_case :
  "c_view \<le> v \<Longrightarrow>
   situation_has_nodes s \<Longrightarrow>
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
  moreover assume "situation_has_nodes s"
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
       situation_has_nodes s \<Longrightarrow>
       nth_ancestor s (nat (v - c_view)) x \<noteq> Some y \<Longrightarrow>
       two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
       prepared s x v vs1 \<Longrightarrow>
       vs1 < v \<Longrightarrow>
       \<not> vs1 < c_view \<Longrightarrow>
       \<not> c_view \<le> - 1 \<Longrightarrow>
       \<forall>x y v.
          nat (v - c_view) \<le> n \<longrightarrow>
          c_view \<le> v \<longrightarrow>
          situation_has_nodes s \<longrightarrow>
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
  "(\<exists> somebody. \<not> slashed s somebody \<and> somebody \<in> Nodes s \<and> (somebody, Prepare (x, v, vs1)) \<in> Messages s) \<or> one_third_slashed s")
 apply clarify
 apply(subgoal_tac "\<not> slashed_two s somebody")
  defer
  apply(simp add: slashed_def)
 apply (metis (mono_tags, lifting) not_one_third one_third_slashed_def prepared_def two_more_two_ex two_thirds_sent_message_def)
apply(simp add: slashed_two_def)
apply(drule_tac x = x in spec)
apply(drule_tac x = x in spec)
apply(drule_tac x = v in spec)
apply(drule_tac x = vs1 in spec)
apply auto
done

lemma safety_sub_ind' :
  "\<forall> c_view s x y v vs1.
   n \<ge> nat (v - c_view) \<longrightarrow>
   v \<ge> c_view \<longrightarrow>
   situation_has_nodes s \<longrightarrow>
   nth_ancestor s (nat (v - c_view)) x \<noteq> Some y \<longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<longrightarrow>
   prepared s x v vs1 \<longrightarrow>
   - 1 \<le> vs1 \<longrightarrow> vs1 < v \<longrightarrow> one_third_slashed s"
apply(induction n; auto)
 using commit_prepared_again apply blast
apply(case_tac "\<not> (v > c_view)")
 apply clarsimp
 using commit_prepared_again apply blast 
apply(case_tac "vs1 < c_view")
 apply clarsimp
 using between_case apply blast
apply(case_tac "c_view \<le> -1")
 apply(clarsimp)
 using negone_commit apply blast
apply(clarsimp)
apply(drule_tac x = c_view in spec)
apply(drule_tac x = s in spec)
using the_induction by blast

lemma safety_sub_ind'' :
  "n = nat (v - c_view) \<Longrightarrow>
   v \<ge> c_view \<Longrightarrow>
   situation_has_nodes s \<Longrightarrow>
   nth_ancestor s n x \<noteq> Some y \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, c_view)) \<Longrightarrow>
   prepared s x v vs1 \<Longrightarrow>
   - 1 \<le> vs1 \<Longrightarrow> vs1 < v \<Longrightarrow> one_third_slashed s"
using safety_sub_ind' by blast

lemma no_pependency_ancestor [simp] :
 "not_on_same_chain s x y \<Longrightarrow>
  nth_ancestor s m x \<noteq> Some y"
apply(simp add: not_on_same_chain_def is_descendant_def)
done

lemma safety_sub_ind :
  "situation_has_nodes s \<longrightarrow>
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
  "situation_has_nodes s \<longrightarrow>
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
  "situation_has_nodes s \<Longrightarrow>
   not_on_same_chain s x y \<Longrightarrow>
   two_thirds_sent_message s (Commit (x, v1)) \<Longrightarrow>
   two_thirds_sent_message s (Commit (y, v2)) \<Longrightarrow>
   prepared s x v1 vs1 \<Longrightarrow>
   prepared s y v2 vs2 \<Longrightarrow>
   - 1 \<le> vs1 \<Longrightarrow> vs1 < v1 \<Longrightarrow> - 1 \<le> vs2 \<Longrightarrow> vs2 < v2 \<Longrightarrow> one_third_slashed s"
using safety_sub_closer by auto

lemma accountable_safety_sub :
  "situation_has_nodes s \<Longrightarrow>
   \<exists> v1 vs1. two_thirds_sent_message s (Commit (x, v1)) \<and> prepared s x v1 vs1 \<and> -1 \<le> vs1 \<and> vs1 < v1 \<Longrightarrow>
   \<exists> v2 vs2. two_thirds_sent_message s (Commit (y, v2)) \<and> prepared s y v2 vs2 \<and> -1 \<le> vs2 \<and> vs2 < v2 \<Longrightarrow>
   not_on_same_chain s x y \<Longrightarrow>
   one_third_slashed s
  "
apply(auto simp add: safety_sub')
done



lemma accountable_safety :
  "situation_has_nodes s \<Longrightarrow>
   committed s x \<Longrightarrow> committed s y \<Longrightarrow>
   not_on_same_chain s x y \<Longrightarrow> one_third_slashed s"
apply(auto simp add: committed_def)
using accountable_safety_sub commit_expand by blast

(* what happens with half_slashed? *)


definition authors :: "(node * message) set \<Rightarrow> node set"
where
  "authors ms = {n. \<exists> m. (n, m) \<in> ms}"

definition unslashed_nodes :: "situation \<Rightarrow> node set"
where
  "unslashed_nodes s = {n \<in> Nodes s. \<not> slashed s n}"

definition unslashed_can_extend :: "situation \<Rightarrow> situation \<Rightarrow> bool"
where
"unslashed_can_extend s s_new =
 (\<exists> new_messages.
  authors new_messages \<subseteq> unslashed_nodes s \<and>
  Nodes s_new = Nodes s \<and>
  Messages s_new = Messages s \<union> new_messages \<and>
  PrevHash s_new = PrevHash s_new)"

definition no_commits_by_honest :: "situation \<Rightarrow> bool"
where
"no_commits_by_honest s =
  (\<forall> n \<in> Nodes s. (\<forall> h v.
     (n, Commit (h, v)) \<in> Messages s \<longrightarrow> slashed s n
  ))
"

definition no_messages_by_honest :: "situation \<Rightarrow> bool"
where
"no_messages_by_honest s =
  (\<forall> n \<in> Nodes s. (\<forall> m. (n, m) \<in> Messages s \<longrightarrow> slashed s n))"

definition some_commits_by_honest_at :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"some_commits_by_honest_at s v =
  (\<exists> n \<in> Nodes s.
     (\<not> slashed s n) \<and>
     (\<exists> h v. (n, Commit (h, v)) \<in> Messages s)
  )
"

definition some_messages_by_honest_at :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"some_messages_by_honest_at s v =
  (\<exists> n \<in> Nodes s.
     (\<not> slashed s n) \<and>
     (\<exists> m. (n, m) \<in> Messages s))"

definition no_commits_by_honest_after :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"no_commits_by_honest_after s v_latest =
   (\<forall> n \<in> Nodes s. (\<forall> h v.
     (n, Commit (h, v)) \<in> Messages s \<longrightarrow>
     v \<le> v_latest \<or> slashed s n
     ))
"

definition no_messages_by_honest_after :: "situation \<Rightarrow> view \<Rightarrow> bool"
where
"no_messages_by_honest_after s v_latest =
  (\<forall> n \<in> Nodes s. (\<forall> m.
    (n, m) \<in> Messages s \<longrightarrow>
    view_of_message m \<le> v_latest \<or> slashed s n))"

lemma some_commits_by_honest_intro :
  "\<exists>n\<in>Nodes s. (\<exists>h v. (n, Commit (h, v)) \<in> Messages s) \<and> \<not> slashed s n \<Longrightarrow>
   {M1. some_commits_by_honest_at s M1} \<noteq> {}"
sorry

definition finite_messages :: "situation \<Rightarrow> bool"
where
"finite_messages s = finite (Messages s)"

lemma finite_commits_by_honest :
  "finite_messages s \<Longrightarrow>
   finite {M1. some_commits_by_honest_at s M1}"
sorry

lemma finite_views_have_max :
 "views \<noteq> {} \<Longrightarrow> finite views \<Longrightarrow>
  \<exists> v_max.
    v_max \<in> views \<and> (\<forall> v. v \<le> v_max \<or> v \<notin> views)"
sorry

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
apply(subgoal_tac "
  \<exists> v_max.
    v_max \<in> {M1. some_commits_by_honest_at s M1}
    \<and> (\<forall> v. v \<le> v_max \<or> v \<notin> {M1. some_commits_by_honest_at s M1})")
 apply(clarsimp)
 apply(rule_tac x = v_max in exI)
 apply(rule disjI2)
 apply(rule conjI)
  apply(auto)
 apply(simp add: no_commits_by_honest_after_def some_commits_by_honest_at_def)
by (metis all_not_in_conv finite_views_have_max mem_Collect_eq)


lemma M2_properties:
  "\<exists> M2.
     (M2 = -1 \<and> no_messages_by_honest s)
   \<or> (some_messages_by_honest_at s M2 \<and> no_messages_by_honest_after s M2)
  "
oops

lemma plausible_liveness :
  "situation_has_nodes s \<Longrightarrow>
   (* decendants_exist s \<Longrightarrow> *)
   \<not> one_third_slashed s \<Longrightarrow>
   \<exists> s_new h_new.
     \<not> committed s h_new \<and>
     unslashed_can_extend s s_new \<and>
     committed s_new h_new
  "


end
