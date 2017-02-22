theory MinimumAlgo

imports Main

begin

datatype hash = Hash int
type_synonym view = int

datatype message =
  Commit "hash * view"
| Prepare "hash * view * view"

datatype node = Node int

type_synonym sent = "node * message"

record situation =
  Nodes :: "node set"
  Messages :: "sent set"
  PrevHash :: "hash \<Rightarrow> hash option"
(* The slashing condition should be a function of the situation *)

fun nth_ancestor :: "situation \<Rightarrow> nat \<Rightarrow> hash \<Rightarrow> hash option"
where
  "nth_ancestor _ 0 h = Some h"
| "nth_ancestor s (Suc n) h =
   (case PrevHash s h of
      None \<Rightarrow> None
    | Some h' \<Rightarrow> nth_ancestor s n h')"

definition who_have_sent :: "situation \<Rightarrow> message \<Rightarrow> node set"
where
"who_have_sent s m =
 {n. n \<in> Nodes s \<and> (n, m) \<in> Messages s}"

definition two_thirds_sent_message :: "situation \<Rightarrow> message \<Rightarrow> bool"
where
"two_thirds_sent_message s m =
 (2 * card (Nodes s) \<le> 3 * card (who_have_sent s m))"

definition slashing_one :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashing_one s n =
 (n \<in> Nodes s \<and>
    (\<exists> h v.
      ((n, Commit (h, v)) \<in> Messages s \<and>
    (\<not> (\<exists> vs. -1 \<le> vs \<and> vs < v \<and> two_thirds_sent_message s (Prepare (h, v, vs) ))))))"

definition slashing_two :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashing_two s n =
  (n \<in> Nodes s \<and>
     (\<exists> h v vs.
       ((n, Prepare (h, v, vs)) \<in> Messages s \<and>
       vs \<noteq> -1 \<and>
       (\<not> (\<exists> h_anc vs'.
           -1 \<le> vs' \<and> vs' < vs \<and>
           Some h_anc = nth_ancestor s (nat (vs - vs')) h \<and>
           two_thirds_sent_message s (Prepare (h_anc, vs, vs')))))))"

definition slashing_three :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashing_three s n =
  (n \<in> Nodes s \<and>
    (\<exists> x y v w u.
      (n, Commit (x, v)) \<in> Messages s \<and>
      (n, Prepare (y, w, u)) \<in> Messages s \<and>
      u < v \<and> v < w))"

definition slashing_four :: "situation \<Rightarrow> node \<Rightarrow> bool"
where
"slashing_four s n =
  (n \<in> Nodes s \<and>
    (\<exists> x1 x2 v vs1 vs2.
      (n, Prepare (x1, v, vs1)) \<in> Messages s \<and>
      (n, Prepare (x2, v, vs2)) \<in> Messages s \<and>
      (x1 \<noteq> x2 \<or> vs1 \<noteq> vs2)))"

end
