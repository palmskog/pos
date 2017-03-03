/*
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
*/
module minimalt

abstract sig Node {}
sig SaneNode extends Node {}
sig SlashedNode extends Node {}

sig View {
  v_prev: lone View
}

sig Hash { // actually (H, v)
  h_prev: lone Hash,
  h_view: one View
}

fact {
  no x : Hash | x in x.(^h_prev)
}

fact {
  no x : View | x in x.(^v_prev)
}


sig Commit {
  c_hash : Hash,
  c_sender: one Node
}

sig Prepare {
  p_hash : Hash,
  p_view_src : View,
  p_sender: one Node
}

fact {
   all p : Prepare | p.p_view_src in (p.p_hash.h_view.(^v_prev))
}

// Slashing condition [i]
pred slashed1 (s : Node) {
   some c : Commit |
      s in c.c_sender &&
      (#{n : Node | some p : Prepare | p.p_sender = n && p.p_hash = c.c_hash}). mul[ 3]  < mul[ #{n : Node}, 2 ]
}

// Slashing condition [ii]
pred slashed2 (s : Node) {
  some p : Prepare |
     (s in p.p_sender && some p.p_view_src.v_prev) &&
     not (
     some h_anc : Hash | some v_src : View |
      h_anc in p.p_hash.(^h_prev) && h_anc.h_view = p.p_view_src &&
      (#{n : Node | some p' : Prepare | p'.p_sender = n && p'.p_hash = h_anc && p'.p_view_src = v_src }). mul[ 3]  >= (#{n : Node}).mul[ 2 ])
}

// Slashing condition [iii]
pred slashed3 (s : Node) {
  some c : Commit | s in c.c_sender && not (all p : Prepare | c.c_sender = p.p_sender &&
    p.p_view_src in c.c_hash.h_view.(^v_prev) && c.c_hash.h_view in p.p_hash.h_view.(^v_prev)
    implies 0 = 1)
}

// Slashing condition [iv]
pred slashed4 (s : Node) {
  some p0: Prepare | some p1:Prepare | s in p0.p_sender && p0.p_sender = p1.p_sender && p0.p_hash.h_view = p1.p_hash.h_view && not
    (p0.p_view_src = p1.p_view_src && p0.p_hash = p1.p_hash)
}

pred some_commit {
   some c : Commit |
     c.c_sender in SaneNode
}

pred some_prepare_new {
   some p : Prepare | some c : Commit |
      some p.p_view_src.v_prev && p.p_sender in SaneNode && c.c_sender = p.p_sender
}

fact {

  all h : Hash |
    h.h_prev.h_view = h.h_view.v_prev

}

fact {
  all v0, v1 : View | v0 in v1.(*v_prev) or v1 in v0.(*v_prev)
}

fact {
   {n : Node | n.slashed1 or n.slashed2 or n.slashed3 or n.slashed4} = { n : Node | not n in SaneNode }
}


pred incompatible_commits {

   some Node &&
   some h0, h1 : Hash | (not h0 in h1.(*h_prev)) &&
    (not h1 in h0.(*h_prev)) &&
    (#{n0 : Node | some c0 : Commit | c0.c_sender = n0 && c0.c_hash = h0}).mul[3] >= (#Node).mul[2] &&
    (#{n1 : Node | some c1 : Commit | c1.c_sender = n1 && c1.c_hash = h1}).mul[3] >= (#Node).mul[2] &&
    (#SlashedNode).mul[3] < (#Node)
}

// how to do the degree of ancestors

// run ownPrev for 10

run incompatible_commits for 4
