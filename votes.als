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
module votes

enum Bool { True, False }

abstract sig Node {}
sig SaneNode extends Node {}
sig SlashedNode extends Node {}

sig View {
  v_prev: lone View
}

abstract sig Hash { // actually (H, v)
  h_prev: lone Hash,
  h_view: one View
}

abstract sig JustifiedHash extends Hash{}
one sig Genesis extends JustifiedHash{}
sig JustifiedNonGenesis extends JustifiedHash{ justification : one JustifiedHash }
sig NonJustifiedHash extends Hash{}

fact {
  no x : Hash | x in x.(^h_prev)
}

fact {
  no x : View | x in x.(^v_prev)
}

// TODO: rename View into Epoch

sig Vote {
  epoch : View,
  checkpoint : Hash,
  source : View,
  sender : one Node // TODO: 'one' here might not be necessary
}

fact {
   all vote : Vote | vote.source in (vote.checkpoint.h_view.(^v_prev))
}

pred some_votes {
   some vote : Vote |
     vote.sender in SaneNode
}

pred two_votes {
  some vote0, vote1 : Vote |
    vote0.sender = vote1.sender && vote0.sender in SaneNode
}

pred justification_link [h_src, h : Hash] {
   h_src in h.(^h_prev) &&
   (#{n : Node | some vote : Vote | vote.sender = n && vote.checkpoint = h && vote.source = h_src.h_view}).mul[3] >= (#Node).mul[2]
}

pred finalized(h : JustifiedNonGenesis)
{
   some child : JustifiedNonGenesis | child.h_prev = h && justification_link[h, child]
}

fact {
   all j : JustifiedNonGenesis | justification_link[j.justification, j]
}

fact {
  all j : JustifiedNonGenesis | Genesis in j.(^justification)
}

fact {
  all h : Hash |
    h.h_prev.h_view = h.h_view.v_prev
}

fact {
  all v0, v1 : View | v0 in v1.(*v_prev) or v1 in v0.(*v_prev)
}

fact {
  all vote : Vote | vote.checkpoint.h_view = vote.epoch
}

pred DBL_VOTE (s : Node) {
  some vote0, vote1 : Vote |
    vote0 != vote1 && vote0.sender = s && vote1.sender = s && vote0.epoch = vote1. epoch
}

pred SURROUND (s : Node) {
  some vote1, vote2 : Vote |
    vote1.epoch in vote2.epoch.(^v_prev) && vote2.source in vote1.source.(^v_prev)
}

fact {
   { n : Node | n.DBL_VOTE or n.SURROUND } = { n : Node | not n in SaneNode }
}



pred incompatible_commits {

   some Node &&
   some h0, h1 : JustifiedNonGenesis | h0.finalized && h1.finalized && (not h0 in h1.(*h_prev)) &&
    (not h1 in h0.(*h_prev)) &&
    (#{n0 : Node | some c0 : Vote | c0.sender = n0 && c0.checkpoint = h0}).mul[3] >= (#Node).mul[2] &&
    (#{n1 : Node | some c1 : Vote | c1.sender = n1 && c1.checkpoint = h1}).mul[3] >= (#Node).mul[2] &&
    (#SlashedNode).mul[3] < (#Node)
}


// how to do the degree of ancestors

// run ownPrev for 10

run incompatible_commits for 10
