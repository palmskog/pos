module minimalt

abstract sig Node {}
sig SaneNode extends Node {}
sig SlashedNode extends Node {}

sig View {
  v_prev: lone View
}

sig Hash {
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

fact {
   all c : Commit |
      c.c_sender in SaneNode implies
      (#{n : Node | some p : Prepare | p.p_hash = c.c_hash}). mul[ 3]  >= mul[ #Node, 2 ]
}

pred some_commit {
   some c : Commit |
     c.c_sender in SaneNode
}

fact prev_does_not_match {

  all h : Hash |
    h.h_prev.h_view = h.h_view.v_prev

}

// how to do the degree of ancestors

// run ownPrev for 10

run some_commit for 2
