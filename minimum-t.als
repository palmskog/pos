module minimalt

abstract sig Node {}
sig SaneNode extends Node {}
sig SlashedNode extends Node {}

sig View {
  v_prev: lone View
}

sig Hash {
  h_prev: lone Hash
}

fact {
  no x : Hash | x in x.(^h_prev)
}

fact {
  no x : View | x in x.(^v_prev)
}


sig Commit {
  c_hash : Hash,
  c_view : View,
  c_sender: one Node
}

sig Prepare {
  p_hash : Hash,
  p_view: View,
  p_view_src : View,
  p_sender: one Node
}

fact {
   all p : Prepare | p.p_view_src in (p.p_view.(^v_prev))
}

fact {
   all c : Commit |
  
      (#{n : Node | some p : Prepare | p.p_hash = c.c_hash && p.p_view = c.c_view}). mul[ 3]  >= mul[ #Node, 2 ]
}

pred some_commit {
   some Commit
}

// run ownPrev for 10

run some_commit for 2
