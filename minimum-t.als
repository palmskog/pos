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
fact {
   all c : Commit |
      c.c_sender in SaneNode implies
      (#{n : Node | some p : Prepare | p.p_hash = c.c_hash}). mul[ 3]  >= mul[ #{n : Node}, 2 ]
}

// Slashing condition [ii]
fact {
  all p : Prepare |
     (p.p_sender in SaneNode && some p.p_view_src.v_prev) implies
     some h_anc : Hash | some v_src : View |
      h_anc in p.p_hash.(^h_prev) &&
      (#{n : Node | some p' : Prepare | p'.p_sender = n && p'.p_hash = h_anc && p'.p_view_src = v_src }). mul[ 3]  >= (#{n : Node}).mul[ 2 ]
}

// Slashing condition [iii]
fact {
  all c : Commit | c.c_sender in SaneNode implies all p : Prepare | c.c_sender = p.p_sender && 
    p.p_view_src in c.c_hash.h_view.(^v_prev) && c.c_hash.h_view in p.p_hash.h_view.(^v_prev)
    implies 0 = 1
}

// Slashing condition [iv]
fact {
  all p0: Prepare | all p1:Prepare | p0.p_sender = p1.p_sender && p1.p_sender in SaneNode && p0.p_hash.h_view = p1.p_hash.h_view implies
    p0.p_view_src = p1.p_view_src && p0.p_hash = p1.p_hash
}

pred some_commit {
   some c : Commit |
     c.c_sender in SaneNode
}

pred some_prepare_new {
   some p : Prepare | some c : Commit |
      some p.p_view_src.v_prev && p.p_sender in SaneNode && c.c_sender = p.p_sender
}

fact prev_does_not_match {

  all h : Hash |
    h.h_prev.h_view = h.h_view.v_prev

}

// how to do the degree of ancestors

// run ownPrev for 10

run some_prepare_new for 4
