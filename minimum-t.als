module minimalt

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
  hash : Hash,
  view : View
}

sig Prepare {
  hash : Hash,
  view: View,
  view_src : View
}

fact {
   all p : Prepare | p.view_src in (p.view.(^v_prev))
}

pred some_prepare {
   some Prepare
}

// run ownPrev for 10

run some_prepare for 3
