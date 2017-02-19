module minimalt

sig View {
  prev: lone View
}

sig Hash {
  prev: lone Hash
}

fact {
  no x : Hash | x in x.(*prev)
}

sig Commit {
  commit_h : Hash,
  commit_v : View
}

sig Prepare {
  prepare_h : Hash,
  prepare_view: View,
  prepare_view_src : View
}

pred ownPrev (h: Hash) {
  h in h.prev
}

pred any {
}

// run ownPrev for 10

run any for 10
