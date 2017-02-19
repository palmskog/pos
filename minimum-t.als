module minimalt

sig View {
//  prev: lone View
}

sig Hash {
  prev: lone Hash
}

fact {
  no x : Hash | x in x.(^prev)
}

// sig Commit {
 //  hash : Hash,
 // view : View
//}

//sig Prepare {
//  hash : Hash,
//  view: View,
//  view_src : View
//}

pred ownPrev (h: Hash) {
  h in h.prev
}

pred viewSrcNotOlder (p : Hash) {
  // p.view_src in (p.view)
}

pred any {
}

// run ownPrev for 10

run viewSrcNotOlder for 10
