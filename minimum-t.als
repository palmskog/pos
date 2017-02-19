module minimalt

sig Hash {
  prev: lone Hash
}

fact {
  no x : Hash | x in x.(*prev)
}

pred ownPrev (h: Hash) {
  h in h.prev
}

run ownPrev for 10
