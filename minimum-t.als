module minimalt

sig Hash {
  prev: lone Hash
}

pred ownPrev (h: Hash) {
  h in h.prev
}

run ownPrev for 3
