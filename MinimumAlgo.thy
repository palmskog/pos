theory MinimumAlgo

imports Main

begin

datatype hash = Hash int
type_synonym view = int

record commit =
  CommitHash :: hash
  CommitView :: view

record prepare =
  PrepareHash :: hash
  PrepareView :: view
  PrepareViewSource :: view

datatype message =
  Commit commit
| Prepare prepare

datatype node = Node int

type_synonym sent = "node * message"

record situation =
  Nodes :: "node set"
  Messages :: "sent set"
  PrevHash :: "hash \<Rightarrow> hash option"

end
