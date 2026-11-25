/-
Block-level model of a `y-octo` text sequence: items that cover a run of
clocks, with split, merge, garbage collection and the pending queue, as in
`y-octo/src/doc/store.rs`.

`flatten` maps a block sequence to the unit-level model of
`YoctoSpec.Model.Yata`: a block of length `n` stands for `n` unit items, the
`k`-th of which has the `k - 1`-th as left origin and the right origin of the
block (this is what `Item::split_at` gives the right half of a split).
-/
import YoctoSpec.Model.Yata

namespace YoctoSpec

/-- `Content::String` (one `Char` per clock; the model works with texts whose
characters take one UTF-16 code unit) or `Content::Deleted`. -/
inductive Content where
  | str (cs : List Char)
  | del (n : Nat)
deriving DecidableEq, Repr, Inhabited

namespace Content

def len : Content → Nat
  | str cs => cs.length
  | del n => n

def take (c : Content) (k : Nat) : Content :=
  match c with
  | str cs => str (cs.take k)
  | del n => del (min k n)

def drop (c : Content) (k : Nat) : Content :=
  match c with
  | str cs => str (cs.drop k)
  | del n => del (n - k)

def sameKind : Content → Content → Bool
  | str _, str _ => true
  | del _, del _ => true
  | _, _ => false

/-- Content of two merged items (`Node::merge`); only used on the same kind. -/
def append : Content → Content → Content
  | str a, str b => str (a ++ b)
  | del a, del b => del (a + b)
  | c, _ => c

def chars : Content → List Char
  | str cs => cs
  | del _ => []

end Content

/-- `Item` of a text sequence: the clocks `id.clock .. id.clock + len - 1` of
`id.client`. `left` and `right` are the origins of the first clock. -/
structure Block where
  id : Id
  left : Option Id
  right : Option Id
  deleted : Bool
  content : Content
deriving DecidableEq, Repr, Inhabited

namespace Block

def len (b : Block) : Nat := b.content.len

/-- `Item::last_id`. -/
def lastId (b : Block) : Id := ⟨b.id.client, b.id.clock + b.len - 1⟩

/-- The `ConflictItem` of a block: its first clock. -/
def toItem (b : Block) : Item := ⟨b.id, b.left, b.right⟩

def contains (b : Block) (x : Id) : Bool :=
  decide (x.client = b.id.client ∧ b.id.clock ≤ x.clock ∧ x.clock < b.id.clock + b.len)

end Block

/-- `n` unit items of client `c` from clock `k`: the first has left origin `l`,
each next one its predecessor; all have right origin `right`. -/
def unitsFrom (c : Nat) (right : Option Id) : Nat → Option Id → Nat → List Item
  | _, _, 0 => []
  | k, l, n + 1 => ⟨⟨c, k⟩, l, right⟩ :: unitsFrom c right (k + 1) (some ⟨c, k⟩) n

def Block.units (b : Block) : List Item :=
  unitsFrom b.id.client b.right b.id.clock b.left b.len

/-- The unit-level sequence a block sequence stands for. -/
def flatten (bs : List Block) : List Item := bs.flatMap Block.units

/-- Ids of the deleted clocks of a block. -/
def Block.deletedIds (b : Block) : List Id :=
  if b.deleted then b.units.map Item.id else []

/-- The delete set of a block sequence (`DocStore::generate_delete_set`). -/
def deletedSet (bs : List Block) : DeleteSet :=
  (bs.flatMap Block.deletedIds).foldl DeleteSet.insert DeleteSet.empty

/-- The unit-level document a block sequence stands for. -/
def toDoc (bs : List Block) : Doc := ⟨flatten bs, deletedSet bs⟩

/-- The visible text. -/
def visible (bs : List Block) : List Char :=
  bs.flatMap (fun b => if b.deleted then [] else b.content.chars)

/-! ## Split -/

/-- Left half of `Item::split_at` at offset `k`: the first `k` clocks. -/
def Block.leftPart (b : Block) (k : Nat) : Block := { b with content := b.content.take k }

/-- Right half of `Item::split_at` at offset `k`: its left origin is the last
clock of the left half, and it keeps the right origin. -/
def Block.rightPart (b : Block) (k : Nat) : Block :=
  { id := ⟨b.id.client, b.id.clock + k⟩
    left := some ⟨b.id.client, b.id.clock + k - 1⟩
    right := b.right
    deleted := b.deleted
    content := b.content.drop k }

/-- `Item::split_at`: the two halves of `b` at offset `k` (`0 < k < b.len`). -/
def Block.splitAt (b : Block) (k : Nat) : List Block := [b.leftPart k, b.rightPart k]

def splitBlock (x : Id) (b : Block) : List Block :=
  if x.client = b.id.client ∧ b.id.clock < x.clock ∧ x.clock < b.id.clock + b.len then
    b.splitAt (x.clock - b.id.clock)
  else [b]

/-- `split_at_and_get_right(x)`: afterwards a block starts at `x`. -/
def split (bs : List Block) (x : Id) : List Block := bs.flatMap (splitBlock x)

/-- `split_at_and_get_left(x)`: afterwards a block ends at `x`. -/
def splitAfter (bs : List Block) (x : Id) : List Block := split bs ⟨x.client, x.clock + 1⟩

/-! ## Merge -/

/-- The conditions of `Node::merge` for two neighbours of the sequence. -/
def canMerge (a b : Block) : Bool :=
  decide (a.id.client = b.id.client ∧ a.id.clock + a.len = b.id.clock ∧ 0 < a.len ∧
    b.left = some a.lastId ∧ a.right = b.right ∧ a.deleted = b.deleted) &&
    a.content.sameKind b.content

def mergeBlocks (a b : Block) : Block := { a with content := a.content.append b.content }

/-- `Node::merge` of the blocks at `idx` and `idx + 1`, when they can merge. -/
def mergeAt : Nat → List Block → List Block
  | _, [] => []
  | _, [a] => [a]
  | 0, a :: b :: t => if canMerge a b then mergeBlocks a b :: t else a :: b :: t
  | n + 1, a :: b :: t => a :: mergeAt n (b :: t)

/-- Merges every pair of neighbours that can merge (`DocStore::optimize_all`
after its GC pass). -/
def mergeAll : List Block → List Block
  | [] => []
  | a :: t =>
    match mergeAll t with
    | [] => [a]
    | b :: t' => if canMerge a b then mergeBlocks a b :: t' else a :: b :: t'

/-! ## Garbage collection -/

/-- `gc_item_content(_, parent_gced = false)`: a deleted item keeps its place
in the sequence and its content becomes `Content::Deleted`. -/
def gcBlock (b : Block) : Block :=
  if b.deleted then { b with content := Content.del b.len } else b

def gcContent (bs : List Block) : List Block := bs.map gcBlock

/-- `gc_item_content(_, parent_gced = true)`: the deleted block at `idx` leaves
the sequence; the store keeps its clock range as a `Node::GC`. The result is
the sequence and the range. -/
def gcNodeAt : Nat → List Block → List Block × Option (Id × Nat)
  | _, [] => ([], none)
  | 0, b :: t => if b.deleted then (t, some (b.id, b.len)) else (b :: t, none)
  | n + 1, b :: t => let r := gcNodeAt n t; (b :: r.1, r.2)

/-! ## Integration -/

/-- `origin_owner`: the start id of the block that contains `x`. -/
def ownerB : List Block → Id → Option Id
  | [], _ => none
  | b :: t, x => if b.contains x then some b.id else ownerB t x

def afterBId (x : Id) : List Block → List Block
  | [] => []
  | b :: t => if b.id = x then t else afterBId x t

/-- The blocks after the block that starts at `o` (all of them without one). -/
def afterB (o : Option Id) (bs : List Block) : List Block :=
  match o with
  | none => bs
  | some x => afterBId x bs

def insertAfterBId (x : Id) (n : Block) : List Block → List Block
  | [] => [n]
  | b :: t => if b.id = x then b :: n :: t else b :: insertAfterBId x n t

def insertAfterB (o : Option Id) (n : Block) (bs : List Block) : List Block :=
  match o with
  | none => n :: bs
  | some x => insertAfterBId x n bs

/-- `repair`, left origin: `split_at_and_get_left`, after which a block ends at
the origin. -/
def splitLeft (o : Option Id) (bs : List Block) : List Block :=
  match o with
  | some l => splitAfter bs l
  | none => bs

/-- `repair`, right origin: `split_at_and_get_right`, after which a block
starts at the origin. -/
def splitRight (o : Option Id) (bs : List Block) : List Block :=
  match o with
  | some r => split bs r
  | none => bs

/-- The conflict scan of `DocStore::integrate` on blocks: the candidates are
the blocks after the left neighbour, `left` is a block, and the two sets hold
block starts, which `origin_owner` (`ownerB`) maps origins to. -/
def scanB (bs : List Block) (b : Block) : Option Id :=
  findConflictLeft b.toItem b.right (ownerB bs)
    ((afterB (b.left.bind (ownerB bs)) bs).map Block.toItem) (b.left.bind (ownerB bs)) [] []

/-- `DocStore::repair` (splitting at the origins) and `DocStore::integrate` for
an item whose dependencies are integrated and that does not overlap the store. -/
def integrateBlock (bs : List Block) (b : Block) : List Block :=
  insertAfterB (scanB (splitRight b.right (splitLeft b.left bs)) b) b
    (splitRight b.right (splitLeft b.left bs))

/-- `DocStore::get_state` of a block sequence. -/
def stateB : List Block → Nat → Nat
  | [], _ => 0
  | b :: t, c => if b.id.client = c then max (b.id.clock + b.len) (stateB t c) else stateB t c

/-- The part of a struct after its first `k` clocks (`integrate(node, offset)`):
its left origin is the clock before it. -/
def Block.trim (b : Block) (k : Nat) : Block := if k = 0 then b else b.rightPart k

/-! ## Deletion -/

def markBlock (c lo hi : Nat) (b : Block) : Block :=
  if b.id.client = c ∧ lo ≤ b.id.clock ∧ b.id.clock + b.len ≤ hi then { b with deleted := true }
  else b

/-- Marks the blocks of client `c` that lie inside `[lo, hi)`. -/
def markRange (c lo hi : Nat) (bs : List Block) : List Block := bs.map (markBlock c lo hi)

/-- `DocStore::delete_range`: splits at both ends of the range and deletes the
blocks in between. -/
def deleteRange (bs : List Block) (c lo hi : Nat) : List Block :=
  markRange c lo hi (split (split bs ⟨c, lo⟩) ⟨c, hi⟩)

end YoctoSpec
