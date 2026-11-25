/-
Unit-level YATA integration, following `find_conflict_left`
(`y-octo/src/doc/common/algorithm.rs`) and the linking part of
`DocStore::integrate` (`y-octo/src/doc/store.rs`) branch for branch.
-/
import YoctoSpec.Model.Basic

namespace YoctoSpec

/-- `find_conflict_left`. `cands` is the chain reached from `conflict` through
`next`; `left` is the current left neighbour, `before` is `before_origin` and
`conflicting` is `conflicting`. `owner` is `origin_owner`: the start id of the
struct that contains an origin. -/
def findConflictLeft (this : Item) (right : Option Id) (owner : Id → Option Id) :
    List Item → Option Id → List Id → List Id → Option Id
  | [], left, _, _ => left
  | c :: rest, left, before, conflicting =>
    -- `if right.as_ref() == Some(&current) { break }`
    if right = some c.id then left
    else
      if this.left = c.left then
        if c.id.client < this.id.client then
          -- `left = Some(current); conflicting.clear()`
          findConflictLeft this right owner rest (some c.id) (c.id :: before) []
        else if this.right = c.right then left
        else findConflictLeft this right owner rest left (c.id :: before) (c.id :: conflicting)
      else
        match c.left with
        | none => left
        | some cl =>
          match owner cl with
          | none => left
          | some o =>
            -- `if !before_origin.contains(&owner) { break }`
            if o ∈ c.id :: before then
              -- `if !conflicting.contains(&owner) { left = Some(current); conflicting.clear() }`
              if o ∈ c.id :: conflicting then
                findConflictLeft this right owner rest left (c.id :: before) (c.id :: conflicting)
              else findConflictLeft this right owner rest (some c.id) (c.id :: before) []
            else left

/-- The items after `x` (`left.right` and its successors). -/
def afterId (x : Id) : List Item → List Item
  | [] => []
  | a :: t => if a.id = x then t else afterId x t

/-- First conflict candidate onwards: `left.right`, or the start of the parent
sequence when there is no left neighbour. -/
def after (o : Option Id) (s : List Item) : List Item :=
  match o with
  | none => s
  | some x => afterId x s

def insertAfterId (x : Id) (i : Item) : List Item → List Item
  | [] => [i]
  | a :: t => if a.id = x then a :: i :: t else a :: insertAfterId x i t

/-- Relinks `left <-> i <-> left.right`; without a left neighbour `i` becomes
the start of the sequence. -/
def insertAfter (o : Option Id) (i : Item) (s : List Item) : List Item :=
  match o with
  | none => i :: s
  | some x => insertAfterId x i s

/-- `origin_owner` of a unit sequence: an integrated id owns itself. -/
def owner (s : List Item) (x : Id) : Option Id :=
  if x ∈ s.map Item.id then some x else none

/-- Integrates one item whose origins are already integrated. -/
def integrate (s : List Item) (i : Item) : List Item :=
  insertAfter (findConflictLeft i i.right (owner s) (after i.left s) i.left [] []) i s

/-- `DocStore::get_state`: the next clock expected from `c`. -/
def nextClock : List Item → Nat → Nat
  | [], _ => 0
  | a :: t, c => if a.id.client = c then max (a.id.clock + 1) (nextClock t c) else nextClock t c

/-- Id of the item at 1-based position `j`; `none` at the two sentinels. -/
def idAt : List Item → Nat → Option Id
  | _, 0 => none
  | [], _ + 1 => none
  | a :: t, j + 1 => if j = 0 then some a.id else idAt t j

/-- The item client `c` creates when it inserts at gap `k` of `s` (between
positions `k` and `k + 1`): its origins are the two neighbours. -/
def mkItem (s : List Item) (c k : Nat) : Item :=
  { id := ⟨c, nextClock s c⟩, left := idAt s k, right := idAt s (k + 1) }

namespace Doc

def empty : Doc := ⟨[], DeleteSet.empty⟩

def integrate (d : Doc) (i : Item) : Doc := { d with items := YoctoSpec.integrate d.items i }

def delete (d : Doc) (x : Id) : Doc := { d with deleted := d.deleted.insert x }

/-- Applies a whole delete set (`DeleteSet::merge`). -/
def deleteAll (d : Doc) (ds : DeleteSet) : Doc := { d with deleted := d.deleted.union ds }

end Doc

end YoctoSpec
