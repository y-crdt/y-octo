/-
The store of one replica: the block sequence, the `Node::GC` ranges, and the
pending queue of structs and deletions whose dependencies are missing
(`DocStore` and `Update::pending_*` of `y-octo`).
-/
import YoctoSpec.Model.Block

namespace YoctoSpec

/-- A struct of an update. -/
inductive Wire where
  /-- an item -/
  | item (b : Block)
  /-- `Node::GC`: a clock range without content or place in a sequence -/
  | gc (id : Id) (len : Nat)
  /-- `Node::Skip`: a gap of the update -/
  | skip (id : Id) (len : Nat)
deriving DecidableEq, Repr, Inhabited

namespace Wire

def id : Wire → Id
  | item b => b.id
  | gc x _ => x
  | skip x _ => x

def len : Wire → Nat
  | item b => b.len
  | gc _ n => n
  | skip _ n => n

end Wire

/-- A deleted clock range: client, first clock, length. -/
structure DelRange where
  client : Nat
  clock : Nat
  len : Nat
deriving DecidableEq, Repr, Inhabited

structure Update where
  structs : List Wire
  ds : List DelRange
deriving Repr, Inhabited

structure Store where
  /-- the sequence -/
  blocks : List Block
  /-- `Node::GC` structs -/
  gc : List (Id × Nat)
  /-- structs that wait for a dependency -/
  pending : List Wire
  /-- deletions of clocks that are not integrated yet -/
  pendingDs : List DelRange
deriving Repr, Inhabited

namespace Store

def empty : Store := ⟨[], [], [], []⟩

def gcState : List (Id × Nat) → Nat → Nat
  | [], _ => 0
  | (x, n) :: t, c => if x.client = c then max (x.clock + n) (gcState t c) else gcState t c

/-- `DocStore::get_state`: the next clock expected from client `c`. -/
def state (s : Store) (c : Nat) : Nat := max (stateB s.blocks c) (gcState s.gc c)

/-- `find_missing_dependency` for one origin under the state vector `sv`: an
origin of another client is missing when `sv` has not reached its clock.
Origins of the same client never block. -/
def depOkSv (sv : Nat → Nat) (client : Nat) (o : Option Id) : Bool :=
  match o with
  | none => true
  | some d => d.client = client || decide (d.clock < sv d.client)

/-- Whether `UpdateIterator` hands a struct on under the state vector `sv`: a
`Skip` is always consumed (and dropped); any other struct needs its clocks to
continue the ones of its client, and an item needs its origins. -/
def readySv (sv : Nat → Nat) (w : Wire) : Bool :=
  match w with
  | Wire.skip _ _ => true
  | Wire.gc x _ => decide (x.clock ≤ sv x.client)
  | Wire.item b =>
    decide (b.id.clock ≤ sv b.id.client) && depOkSv sv b.id.client b.left &&
      depOkSv sv b.id.client b.right

def ready (s : Store) (w : Wire) : Bool := readySv s.state w

def inGc (g : List (Id × Nat)) (x : Id) : Bool :=
  g.any (fun r => decide (r.1.client = x.client ∧ r.1.clock ≤ x.clock ∧ x.clock < r.1.clock + r.2))

/-- Integrates a ready struct. Clocks the store already has are dropped
(`integrate(node, offset)`). An origin that lies in a `Node::GC` range is
dropped by `repair`; an item that named origins and lost all of them cannot
find its parent and becomes a `Node::GC` itself. -/
def applyWire (s : Store) (w : Wire) : Store :=
  let st := s.state w.id.client
  if w.id.clock + w.len ≤ st then s
  else
    let off := st - w.id.clock
    match w with
    | Wire.skip _ _ => s
    | Wire.gc x n => { s with gc := s.gc ++ [(⟨x.client, x.clock + off⟩, n - off)] }
    | Wire.item b =>
      let b' := b.trim off
      let left := b'.left.filter (fun l => !inGc s.gc l)
      let right := b'.right.filter (fun r => !inGc s.gc r)
      if (b'.left.isSome || b'.right.isSome) && left.isNone && right.isNone then
        { s with gc := s.gc ++ [(b'.id, b'.len)] }
      else
        { s with blocks := integrateBlock s.blocks { b' with left := left, right := right } }

/-- The first ready struct of the queue, and the rest. -/
def pickReady (s : Store) : List Wire → Option (Wire × List Wire)
  | [] => none
  | w :: t =>
    if s.ready w then some (w, t)
    else
      match pickReady s t with
      | none => none
      | some (r, t') => some (r, w :: t')

/-- Integrates ready structs of the queue until none is left; what remains
stays pending. -/
def drain : Nat → Store → List Wire → Store × List Wire
  | 0, s, q => (s, q)
  | fuel + 1, s, q =>
    match pickReady s q with
    | none => (s, q)
    | some (w, q') => drain fuel (s.applyWire w) q'

/-- `DeleteSetIterator`, the sequence: the part of a range the store has
integrated is deleted. -/
def rangeBlocks (s : Store) (r : DelRange) : List Block :=
  if s.state r.client ≤ r.clock then s.blocks
  else deleteRange s.blocks r.client r.clock (min (r.clock + r.len) (s.state r.client))

/-- The parts of the range `r` the range `d` does not cover: what is before
`d` and what is after it. -/
def rangeMinus (r d : DelRange) : List DelRange :=
  if r.client = d.client then
    (if r.clock < d.clock then [⟨r.client, r.clock, min (r.clock + r.len) d.clock - r.clock⟩]
      else []) ++
    (if d.clock + d.len < r.clock + r.len then
        [⟨r.client, max r.clock (d.clock + d.len),
          r.clock + r.len - max r.clock (d.clock + d.len)⟩]
      else [])
  else [r]

/-- The parts of `r` none of the ranges `ds` covers. -/
def uncovered (ds : List DelRange) (r : DelRange) : List DelRange :=
  ds.foldl (fun parts d => parts.flatMap (fun part => rangeMinus part d)) [r]

/-- `DeleteSetIterator`, the rest: the part of a range beyond the state of its
client stays pending. A clock that already waits is not added again
(`DeleteSet::merge`): a range received twice, or overlapping one that waits,
adds only the clocks that do not wait yet. -/
def rangePending (s : Store) (r : DelRange) : List DelRange :=
  if r.clock + r.len ≤ s.state r.client then s.pendingDs
  else
    s.pendingDs ++
      uncovered s.pendingDs
        ⟨r.client, max r.clock (s.state r.client), r.clock + r.len - max r.clock (s.state r.client)⟩

def applyRange (s : Store) (r : DelRange) : Store :=
  { s with blocks := rangeBlocks s r, pendingDs := rangePending s r }

/-- The first `k` clocks of a struct dropped. -/
def dropFront (w : Wire) (k : Nat) : Wire :=
  match w with
  | Wire.item b => Wire.item (b.trim k)
  | Wire.gc x n => Wire.gc ⟨x.client, x.clock + k⟩ (n - k)
  | Wire.skip x n => Wire.skip ⟨x.client, x.clock + k⟩ (n - k)

/-- Whether the `j`-th struct `v` of a queue is kept in front of the `i`-th
struct `w` where both carry a clock: `v` is of the same client and starts
earlier, or at the same clock and is longer, or is the same range earlier in
the queue. A `Skip` is a gap and covers nothing.

Like `Update::merge`, the queue then holds every clock of a client once,
each struct cut by what the structs kept in front of it carry; the structs
stay in the order of the queue.
It is not `Update::merge` struct by struct: of two structs that start at the
same clock the model keeps the longer one whole, where the Rust keeps the one
its sources give first and takes the rest from the other. The clocks kept
are the same, the cuts may differ. -/
def keptBefore (j : Nat) (v : Wire) (i : Nat) (w : Wire) : Bool :=
  match v with
  | Wire.skip _ _ => false
  | _ =>
    decide (v.id.client = w.id.client) &&
      (decide (v.id.clock < w.id.clock) ||
        (decide (v.id.clock = w.id.clock) &&
          (decide (w.len < v.len) || (decide (v.len = w.len) && decide (j < i)))))

/-- Where the structs kept in front of the `i`-th struct `w` end (the queue
from its `j`-th struct on): at the first clock of `w` if there is none. -/
def coveredTo (i : Nat) (w : Wire) : Nat → List Wire → Nat
  | _, [] => w.id.clock
  | j, v :: t =>
    if keptBefore j v i w then max (v.id.clock + v.len) (coveredTo i w (j + 1) t)
    else coveredTo i w (j + 1) t

def mergeFrom (q : List Wire) : Nat → List Wire → List Wire
  | _, [] => []
  | i, w :: t =>
    match w with
    | Wire.skip _ _ => w :: mergeFrom q (i + 1) t
    | _ =>
      if w.id.clock + w.len ≤ coveredTo i w 0 q then mergeFrom q (i + 1) t
      else dropFront w (coveredTo i w 0 q - w.id.clock) :: mergeFrom q (i + 1) t

/-- `Update::merge` on a queue of structs: every clock is carried by one
struct. A struct that arrives again, the same range cut at another clock, or a
range that overlaps one of the queue, adds only the clocks no struct in front
of it carries; the order of the queue is kept. -/
def mergeQueue (q : List Wire) : List Wire := mergeFrom q 0 q

/-- The pending structs and the structs of the update, merged and drained. -/
def drained (s : Store) (u : Update) : Store × List Wire :=
  drain (mergeQueue (s.pending ++ u.structs)).length { s with pending := [] }
    (mergeQueue (s.pending ++ u.structs))

/-- `Doc::apply_update`: the pending structs and deletions join the update
(a clock that waits twice waits once), whatever is ready is integrated, the
rest waits. -/
def applyUpdate (s : Store) (u : Update) : Store :=
  (s.pendingDs ++ u.ds).foldl applyRange
    { (drained s u).1 with pending := (drained s u).2, pendingDs := [] }

/-- `Doc::gc` (`DocStore::optimize_all`): every deleted item drops its content,
then everything that can merge is merged. -/
def gcAll (s : Store) : Store := { s with blocks := mergeAll (gcContent s.blocks) }

/-- The items of a sequence from the state vector `sv` on
(`DocStore::diff_structs`). -/
def diffBlocks (sv : Nat → Nat) : List Block → List Wire
  | [] => []
  | b :: t =>
    let st := sv b.id.client
    if b.id.clock + b.len ≤ st then diffBlocks sv t
    else Wire.item (b.trim (st - b.id.clock)) :: diffBlocks sv t

/-- The deleted ranges of a sequence. -/
def dsOf : List Block → List DelRange
  | [] => []
  | b :: t => if b.deleted then ⟨b.id.client, b.id.clock, b.len⟩ :: dsOf t else dsOf t

/-- `DocStore::generate_delete_set`: the deleted items and the `Node::GC`
structs, which count as deleted. -/
def deleteSet (s : Store) : List DelRange :=
  dsOf s.blocks ++ s.gc.map (fun g => ⟨g.1.client, g.1.clock, g.2⟩)

/-- `DocStore::diff_state_vector`: what a replica at `sv` is missing. The
pending structs and deletions are part of it: pending does not mean unknown to
the recipient. -/
def diff (s : Store) (sv : Nat → Nat) : Update :=
  ⟨diffBlocks sv s.blocks ++
      (s.gc.filter (fun g => decide (sv g.1.client < g.1.clock + g.2))).map
        (fun g => Wire.gc g.1 g.2) ++
      s.pending.filter (fun w => decide (sv w.id.client < w.id.clock + w.len)),
    s.deleteSet ++ s.pendingDs⟩

end Store

end YoctoSpec
