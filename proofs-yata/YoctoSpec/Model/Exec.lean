/-
Trace executor: replicas driven by updates taken from the wire, by local
operations of the model, and by explicit split, merge and GC steps.
-/
import YoctoSpec.Model.Store

namespace YoctoSpec

inductive Op where
  /-- applies an update (structs and delete set) to a replica -/
  | apply (replica : Nat) (u : Update)
  /-- inserts `text` right after the clock `after` (at the start without one) -/
  | insert (replica : Nat) (after : Option Id) (text : List Char)
  /-- deletes clock ranges -/
  | delete (replica : Nat) (ranges : List DelRange)
  /-- sends `dst` what it is missing from `src`, with the delete set of `src` -/
  | sync (src dst : Nat)
  | split (replica : Nat) (x : Id)
  | merge (replica : Nat) (idx : Nat)
  | mergeAll (replica : Nat)
  /-- `Content::Deleted` for every deleted item -/
  | gcContent (replica : Nat)
  /-- `Node::GC` for the deleted block at `idx` -/
  | gcNode (replica : Nat) (idx : Nat)
  /-- `Doc::gc` -/
  | gc (replica : Nat)
deriving Repr, Inhabited

def Op.replica : Op → Nat
  | .apply r _ => r
  | .insert r _ _ => r
  | .delete r _ => r
  | .sync _ d => d
  | .split r _ => r
  | .merge r _ => r
  | .mergeAll r => r
  | .gcContent r => r
  | .gcNode r _ => r
  | .gc r => r

structure Replica where
  client : Nat
  /-- `DocOptions::auto_gc`: deleted items drop their content at every commit -/
  autoGc : Bool
  store : Store
deriving Repr, Inhabited

namespace Replica

/-- End of a transaction. -/
def commit (r : Replica) (s : Store) : Replica :=
  { r with store := if r.autoGc then { s with blocks := gcContent s.blocks } else s }

def localInsert (r : Replica) (after : Option Id) (text : List Char) : Replica :=
  let fl := flatten r.store.blocks
  let k := ixL fl after
  let b : Block :=
    { id := ⟨r.client, r.store.state r.client⟩
      left := after
      right := idAt fl (k + 1)
      deleted := false
      content := Content.str text }
  if text.isEmpty then r else r.commit (r.store.applyUpdate ⟨[Wire.item b], []⟩)

end Replica

def getReplica (rs : List Replica) (i : Nat) : Replica := rs.getD i default

def setReplica (rs : List Replica) (i : Nat) (r : Replica) : List Replica := rs.set i r

def step (rs : List Replica) (op : Op) : List Replica :=
  let r := getReplica rs op.replica
  let s := r.store
  let r' : Replica :=
    match op with
    | .apply _ u => r.commit (s.applyUpdate u)
    | .insert _ after text => r.localInsert after text
    | .delete _ ranges => r.commit (s.applyUpdate ⟨[], ranges⟩)
    | .sync src _ => r.commit (s.applyUpdate ((getReplica rs src).store.diff s.state))
    | .split _ x => { r with store := { s with blocks := split s.blocks x } }
    | .merge _ idx => { r with store := { s with blocks := mergeAt idx s.blocks } }
    | .mergeAll _ => { r with store := { s with blocks := mergeAll s.blocks } }
    | .gcContent _ => { r with store := { s with blocks := gcContent s.blocks } }
    | .gcNode _ idx =>
      let g := gcNodeAt idx s.blocks
      { r with store := { s with blocks := g.1, gc := s.gc ++ g.2.toList } }
    | .gc _ => { r with store := s.gcAll }
  setReplica rs op.replica r'

/-! ## Snapshots -/

/-- One clock of the store: id, origins, and what it holds: `some ch` for text,
`none` for `Content::Deleted`; `gc` marks a clock of a `Node::GC`. -/
structure UnitInfo where
  id : Id
  left : Option Id
  right : Option Id
  ch : Option Char
  gc : Bool
  deleted : Bool
deriving Repr, Inhabited

def unitInfosFrom (c : Nat) (right : Option Id) (deleted : Bool) :
    Nat → Option Id → List (Option Char) → List UnitInfo
  | _, _, [] => []
  | k, l, ch :: t =>
    ⟨⟨c, k⟩, l, right, ch, false, deleted⟩ ::
      unitInfosFrom c right deleted (k + 1) (some ⟨c, k⟩) t

def Block.unitInfos (b : Block) : List UnitInfo :=
  let chs : List (Option Char) :=
    match b.content with
    | Content.str cs => cs.map some
    | Content.del n => List.replicate n none
  unitInfosFrom b.id.client b.right b.deleted b.id.clock b.left chs

def gcUnitInfos (g : Id × Nat) : List UnitInfo :=
  (List.range g.2).map (fun j => ⟨⟨g.1.client, g.1.clock + j⟩, none, none, none, true, true⟩)

def idLt (a b : Id) : Bool := decide (a < b)

def sortBy {α : Type} (lt : α → α → Bool) (l : List α) : List α := (l.toArray.qsort lt).toList

/-- Every clock of the store, ordered by id. -/
def Store.unitInfos (s : Store) : List UnitInfo :=
  sortBy (fun a b => idLt a.id b.id)
    (s.blocks.flatMap Block.unitInfos ++ s.gc.flatMap gcUnitInfos)

def dedup : List Nat → List Nat
  | [] => []
  | a :: t => if t.contains a then dedup t else a :: dedup t

/-- The state vector, ordered by client. -/
def Store.stateVector (s : Store) : List (Nat × Nat) :=
  let clients := sortBy (fun a b => decide (a < b))
    (dedup (s.blocks.map (·.id.client) ++ s.gc.map (·.1.client)))
  clients.map (fun c => (c, s.state c))

/-- Merges sorted ids into ranges. -/
def toRanges : List Id → List DelRange
  | [] => []
  | x :: t =>
    match toRanges t with
    | [] => [⟨x.client, x.clock, 1⟩]
    | r :: rs =>
      if r.client = x.client ∧ r.clock = x.clock + 1 then ⟨x.client, x.clock, r.len + 1⟩ :: rs
      else ⟨x.client, x.clock, 1⟩ :: r :: rs

/-- `Doc::get_delete_sets`: the clocks of the deleted items and of the
`Node::GC` structs, as sorted ranges. -/
def Store.deleteRanges (s : Store) : List DelRange :=
  toRanges (sortBy idLt
    (s.blocks.flatMap Block.deletedIds ++ (s.gc.flatMap gcUnitInfos).map (·.id)))

/-- The visible clocks, in document order. -/
def Store.visibleIds (s : Store) : List Id :=
  s.blocks.flatMap (fun b => if b.deleted then [] else b.units.map Item.id)

/-- The blocks ordered by id, and the `Node::GC` ranges. -/
def Store.structs (s : Store) : List Block := sortBy (fun a b => idLt a.id b.id) s.blocks

end YoctoSpec
