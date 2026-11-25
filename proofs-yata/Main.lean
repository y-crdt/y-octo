/-
`yocto-spec`: runs a JSON trace on the block-level model and prints the state
of the replica every step touched, and the final state of all replicas.

Usage: `yocto-spec <trace.json>`.

Trace:
```
{ "replicas": [{ "client": 1, "gc": false }, ...],
  "steps": [
    { "op": "apply", "replica": 0,
      "structs": [{ "kind": "item", "client": 1, "clock": 0, "text": "ab",
                    "left": null, "right": [2, 5] },
                  { "kind": "deleted", "client": 1, "clock": 2, "len": 3,
                    "left": [1, 1], "right": null },
                  { "kind": "gc", "client": 3, "clock": 0, "len": 2 },
                  { "kind": "skip", "client": 3, "clock": 2, "len": 1 }],
      "ds": [[1, 0, 2]] },
    { "op": "insert", "replica": 0, "after": [1, 1], "text": "xy" },
    { "op": "delete", "replica": 0, "ranges": [[1, 0, 2]] },
    { "op": "sync", "from": 0, "to": 1 },
    { "op": "split", "replica": 0, "id": [1, 1] },
    { "op": "merge", "replica": 0, "index": 0 },
    { "op": "mergeAll", "replica": 0 },
    { "op": "gcContent", "replica": 0 },
    { "op": "gcNode", "replica": 0, "index": 0 },
    { "op": "gc", "replica": 0 } ] }
```
-/
import Lean.Data.Json
import YoctoSpec.Model.Exec

open Lean YoctoSpec

namespace YoctoSpec.Cli

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

def optField (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def natField (j : Json) (k : String) : Except String Nat := do
  (← field j k).getNat?

def strField (j : Json) (k : String) : Except String String := do
  (← field j k).getStr?

def parseId (j : Json) : Except String Id := do
  let a ← j.getArr?
  if a.size = 2 then
    return ⟨← a[0]!.getNat?, ← a[1]!.getNat?⟩
  else throw s!"expected [client, clock], got {j.compress}"

def parseOptId (j : Json) : Except String (Option Id) :=
  if j.isNull then pure none else do return some (← parseId j)

def parseRange (j : Json) : Except String DelRange := do
  let a ← j.getArr?
  if a.size = 3 then
    return ⟨← a[0]!.getNat?, ← a[1]!.getNat?, ← a[2]!.getNat?⟩
  else throw s!"expected [client, clock, len], got {j.compress}"

def parseList {α : Type} (f : Json → Except String α) (j : Json) : Except String (List α) :=
  if j.isNull then pure [] else do
    let a ← j.getArr?
    a.toList.mapM f

def parseWire (j : Json) : Except String Wire := do
  let kind ← strField j "kind"
  let id : Id := ⟨← natField j "client", ← natField j "clock"⟩
  match kind with
  | "item" =>
    let text ← strField j "text"
    let left ← parseOptId (optField j "left")
    let right ← parseOptId (optField j "right")
    return Wire.item ⟨id, left, right, false, Content.str text.toList⟩
  | "deleted" =>
    let len ← natField j "len"
    let left ← parseOptId (optField j "left")
    let right ← parseOptId (optField j "right")
    return Wire.item ⟨id, left, right, true, Content.del len⟩
  | "gc" => return Wire.gc id (← natField j "len")
  | "skip" => return Wire.skip id (← natField j "len")
  | k => throw s!"unknown struct kind {k}"

def parseOp (j : Json) : Except String Op := do
  let op ← strField j "op"
  match op with
  | "apply" =>
    let structs ← parseList parseWire (optField j "structs")
    let ds ← parseList parseRange (optField j "ds")
    return Op.apply (← natField j "replica") ⟨structs, ds⟩
  | "insert" =>
    let after ← parseOptId (optField j "after")
    return Op.insert (← natField j "replica") after (← strField j "text").toList
  | "delete" =>
    return Op.delete (← natField j "replica") (← parseList parseRange (optField j "ranges"))
  | "sync" => return Op.sync (← natField j "from") (← natField j "to")
  | "split" => return Op.split (← natField j "replica") (← parseId (← field j "id"))
  | "merge" => return Op.merge (← natField j "replica") (← natField j "index")
  | "mergeAll" => return Op.mergeAll (← natField j "replica")
  | "gcContent" => return Op.gcContent (← natField j "replica")
  | "gcNode" => return Op.gcNode (← natField j "replica") (← natField j "index")
  | "gc" => return Op.gc (← natField j "replica")
  | k => throw s!"unknown op {k}"

def parseReplica (j : Json) : Except String Replica := do
  let gc := ((optField j "gc").getBool?).toOption.getD false
  return ⟨← natField j "client", gc, Store.empty⟩

def idJson (x : Id) : Json := Json.arr #[toJson x.client, toJson x.clock]

def optIdJson : Option Id → Json
  | none => Json.null
  | some x => idJson x

def unitJson (u : UnitInfo) : Json :=
  Json.arr #[toJson u.id.client, toJson u.id.clock, optIdJson u.left, optIdJson u.right,
    match u.ch with
    | none => Json.null
    | some c => toJson c.toNat,
    Json.bool u.gc, Json.bool u.deleted]

def blockJson (b : Block) : Json :=
  Json.arr #[toJson b.id.client, toJson b.id.clock, toJson b.len,
    Json.str (match b.content with
      | Content.str _ => "str"
      | Content.del _ => "del"),
    Json.bool b.deleted]

def listJson {α : Type} (f : α → Json) (l : List α) : Json := Json.arr (l.map f).toArray

/-- An update as its clock ranges, one entry for every struct and every
deleted range it holds, as it holds them: a clock the update carries twice is
there twice. A `Skip` carries no clock. -/
def exportJson (u : Update) : Json :=
  let range (client clock len : Nat) : Json := Json.arr #[toJson client, toJson clock, toJson len]
  Json.mkObj [
    ("structs", listJson (fun (w : Wire) => range w.id.client w.id.clock w.len)
      (u.structs.filter (fun w =>
        match w with
        | Wire.skip _ _ => false
        | _ => true))),
    ("ds", listJson (fun (d : DelRange) => range d.client d.clock d.len) u.ds)]

/-- The state of replica `i`. `export` is everything the replica would send to
a replica that has nothing (`diff` from the empty state vector), what waits
included. -/
def snapshot (i : Nat) (r : Replica) : Json :=
  let s := r.store
  Json.mkObj [
    ("replica", toJson i),
    ("text", Json.str (String.ofList (visible s.blocks))),
    ("ids", listJson idJson s.visibleIds),
    ("sv", listJson (fun (p : Nat × Nat) => Json.arr #[toJson p.1, toJson p.2]) s.stateVector),
    ("ds", listJson (fun (d : DelRange) => Json.arr #[toJson d.client, toJson d.clock, toJson d.len])
      s.deleteRanges),
    ("pending", Json.bool (!s.pending.isEmpty || !s.pendingDs.isEmpty)),
    ("export", exportJson (s.diff (fun _ => 0))),
    ("units", listJson unitJson s.unitInfos),
    ("blocks", listJson blockJson s.structs),
    ("order", listJson (fun (b : Block) => idJson b.id) s.blocks),
    ("gc", listJson (fun (g : Id × Nat) => Json.arr #[toJson g.1.client, toJson g.1.clock, toJson g.2])
      s.gc)]

def checkOp (n : Nat) (op : Op) : Except String Unit := do
  if n ≤ op.replica then throw s!"replica {op.replica} out of range"
  match op with
  | Op.sync src _ => if n ≤ src then throw s!"replica {src} out of range"
  | _ => pure ()

def run (trace : Json) : Except String Json := do
  let rs ← parseList parseReplica (← field trace "replicas")
  let ops ← parseList parseOp (← field trace "steps")
  for op in ops do
    checkOp rs.length op
  let res := ops.foldl
    (fun (acc : List Replica × Array Json) op =>
      let rs' := step acc.1 op
      (rs', acc.2.push (snapshot op.replica (getReplica rs' op.replica))))
    (rs, #[])
  return Json.mkObj [
    ("steps", Json.arr res.2),
    ("final", listJson (fun i => snapshot i (getReplica res.1 i)) (List.range res.1.length))]

end YoctoSpec.Cli

def main (args : List String) : IO UInt32 := do
  let input ←
    match args with
    | [path] => IO.FS.readFile path
    | _ => do
      IO.eprintln "usage: yocto-spec <trace.json>"
      return 2
  match Json.parse input >>= YoctoSpec.Cli.run with
  | .ok out =>
    IO.println out.compress
    return 0
  | .error e =>
    IO.eprintln s!"yocto-spec: {e}"
    return 1
