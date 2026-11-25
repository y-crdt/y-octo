# Trust assumptions for the Rust core proofs

Charon and Aeneas translate `y-octo-core` into Lean. The proofs describe that translation.
The document engine calls selected core functions. It also maintains state outside the extraction.
Section 4 identifies where each guarantee applies.

## 1. Extraction

[toolchain-lock.json](toolchain-lock.json) pins the extractor, Rust toolchain, Lean toolchain, and Mathlib revision.
The proofs assume that the translation preserves Rust semantics.
They also assume that the Aeneas models describe the standard library operations the core uses.

One distinction matters for insertion. The Aeneas model of `Vec::insert` requires an index below the vector length.
The core calls `Vec::push` at the end and uses `Vec::insert` only inside the vector.

The extraction configuration omits selected trait implementations. The static audit checks these exceptions.
It also rejects custom external stubs and proof holes.
The extraction check compares fresh output with the files in [YoctoCore/Code](YoctoCore/Code).

## 2. Kernel and dependencies

The audit replays declarations from `YoctoCore` and `YoctoSpec` in the Lean kernel.
It reads compiled modules without loading their extensions. It checks public, private, and generated declarations.
The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The audit also checks that each required name denotes a public theorem.

The audit trusts the Lean kernel, its module reader, the toolchain libraries, Aeneas, and the pinned dependencies.
Lake supplies the link between source files and compiled modules. Replay checks the declarations in those modules.
Generated unsafe or partial implementation details stay outside kernel replay. A checked theorem cannot depend on them.
The proof statements and the translation tools remain part of the review boundary.

## 3. Reproduce the checks

Use the pinned Linux x86-64 toolchain. Run these commands from the repository root.

```sh
bash proofs-yata/scripts/audit.sh --static
bash proofs/scripts/bootstrap.sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
bash proofs/scripts/extract.sh --check
python3 proofs/scripts/audit.py
(cd proofs && lake build)
python3 proofs/scripts/audit.py --all
```

The final command checks compiled declarations and runs the audit self-tests.
The [property modules](YoctoCore/Properties) give the exact theorem statements and their hypotheses.

## 4. Production guarantees and boundaries

| Operation | What the core proves | What the document engine supplies |
| --- | --- | --- |
| Varints and UTF-16 | Codec properties and byte boundaries for UTF-16 splits on valid UTF-8 | Rust strings and the cursor that applies successive splits |
| Update V1 decoding | Bounds on input spans under the decoder's sink contract | UTF-8 and JSON validation, duplicate-client checks, and state changes in the sink |
| Deletion ranges | Canonical intervals, union membership, and preservation of the receiver when a checked union exceeds its limit | Input sorting, membership lookup across multiple intervals, and the choice of checked or infallible operation |
| Client timelines | Block lookup by clock, range merges, and slot remapping within one timeline | Client lookup, capacity checks before compound edits, and consistent references across timelines and the arena |
| Item storage | Slot allocation, quarantine, reuse, and the compaction map | Updates to document links after compaction |
| Conflict scans | Candidate lookup and the decisions that advance or stop a scan | Distinct candidate IDs, traversal of document links, and resolution of origins |
| Pending updates and document links | Readiness, split, parent-walk, and link decisions on the supplied inputs | Queue traversal, retries, and application of each decision to the correct container |

**V1 decoding.** The proof covers structural totality and span bounds.
Wire compatibility with Yjs also depends on the Rust sink and interoperability tests.
The unsigned varint proof covers the encode/decode round trip. The signed 32-bit proof covers totality.

**Deletion ranges.** A client can hold at most `2^30` canonical intervals.
Checked unions enforce the limit on the final union. Infallible wrappers can panic above that limit.
Ordered batches can merge overlapping intervals in place.
A random insertion can move existing intervals. The first insertion into a full ring can also require a larger allocation.
The proofs cover the logical intervals. Allocator behavior and the two end-pop operations remain outside their specification.

**Conflict scans.** Each scan uses a keyed table. Lookup correctness holds for every key.
Without the `random` feature, key generation uses build-time seeds and per-instance state.
The proofs give no guarantee about key secrecy, collision frequency, or execution time.

**Store refinement.** `YataStoreCore` models one sequence of items.
Replicas in a legal run agree on their document when they have the same clocks and deletions.
Agreement on visible text also requires matching payloads for live clocks.
Content collection preserves visible text. Whole-struct GC, Skip blocks, and production slot reuse fall outside this store theorem.

A refused integration preserves the abstract document, although repair can split blocks.
The acceptance proof covers origin-free structs that continue their client timeline and fit within capacity.
Tests cover delivery with origins. Range deletion starts at the block containing the requested start clock.
If that clock is absent, the operation leaves the store unchanged.

**Maps and nested types.** The container proofs treat each list as a separate run.
For single-clock map assignments, the last-writer rule leaves at most the last value live.
Replicas must agree on the order and on whether the last value was deleted.
The production store must keep lists separate and apply each link decision to the correct key.
The proofs do not establish those conditions for the whole Rust document engine.

The core also contains reference implementations for state vectors, delete sets, and clock searches.
[Parity tests](../y-octo/tests/core_parity.rs) compare core operations with Rust adapters and store behavior.
The [YATA model guide](../proofs-yata/README.md) describes the convergence hypotheses and the trace oracle.
