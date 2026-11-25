# YATA sequence model

`YoctoSpec` is an executable Lean model of one collaborative text sequence.
It describes how replicas order concurrent inserts, apply deletions, and handle missing dependencies.
The model uses only the Lean toolchain pinned in [lean-toolchain](lean-toolchain).

## Convergence guarantees

- **Item order.** A replica creates an item between adjacent items. Delivery respects its origins and its client's clock order.
  Under these conditions, legal sequences order their common items identically.
- **Deletion.** Replicas may receive deletions in any order. Replicas with the same items and deletions converge.
- **Blocks.** A block represents a run of clocks. Splitting, merging, and collecting deleted content preserve the unit-level document.
  The block convergence theorem assumes live blocks carry the same payload for each clock on both replicas.
- **Pending updates.** Draining the queue processes ready structs and leaves none ready in the resulting store.
  The convergence theorem assumes a legal delivery sequence. Queue readiness alone does not prove that arbitrary arrivals produce such a sequence.

The [model](YoctoSpec/Model) operates on decoded structs. Each character in the text comparison occupies one UTF-16 code unit.
Map keys, nested types, formatting, wire decoding, and duplicate resolution in encoded updates fall outside this model.
The executable model also handles whole-struct GC and delivery of deleted content. The block convergence theorem excludes those steps.
See the [proofs](YoctoSpec/Proofs) for the hypotheses and the [core trust assumptions](../proofs/TRUSTED.md) for their use in Rust.

## Run the model and compare it with Rust

Run these commands from the repository root.

```sh
(
  cd proofs-yata
  bash scripts/audit.sh --static
  lake build --wfail
  bash scripts/audit.sh
  .lake/build/bin/yocto-spec traces/smoke.json
)
YOCTO_SPEC_BIN="$PWD/proofs-yata/.lake/build/bin/yocto-spec" YOCTO_SPEC_REQUIRE=1 \
  cargo test -p y-octo --test lean_yata_differential
```

The static audit checks the sources before the build. The full audit replays compiled model and proof declarations in the Lean kernel.
It checks the required theorems and their axioms. The oracle executable itself sits outside the proof.

The [differential test](../y-octo/tests/lean_yata_differential.rs) applies edits, synchronizes replicas, and runs garbage collection in both implementations.
After each step, it compares text, visible clock IDs, state vectors, delete sets, and pending status.
When pending work clears, it also compares clock origins and live content. After garbage collection, it compares struct boundaries.
It compares deleted clocks as a set. Their relative order and their previous text stay outside the comparison.
