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

The production document uses the core's varint codec.
The unsigned round-trip proof covers encoding followed by decoding. The signed 32-bit proof covers totality.
The other core modules serve as reference implementations for [parity tests](../y-octo/tests/core_parity.rs).

`YataStoreCore` models one sequence of items.
Replicas in a legal run agree on their document when they have the same clocks and deletions.
Agreement on visible text also requires matching payloads for live clocks.
Content collection preserves visible text. Whole-struct GC, Skip blocks, and production slot reuse fall outside this store theorem.

A refused integration preserves the abstract document, although repair can split blocks.
The acceptance proof covers origin-free structs that continue their client timeline and fit within capacity.
Tests cover delivery with origins. Range deletion starts at the block containing the requested start clock.
If that clock is absent, the operation leaves the store unchanged.

The refinement theorem covers one item sequence. It excludes adjacent-block merges and the document engine's parent and map links.
The [YATA model guide](../proofs-yata/README.md) describes the convergence hypotheses and the trace oracle.
