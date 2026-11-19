// Runs the wasm32-unknown-unknown smoke module built from lib.rs, without
// imports (no JS randomness or clock backend), and reads its update with the
// pinned Yjs versions.
//
//   cargo build --manifest-path y-octo/tests/wasm/Cargo.toml \
//     --target wasm32-unknown-unknown --release
//   node y-octo/tests/wasm/run.mjs
import fs from "node:fs";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import { webcrypto } from "node:crypto";
import { Worker, isMainThread, parentPort } from "node:worker_threads";
import { fileURLToPath } from "node:url";

const require = createRequire(
  fileURLToPath(new URL("../oracle/package.json", import.meta.url)),
);
const wasm = fs.readFileSync(
  process.argv[2] ??
    fileURLToPath(
      new URL(
        "./target/wasm32-unknown-unknown/release/y_octo_wasm_smoke.wasm",
        import.meta.url,
      ),
    ),
);
assert.deepEqual(
  WebAssembly.Module.imports(new WebAssembly.Module(wasm)),
  [],
  "no host imports",
);

/// Instantiates the module and runs it with a host-drawn client ID and the
/// host's monotonic time; returns the client ID and the encoded update.
async function runModule() {
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const [hi, lo] = webcrypto.getRandomValues(new Uint32Array(2));
  const client = (BigInt(hi & 0x1fffff) << 32n) | BigInt(lo) || 1n;
  const now = BigInt(Math.floor(performance.now())) + 1n;
  const step = instance.exports.run(client, now);
  assert.equal(step, 0, `step ${step} of the wasm smoke run failed`);
  const memory = new Uint8Array(instance.exports.memory.buffer);
  const ptr = instance.exports.output_ptr();
  return {
    client,
    update: memory.slice(ptr, ptr + instance.exports.output_len()),
  };
}

if (!isMainThread) {
  // the same run inside a Worker
  parentPort.postMessage(await runModule());
  process.exit(0);
}
const runs = [await runModule()];
runs.push(
  await new Promise((resolve, reject) => {
    const worker = new Worker(new URL(import.meta.url), {
      argv: process.argv.slice(2),
    });
    worker.once("message", resolve);
    worker.once("error", reject);
  }),
);

for (const [where, { client, update }] of runs.map((run, i) => [
  i ? "worker" : "main thread",
  run,
])) {
  for (const version of ["yjs-13-6-21", "yjs-13-6-33"]) {
    const Y = await import(require.resolve(version));
    const doc = new Y.Doc();
    Y.applyUpdate(doc, update);
    const text = doc.getText("text");
    assert.equal(text.toString(), "hello world", `${where} ${version}`);
    assert.deepEqual(
      text.toDelta(),
      [{ insert: "hello", attributes: { bold: true } }, { insert: " world" }],
      `${where} ${version}`,
    );
    assert.ok(
      Y.decodeUpdate(update).structs.some(
        (s) => BigInt(s.id.client) === client,
      ),
      `${where} ${version}: structs by the host's client ID`,
    );
  }
  console.log(
    `wasm smoke (${where}): ${update.length}-byte update read by both Yjs versions`,
  );
}
