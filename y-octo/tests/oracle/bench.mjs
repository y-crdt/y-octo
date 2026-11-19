// Optional comparison runner replacing the removed Rust/Yrs bench targets.
// Run `npm run bench --prefix y-octo/tests/oracle -- [update.bin ...]`.
import fs from "node:fs";
import { performance } from "node:perf_hooks";
import * as Y from "yjs-13-6-33";
import * as encoding from "lib0/encoding";
import * as decoding from "lib0/decoding";
const n = Number(process.env.BENCH_SIZE ?? 100000);
function measure(name, body) {
  const start = performance.now();
  body();
  console.log(
    JSON.stringify({
      engine: "yjs-13.6.33",
      name,
      count: n,
      elapsed_ms: Math.round(performance.now() - start),
    }),
  );
}
measure("map/insert-get-remove", () => {
  const d = new Y.Doc();
  const m = d.getMap("m");
  d.transact(() => {
    for (let i = 0; i < n; i++) m.set(String(i), i);
    for (let i = 0; i < n; i++) if (m.get(String(i)) !== i) throw Error("map");
    for (let i = 0; i < n; i++) m.delete(String(i));
  });
});
measure("array/insert-range-remove", () => {
  const d = new Y.Doc();
  const a = d.getArray("a");
  a.insert(
    0,
    Array.from({ length: n }, (_, i) => i),
  );
  a.delete(0, n);
});
measure("text/insert-remove", () => {
  const d = new Y.Doc();
  const t = d.getText("t");
  t.insert(0, "x".repeat(n));
  t.delete(0, n);
});
measure("codec/varints", () => {
  const e = encoding.createEncoder();
  for (let i = 0; i < n; i++) {
    encoding.writeVarUint(e, i);
    encoding.writeVarInt(e, -i);
  }
  const d = decoding.createDecoder(encoding.toUint8Array(e));
  for (let i = 0; i < n; i++) {
    if (decoding.readVarUint(d) !== i || decoding.readVarInt(d) !== -i)
      throw Error("codec");
  }
});
for (const file of process.argv.slice(2)) {
  const bytes = fs.readFileSync(file);
  measure(`decode/${file}`, () => Y.decodeUpdate(bytes));
  measure(`apply-encode/${file}`, () => {
    const d = new Y.Doc();
    Y.applyUpdate(d, bytes);
    Y.encodeStateAsUpdate(d);
  });
}
