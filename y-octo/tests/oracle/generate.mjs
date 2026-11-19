import fs from "node:fs";
import { gzipCorpus } from "./format.mjs";
import { fileURLToPath } from "node:url";
// Separate imports warn about multiple Yjs copies; never pass types across versions.
import * as old from "yjs-13-6-21";
import * as current from "yjs-13-6-33";

export function random(seed) {
  let state = seed >>> 0;
  return (n) => {
    state ^= state << 13;
    state ^= state >>> 17;
    state ^= state << 5;
    return (state >>> 0) % n;
  };
}
export function doc(Y, client) {
  const d = new Y.Doc({ guid: `oracle-${client}`, gc: true });
  d.clientID = client;
  d.getText("text");
  d.getArray("array");
  d.getMap("map");
  return d;
}
export function snapshot(Y, d) {
  const full = Y.encodeStateAsUpdate(d);
  const deleted = Y.decodeUpdate(full).ds.clients;
  return {
    text: d.getText("text").toString(),
    delta: d.getText("text").toDelta(),
    array: d.getArray("array").toJSON(),
    map: d.getMap("map").toJSON(),
    state_vector: [...Y.decodeStateVector(Y.encodeStateVector(d))].sort(
      (a, b) => a[0] - b[0],
    ),
    delete_set: [...deleted]
      .sort((a, b) => a[0] - b[0])
      .map(([c, rs]) => [c, rs.map((r) => [r.clock, r.len])]),
  };
}
function apply(d, op) {
  const t = d.getText("text"),
    a = d.getArray("array"),
    m = d.getMap("map");
  switch (op.kind) {
    case "text_insert":
      t.insert(op.index, op.value);
      break;
    case "text_remove":
      t.delete(op.index, op.length);
      break;
    case "array_insert":
      a.insert(op.index, [op.value]);
      break;
    case "array_remove":
      a.delete(op.index, op.length);
      break;
    case "map_insert":
      m.set(op.key, op.value);
      break;
    case "map_remove":
      m.delete(op.key);
      break;
    case "gc":
      break; // Yjs already performs GC at the transaction boundary.
    default:
      throw new Error(op.kind);
  }
}
// Avoid bisecting a surrogate here: indices are still UTF-16, and every emoji
// occupies two clocks. Dedicated position vectors cover surrogate interiors.
function boundaries(s) {
  const out = [0];
  let n = 0;
  for (const ch of s) {
    n += ch.length;
    out.push(n);
  }
  return out;
}
function live(Y, kind, seed) {
  const a = doc(Y, 101),
    b = doc(Y, 202),
    next = random(seed),
    steps = [];
  function step(op, remote = false) {
    if (remote)
      Y.applyUpdate(b, Y.encodeStateAsUpdate(a, Y.encodeStateVector(b)));
    const writer = remote ? b : a,
      sv = Y.encodeStateVector(writer);
    apply(writer, op);
    const update = Y.encodeStateAsUpdate(writer, sv);
    if (remote) Y.applyUpdate(a, update);
    steps.push({ op, remote, update: [...update], expected: snapshot(Y, a) });
  }
  if (kind === "map") {
    // This prefix must survive tombstone merging and produce a valid new origin.
    for (const op of [
      { kind: "map_insert", key: "k", value: 1 },
      { kind: "map_insert", key: "k", value: 2 },
      { kind: "map_remove", key: "k" },
      { kind: "gc" },
      { kind: "map_insert", key: "k", value: 3 },
    ])
      step(op);
  }
  for (let i = 0; i < 64; i++) {
    const remote = i % 3 === 2;
    if (kind === "text") {
      const bs = boundaries(a.getText("text").toString());
      if (bs.length > 1 && next(3) === 0) {
        const start = next(bs.length - 1),
          end = start + 1 + next(bs.length - start - 1);
        step(
          {
            kind: "text_remove",
            index: bs[start],
            length: bs[end] - bs[start],
          },
          remote,
        );
      } else {
        step(
          {
            kind: "text_insert",
            index: bs[next(bs.length)],
            value: ["a", "NOP", "😀", "界", "🧪z"][next(5)],
          },
          remote,
        );
      }
    } else if (kind === "array") {
      const len = a.getArray("array").length;
      if (len && next(3) === 0) {
        const index = next(len);
        step(
          { kind: "array_remove", index, length: 1 + next(len - index) },
          remote,
        );
      } else
        step(
          { kind: "array_insert", index: next(len + 1), value: next(1000) },
          remote,
        );
    } else {
      const key = ["k", "x", "y"][next(3)];
      if (i % 11 === 0) step({ kind: "gc" });
      step(
        next(4)
          ? { kind: "map_insert", key, value: next(1000) }
          : { kind: "map_remove", key },
        remote,
      );
    }
  }
  return {
    name: `live-${kind}-${seed}`,
    kind,
    seed,
    clients: [101, 202],
    steps,
    full_update: [...Y.encodeStateAsUpdate(a)],
  };
}
const versions = [
  ["13.6.21", old],
  ["13.6.33", current],
];
const output = {
  schema: 1,
  authoritative_version: "13.6.33",
  versions: Object.fromEntries(
    versions.map(([v, Y]) => [
      v,
      ["text", "array", "map"].flatMap((k) =>
        [1, 7, 42, 300].map((s) => live(Y, k, s)),
      ),
    ]),
  ),
};
output.version_differences = output.versions["13.6.33"]
  .filter(
    (s, i) =>
      JSON.stringify(s) !== JSON.stringify(output.versions["13.6.21"][i]),
  )
  .map((s) => s.name);
const path = fileURLToPath(new URL("./live.jsonl.gz", import.meta.url));
const bytes = gzipCorpus(output);
if (process.argv.includes("--check")) {
  if (!fs.readFileSync(path).equals(bytes))
    throw new Error("live.jsonl.gz differs: run npm run generate");
  console.log("live.jsonl.gz is byte-for-byte reproducible");
} else fs.writeFileSync(path, bytes);
