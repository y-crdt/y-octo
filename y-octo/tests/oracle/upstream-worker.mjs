// A thin recorder around the fetched upstream tests, not a port of their code.
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { snapshot } from "./projection.mjs";
const [source, version, output] = process.argv.slice(2);
let nextId = 1000,
  nextGuid = 0,
  clock = 1700000000000,
  documents = [],
  active = true;
globalThis.__factoryNextId = () => nextId++;
globalThis.__factoryGuid = () => `factory-${nextGuid++}`;
Date.now = () => clock++;
const Y = await import(pathToFileURL(path.join(source, "src/index.js")));
const testing = await import("lib0/testing");
const hex = (u) => Buffer.from(u).toString("hex");
function kind(t) {
  if (
    t instanceof Y.XmlElement ||
    t instanceof Y.XmlText ||
    t instanceof Y.XmlFragment
  )
    return "xml";
  if (t instanceof Y.Text) return "text";
  if (t instanceof Y.Array) return "array";
  if (t instanceof Y.Map) return "map";
  if (t instanceof Y.Doc) return "subdocument";
  return "abstract";
}
globalThis.__factoryRegister = (d) => {
  if (!active) return;
  const entry = { doc: d, updates: [], unsupported: new Set() };
  documents.push(entry);
  d.on("update", (u) => {
    entry.updates.push(hex(u));
    for (const s of Y.decodeUpdate(u).structs) {
      if (s.content?.type && kind(s.content.type) === "xml")
        entry.unsupported.add(
          "XML shared types are not supported by native y-octo editing APIs",
        );
      if (s.content?.doc)
        entry.unsupported.add(
          "subdocuments are not supported by this text/map/array replay interpreter",
        );
    }
  });
};
const results = [];
for (const file of fs
  .readdirSync(path.join(source, "tests"))
  .filter((f) => f.endsWith(".tests.js"))
  .sort()) {
  const module = await import(pathToFileURL(path.join(source, "tests", file)));
  for (const name of Object.keys(module)
    .filter((k) => k.startsWith("test") && typeof module[k] === "function")
    .sort()) {
    documents = [];
    active = true;
    nextId = 1000;
    nextGuid = 0;
    clock = 1700000000000;
    const testName = `${file}:${name}`,
      tc = new testing.TestCase(file, name);
    tc._seed = 42;
    let failure;
    try {
      await module[name](tc);
    } catch (e) {
      failure = e;
    }
    active = false;
    if (failure) {
      results.push({
        name: testName,
        status:
          failure.constructor.name === "SkipError"
            ? "upstream_skip"
            : "generation_failure",
        reason: String(failure.message),
        ...(failure.constructor.name === "SkipError"
          ? {
              upstream_conditions: [
                ...module[name].toString().matchAll(/t\.skip\(([^)]*)\)/g),
              ].map((m) => m[1]),
            }
          : {}),
      });
      continue;
    }
    const unsupported = new Set(documents.flatMap((d) => [...d.unsupported]));
    const rootKinds = new Map();
    for (const { doc } of documents)
      for (const [name, t] of doc.share) {
        const k = kind(t);
        if (k === "subdocument" || (k === "xml" && (t._start || t._map.size)))
          unsupported.add(
            `${k} root is outside the text/map/array replay scope`,
          );
        if (k !== "abstract" && k !== "xml") {
          const kinds = rootKinds.get(name) ?? new Set();
          kinds.add(k);
          rootKinds.set(name, kinds);
        }
      }
    for (const [name, kinds] of rootKinds)
      if (kinds.size > 1)
        unsupported.add(
          `cross-type root projection ${JSON.stringify(name)}: ${[...kinds].sort().join("/")}, outside the declared-type compatibility target`,
        );
    if (unsupported.size) {
      results.push({
        name: testName,
        status: "excluded",
        reasons: [...unsupported].sort(),
      });
      continue;
    }
    try {
      const docs = [];
      // Replaying the recorded event stream also exposes any Yjs native/export
      // discrepancy without treating its old result as the canonical state.
      for (const entry of documents) {
        const roots = {};
        for (const [name, t] of entry.doc.share) {
          let k = kind(t);
          if (k === "xml") continue; // testHelper declares unused empty XML roots.
          if (
            k === "abstract" &&
            !t._start &&
            !t._map.size &&
            !rootKinds.has(name)
          )
            continue;
          if (k === "abstract") {
            const choices = rootKinds.get(name);
            if (!choices || choices.size !== 1)
              throw Error(
                `unresolved root constructor ${JSON.stringify(name)}`,
              );
            k = [...choices][0];
            entry.doc.get(
              name,
              { text: Y.Text, array: Y.Array, map: Y.Map }[k],
            );
          }
          roots[name] = k;
        }
        const receiver = new Y.Doc({ gc: entry.doc.gc });
        receiver.clientID = 900000;
        for (const [name, k] of Object.entries(roots))
          receiver.get(name, { text: Y.Text, array: Y.Array, map: Y.Map }[k]);
        for (const u of entry.updates)
          Y.applyUpdate(receiver, new Uint8Array(Buffer.from(u, "hex")));
        const expected = snapshot(Y, receiver, roots),
          native = snapshot(Y, entry.doc, roots);
        docs.push({
          gc: entry.doc.gc,
          roots,
          text_lengths: Object.fromEntries(
            [...receiver.share]
              .filter(([, t]) => t instanceof Y.Text)
              .map(([name, t]) => [name, t.length]),
          ),
          updates: entry.updates,
          expected,
          ...(JSON.stringify(expected) !== JSON.stringify(native)
            ? {
                native_end: native,
                native_update: hex(Y.encodeStateAsUpdate(entry.doc)),
              }
            : {}),
        });
      }
      results.push({
        name: testName,
        status: docs.some((d) => d.updates.length) ? "recorded" : "no_updates",
        docs,
      });
    } catch (e) {
      results.push({
        name: testName,
        status: "generation_failure",
        reason: String(e.message),
      });
    }
    console.error(`${version} ${testName}: ${results.at(-1).status}`);
  }
}
fs.writeFileSync(output, JSON.stringify(results));
