// Replaces the former Rust/Yrs comparisons with pinned Yjs-authored material.
import fs from "node:fs";
import { gunzipSync } from "node:zlib";
import { gzipCorpus, gzipBytes } from "./format.mjs";
import assert from "node:assert/strict";
import * as old from "yjs-13-6-21";
import * as current from "yjs-13-6-33";
import * as encoding from "lib0/encoding";
import { fileURLToPath } from "node:url";
const file = fileURLToPath(
  new URL("../../src/fixtures/yjs-legacy.jsonl.gz", import.meta.url),
);
const integerFile = fileURLToPath(
  new URL("../../src/fixtures/yjs-integers.jsonl.gz", import.meta.url),
);
const hex = (b) => Buffer.from(b).toString("hex");
const snapshot = (d) =>
  Object.fromEntries(
    [...d.share]
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([k, v]) => [k, v.toJSON()]),
  );
// Only wire projection uses Yjs internals: observe nested type discriminants
// and item IDs without adding unsupported native Text/XML editing APIs.
function typeShape(Y, value) {
  const id = value?._item
    ? [value._item.id.client, value._item.id.clock]
    : null;
  if (value instanceof Y.Text)
    return {
      kind: value instanceof Y.XmlText ? "xml-text" : "text",
      id,
      delta: value
        .toDelta()
        .map((op) => ({ ...op, insert: typeShape(Y, op.insert) })),
    };
  if (value instanceof Y.Array)
    return {
      kind: "array",
      id,
      value: value.toArray().map((v) => typeShape(Y, v)),
    };
  if (value instanceof Y.Map)
    return {
      kind: "map",
      id,
      value: Object.fromEntries(
        [...value.entries()]
          .sort(([a], [b]) => a.localeCompare(b))
          .map(([k, v]) => [k, typeShape(Y, v)]),
      ),
    };
  return { kind: "any", value };
}
function typeSnapshot(Y, d) {
  return Object.fromEntries(
    [...d.share]
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([key, value]) => [key, typeShape(Y, value)]),
  );
}
function fixtures(Y) {
  const out = {};
  function record(name, roots, edit, client = 101) {
    const d = new Y.Doc({ guid: "legacy-fixture", gc: true });
    d.clientID = client;
    for (const [key, kind] of Object.entries(roots)) d.get(key, Y[kind]);
    const packets = [];
    d.on("update", (update) => packets.push(hex(update)));
    edit(d);
    out[name] = {
      roots,
      update: hex(Y.encodeStateAsUpdate(d)),
      expected: snapshot(d),
    };
    if (name === "text-type-embeds") {
      out[name].packets = packets;
      out[name].structure = typeSnapshot(Y, d);
    }
  }
  record("map", { abc: "Map" }, (d) => d.getMap("abc").set("a", 1));
  record(
    "array-peer",
    { array: "Array" },
    (d) => d.getArray("array").insert(0, ["array_value"]),
    202,
  );
  record("text-split", { abc: "Text" }, (d) => {
    const t = d.getText("abc");
    t.insert(0, " ");
    t.insert(0, "Hello");
    t.insert(6, "World");
    t.insert(11, "!");
  });
  record("text-append", { abc: "Text" }, (d) => {
    const t = d.getText("abc");
    t.insert(0, "Hello");
    t.insert(5, " ");
    t.insert(6, "World");
    t.insert(11, "!");
  });
  record("array-words", { abc: "Array" }, (d) => {
    const a = d.getArray("abc");
    a.insert(0, ["hello"]);
    a.insert(1, ["world"]);
    a.insert(1, [" "]);
  });
  record("marker-array", { abc: "Array" }, (d) => {
    const a = d.getArray("abc");
    a.insert(0, [" "]);
    a.insert(0, ["Hello"]);
    a.insert(2, ["World"]);
  });
  record("text-recovery", { greating: "Text" }, (d) => {
    const t = d.getText("greating");
    t.insert(0, "hello");
    t.insert(5, " world!");
    t.delete(11, 1);
  });
  record("mixed-array", { abc: "Array" }, (d) => {
    const a = d.getArray("abc");
    a.insert(0, [42, -42, true, false, "hello", "world"]);
    const sub = new Y.Array();
    a.insert(6, [sub]);
    sub.insert(0, [1]);
  });
  record("xml", { xml: "XmlFragment", xml_text: "XmlText" }, (d) => {
    const p = new Y.XmlElement("p");
    const t = new Y.XmlText();
    d.getXmlFragment("xml").insert(0, [p]);
    p.setAttribute("id", "paragraph");
    p.insert(0, [t]);
    t.insert(0, "hello");
    t.format(0, 5, { bold: {} });
    const x = d.get("xml_text", Y.XmlText);
    x.insert(0, "world");
    x.delete(0, 1);
  });
  record(
    "text-type-embeds",
    { typed_text: "Text", typed_xml_text: "XmlText" },
    (d) => {
      for (const parent of [
        d.getText("typed_text"),
        d.get("typed_xml_text", Y.XmlText),
      ]) {
        const map = new Y.Map();
        parent.insertEmbed(0, map);
        map.set("key", "map child");
        const array = new Y.Array();
        parent.insertEmbed(1, array);
        array.insert(0, [1, "array child"]);
        const text = new Y.Text();
        parent.insertEmbed(2, text);
        text.insert(0, "text child😀");
        parent.insert(0, "left");
        parent.insert(parent.length, "right");
      }
    },
  );
  return out;
}
function vectors() {
  const values = [
    0,
    1,
    -1,
    63,
    -63,
    64,
    -64,
    127,
    128,
    16383,
    16384,
    2 ** 31 - 1,
    -(2 ** 31),
    2 ** 31,
    -(2 ** 31) - 1,
    Number.MAX_SAFE_INTEGER,
    -Number.MAX_SAFE_INTEGER,
  ];
  let seed = 1729;
  for (let i = 0; i < 128; i++) {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    values.push(seed, -seed);
  }
  return values.map((value) => {
    const e = encoding.createEncoder();
    encoding.writeVarInt(e, value);
    const u = encoding.createEncoder();
    encoding.writeVarUint(u, Math.abs(value));
    return {
      value,
      signed: hex(encoding.toUint8Array(e)),
      unsigned: hex(encoding.toUint8Array(u)),
    };
  });
}
if (process.argv.includes("--verify")) {
  const input = JSON.parse(fs.readFileSync(0, "utf8"));
  const records = gunzipSync(fs.readFileSync(file))
    .toString("utf8")
    .trimEnd()
    .split("\n")
    .slice(1)
    .map((line) => JSON.parse(line));
  const stored = new Map(
    records
      .filter((record) => record.kind === "update")
      .map((record) => [record.name, record]),
  );
  for (const Y of [old, current])
    for (const entry of input) {
      const fixture = stored.get(entry.name);
      const d = new Y.Doc();
      for (const [key, kind] of Object.entries(fixture.roots))
        d.get(key, Y[kind]);
      try {
        Y.applyUpdate(d, Buffer.from(entry.update, "hex"));
      } catch (cause) {
        throw new Error(
          `Rust wire rejected for ${entry.name}: ${entry.update}`,
          { cause },
        );
      }
      assert.deepEqual(snapshot(d), fixture.expected, entry.name);
      if (fixture.structure)
        assert.deepEqual(
          typeSnapshot(Y, d),
          fixture.structure,
          `${entry.name} nested identities`,
        );
      assert.equal(d.store.pendingStructs, null, entry.name);
      assert.equal(d.store.pendingDs, null, entry.name);
    }
  console.log(
    `Verified ${input.length} Rust-authored/re-encoded cases against both Yjs versions`,
  );
} else {
  const updates = fixtures(current);
  assert.deepEqual(
    fixtures(old),
    updates,
    "pinned versions disagree: record explicit expectations",
  );
  const records = [
    ...Object.entries(updates).map(([name, fixture]) => ({
      kind: "update",
      name,
      ...fixture,
    })),
  ];
  const bytes = gzipCorpus({
    authoritative_version: "13.6.33",
    version_differences: [],
    versions: { "13.6.21": records, "13.6.33": records },
  });
  const integerBytes = gzipBytes(
    Buffer.from(
      [
        JSON.stringify({
          schema: 2,
          authoritative_version: "13.6.33",
          versions: ["13.6.21", "13.6.33"],
          columns: ["value", "signed", "unsigned"],
        }),
        ...vectors().map((vector) =>
          JSON.stringify([vector.value, vector.signed, vector.unsigned]),
        ),
      ].join("\n") + "\n",
    ),
  );
  for (const [path, material] of [
    [file, bytes],
    [integerFile, integerBytes],
  ]) {
    if (process.argv.includes("--check"))
      assert.deepEqual(
        fs.readFileSync(path),
        material,
        "legacy Yjs fixture drift",
      );
    else fs.writeFileSync(path, material);
  }
  console.log(
    `legacy: ${Object.keys(updates).length} update scenarios, ${vectors().length} codec vectors`,
  );
}
