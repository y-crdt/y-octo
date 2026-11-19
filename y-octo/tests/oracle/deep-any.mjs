// Deeply nested ContentAny written and read by pinned Yjs.
//   node deep-any.mjs --generate <depth>  prints a hex Update V1
//   node deep-any.mjs --verify <depth>    reads a hex Update V1 from stdin
// The map entry root.deep holds <depth> arrays nested around { leaf: 42 }.
import assert from "node:assert/strict";
import fs from "node:fs";
import * as Y from "yjs-13-6-33";

const [mode, arg] = process.argv.slice(2);
const depth = Number(arg);
assert(Number.isInteger(depth) && depth > 0, "depth");

if (mode === "--generate") {
  const doc = new Y.Doc();
  doc.clientID = 7;
  let value = { leaf: 42 };
  for (let i = 0; i < depth; i++) value = [value];
  doc.getMap("root").set("deep", value);
  process.stdout.write(Buffer.from(Y.encodeStateAsUpdate(doc)).toString("hex"));
} else if (mode === "--verify") {
  const update = Buffer.from(fs.readFileSync(0, "utf8").trim(), "hex");
  const doc = new Y.Doc();
  Y.applyUpdate(doc, update);
  let value = doc.getMap("root").get("deep");
  let levels = 0;
  while (Array.isArray(value)) {
    assert.equal(value.length, 1);
    value = value[0];
    levels++;
  }
  assert.deepEqual({ depth: levels, value }, { depth, value: { leaf: 42 } });
  console.log(JSON.stringify({ depth: levels, leaf: value.leaf }));
} else {
  throw new Error(`unknown mode ${mode}`);
}
