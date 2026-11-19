// Rust-authored preliminary subtrees, checked by both pinned Yjs engines.
import assert from "node:assert/strict";
import fs from "node:fs";
import * as old from "yjs-13-6-21";
import * as current from "yjs-13-6-33";
const cases = JSON.parse(fs.readFileSync(0, "utf8"));
const results = [];
for (const [version, Y] of [
  ["13.6.21", old],
  ["13.6.33", current],
]) {
  for (const c of cases) {
    for (const mode of ["full", "incremental"]) {
      const doc = new Y.Doc();
      doc.clientID = 202;
      const root = c.root === "map" ? doc.getMap("map") : doc.getArray("array");
      doc.getText("text");
      const apply = (hex) => Y.applyUpdate(doc, Buffer.from(hex, "hex"));
      if (mode === "full") apply(c.full);
      else {
        // Out-of-order delivery, then duplicate replay must settle completely.
        apply(c.diff);
        apply(c.prefix);
        apply(c.diff);
      }
      assert.equal(doc.store.pendingStructs, null);
      assert.equal(doc.store.pendingDs, null);
      assert.deepEqual(
        root.toJSON(),
        c.expected,
        `${version} ${c.root} ${mode}`,
      );
      assert.equal(doc.getText("text").toString(), "AB");
      assert.deepEqual(
        [...Y.decodeStateVector(Y.encodeStateVector(doc))].sort(
          (a, b) => a[0] - b[0],
        ),
        c.sv,
      );
      const child = root.get(c.child_path[0]);
      const array = child.get("items");
      const text = array.get(0);
      for (const [i, ty] of [child, array, text].entries()) {
        assert.deepEqual([ty._item.id.client, ty._item.id.clock], c.ids[i]);
      }
      const delta = c.delta.map(({ insert, format }) => ({
        insert,
        ...(format ? { attributes: format } : {}),
      }));
      assert.deepEqual(text.toDelta(), delta);
      assert.deepEqual(
        [
          doc.getText("text")._start.id.client,
          doc.getText("text")._start.id.clock,
        ],
        [101, 0],
      );
      results.push({
        version,
        root: c.root,
        mode,
        update: Buffer.from(Y.encodeStateAsUpdate(doc)).toString("hex"),
      });
      doc.destroy();
    }
  }
}
process.stdout.write(JSON.stringify(results));
