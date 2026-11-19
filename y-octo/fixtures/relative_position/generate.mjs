// Generates the Yjs oracle for y-octo's RelativePosition tests.
//
//   cd y-octo/fixtures/relative_position
//   npm install --package-lock=false
//   node generate.mjs
//
// The output (`yjs-13.6.33.json`) is consumed by
// `y-octo/src/doc/relative_position/tests.rs`. Byte strings are hex. Every
// case records:
//   - `create_update`: the document state the positions were created on,
//   - `final_update`: the document state after the case's edits,
//   - `redone`: the local `Item.redone` links of the final document (old id,
//     length, new id), which never travel in updates,
//   - `targets`: the positions grouped by the type they were created on (a
//     group without `target` holds positions built by hand). The binary form
//     leaves out the type when it names an item, so the group records the
//     `type` / `tname` Yjs put in every position it created there. Each
//     position has the bytes of `encodeRelativePosition` (`rpos`) produced by
//     Yjs for (target, index, assoc), and what
//     `createAbsolutePositionFromRelativePosition` returns for them on the
//     final document with `followUndoneDeletions` true (`resolved`) and false
//     (`resolved_no_follow`, left out when it is the same).
// The JSON form follows from the bytes and the group's `type` / `tname`, so
// `relativePositionToJSON` is kept once per shape in the top-level `json`:
// one position for each combination of fields and `assoc`.
import { readFileSync, writeFileSync } from "node:fs";

import * as Y from "yjs";

const YJS_VERSION = "13.6.33";
const installed = JSON.parse(
  readFileSync(
    new URL("./node_modules/yjs/package.json", import.meta.url),
    "utf8",
  ),
).version;
if (installed !== YJS_VERSION) {
  throw new Error(`expected yjs ${YJS_VERSION}, found ${installed}`);
}

const newDoc = (client, gc = true) => {
  const doc = new Y.Doc({ gc });
  doc.clientID = client;
  return doc;
};

const sync = (from, to) =>
  Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));

// target: { root, kind: 'text' | 'array', key? }; with `key` the type is the
// value stored under `key` in the root map `root`.
const getType = (doc, target) => {
  if (target.key !== undefined) {
    return doc.getMap(target.root).get(target.key);
  }
  return target.kind === "array"
    ? doc.getArray(target.root)
    : doc.getText(target.root);
};

const identity = (doc, type) => {
  if (type._item !== null) {
    return {
      item: { client: type._item.id.client, clock: type._item.id.clock },
    };
  }
  for (const [name, value] of doc.share) {
    if (value === type) {
      return { root: name };
    }
  }
  throw new Error("type without identity");
};

const collectRedone = (doc) => {
  const redone = [];
  for (const [, structs] of doc.store.clients) {
    for (const struct of structs) {
      if (struct instanceof Y.Item && struct.redone !== null) {
        redone.push({
          old: { client: struct.id.client, clock: struct.id.clock },
          len: struct.length,
          new: { client: struct.redone.client, clock: struct.redone.clock },
        });
      }
    }
  }
  redone.sort(
    (a, b) => a.old.client - b.old.client || a.old.clock - b.old.clock,
  );
  return redone;
};

const everyIndex = (target, len, assocs = [0, -1]) => {
  const specs = [];
  for (let index = 0; index <= len; index++) {
    for (const assoc of assocs) {
      specs.push({ target, index, assoc });
    }
  }
  return specs;
};

const cases = [];
const jsonShapes = new Map();

const hex = (bytes) => Buffer.from(bytes).toString("hex");

const recordJson = (rpos) => {
  const json = Y.relativePositionToJSON(rpos);
  const shape = JSON.stringify(json, (key, value) =>
    key === "client" || key === "clock" ? 0 : key === "tname" ? "" : value,
  );
  if (!jsonShapes.has(shape)) {
    jsonShapes.set(shape, JSON.stringify(json));
  }
};

// setup() returns { doc, final? }: positions are created on `doc`, resolved on
// `final` (defaults to `doc`) after `mutate`. `raw` positions are built by hand
// instead of from a type index.
const addCase = (
  name,
  { gc = true, note, setup, specs = () => [], raw = [], mutate = () => {} },
) => {
  const ctx = setup(gc);
  const createUpdate = Y.encodeStateAsUpdate(ctx.doc);
  const positions = specs(ctx).map(({ target, index, assoc }) => {
    const rpos = Y.createRelativePositionFromTypeIndex(
      getType(ctx.doc, target),
      index,
      assoc,
    );
    return { target, index, assoc, rpos };
  });
  for (const rpos of raw) {
    positions.push({ rpos });
  }
  mutate(ctx);
  const final = ctx.final ?? ctx.doc;
  const finalUpdate = Y.encodeStateAsUpdate(final);
  const redone = collectRedone(final);
  const resolve = (bytes, follow) => {
    const abs = Y.createAbsolutePositionFromRelativePosition(
      Y.decodeRelativePosition(bytes),
      final,
      follow,
    );
    if (abs === null) {
      return null;
    }
    // Yjs resolves into a deleted (but not collected) type; y-octo returns None there on purpose.
    const deleted = abs.type._item !== null && abs.type._item.deleted;
    return {
      index: abs.index,
      type: identity(final, abs.type),
      ...(deleted ? { type_deleted: true } : {}),
    };
  };
  const groups = [];
  for (const { target, index, assoc, rpos } of positions) {
    const key = target ? JSON.stringify(target) : undefined;
    const { type, tname } = Y.relativePositionToJSON(rpos);
    const identity = target ? { type, tname } : {};
    let group = groups.find((g) => g.key === key);
    if (group === undefined) {
      group = { key, target, identity, positions: [] };
      groups.push(group);
    }
    if (JSON.stringify(group.identity) !== JSON.stringify(identity)) {
      throw new Error(`${name}: positions of one target name different types`);
    }
    const bytes = Y.encodeRelativePosition(rpos);
    recordJson(rpos);
    const resolved = resolve(bytes, true);
    const resolvedNoFollow = resolve(bytes, false);
    group.positions.push({
      ...(target ? { index, assoc } : {}),
      rpos: hex(bytes),
      resolved,
      ...(JSON.stringify(resolvedNoFollow) !== JSON.stringify(resolved)
        ? { resolved_no_follow: resolvedNoFollow }
        : {}),
    });
  }
  cases.push({
    name,
    gc,
    ...(note ? { note } : {}),
    create_update: hex(createUpdate),
    final_update: hex(finalUpdate),
    redone,
    targets: groups.map(({ target, identity, positions }) => ({
      ...(target ? { target } : {}),
      ...identity,
      positions,
    })),
  });
};

const T = { root: "t", kind: "text" };
const A = { root: "a", kind: "array" };

addCase("text_edges", {
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getText("t").insert(0, "hello world");
    // a root that only has deleted content: it is in the update, unlike a
    // root nothing was ever written to
    doc.getText("empty").insert(0, "x");
    doc.getText("empty").delete(0, 1);
    return { doc };
  },
  specs: () => [
    ...everyIndex(T, 11),
    { target: T, index: 0, assoc: 5 },
    { target: T, index: 4, assoc: -3 },
    { target: T, index: 11, assoc: 7 },
    ...everyIndex({ root: "empty", kind: "text" }, 0),
  ],
});

addCase("text_insert_both_sides", {
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getText("t").insert(0, "abcd");
    const other = newDoc(2, gc);
    sync(doc, other);
    return { doc, other };
  },
  specs: () => everyIndex(T, 4),
  mutate: ({ doc, other }) => {
    const t = other.getText("t");
    t.insert(2, "XY");
    t.insert(0, "S");
    t.insert(t.length, "E");
    sync(other, doc);
  },
});

addCase("text_interleaved_clients", {
  setup: (gc) => {
    const a = newDoc(1, gc);
    const b = newDoc(2, gc);
    a.getText("t").insert(0, "one two three");
    sync(a, b);
    b.getText("t").insert(4, "BB ");
    a.getText("t").insert(8, "AA ");
    sync(a, b);
    sync(b, a);
    a.getText("t").delete(1, 2);
    b.getText("t").insert(b.getText("t").length, " tail");
    sync(a, b);
    sync(b, a);
    return { doc: a, other: b };
  },
  specs: ({ doc }) => everyIndex(T, doc.getText("t").length),
  mutate: ({ doc, other }) => {
    other.getText("t").insert(3, "__");
    other.getText("t").delete(10, 4);
    doc.getText("t").insert(0, ">");
    sync(other, doc);
  },
});

addCase("text_target_deleted", {
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getText("t").insert(0, "abcdefgh");
    const other = newDoc(2, gc);
    sync(doc, other);
    return { doc, other };
  },
  specs: () => everyIndex(T, 8),
  mutate: ({ doc, other }) => {
    doc.getText("t").delete(2, 3);
    other.getText("t").delete(6, 1);
    sync(other, doc);
  },
});

addCase("text_remote_split", {
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getText("t").insert(0, "hello world");
    const other = newDoc(2, gc);
    sync(doc, other);
    return { doc, other };
  },
  specs: () => everyIndex(T, 11),
  mutate: ({ doc, other }) => {
    other.getText("t").insert(5, "XYZ");
    other.getText("t").insert(2, "Q");
    sync(other, doc);
  },
});

addCase("text_merged_items", {
  note: "one character per transaction; Yjs merges the items at transaction cleanup",
  setup: (gc) => {
    const doc = newDoc(1, gc);
    for (const ch of "abcdef") {
      doc.getText("t").insert(doc.getText("t").length, ch);
    }
    return { doc };
  },
  specs: () => everyIndex(T, 6),
  mutate: ({ doc }) => {
    doc.getText("t").insert(3, "|");
  },
});

const UNICODE = "a😀b👨‍👩‍👧cé שלום עולם 🇨🇳!";
addCase("text_unicode", {
  note: "emoji, ZWJ family, combining acute, RTL Hebrew and a flag; indices are UTF-16 code units",
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getText("t").insert(0, UNICODE);
    const other = newDoc(2, gc);
    sync(doc, other);
    return { doc, other };
  },
  specs: () => everyIndex(T, UNICODE.length),
  mutate: ({ doc, other }) => {
    // after 'a😀' (3 UTF-16 units)
    other.getText("t").insert(3, "🎉");
    // the ZWJ family starts after 'a😀b' (4 units) and is 8 units long
    doc.getText("t").delete(4, 8);
    sync(other, doc);
  },
});

addCase("text_format_items", {
  note: "format items do not occupy positions",
  setup: (gc) => {
    const doc = newDoc(1, gc);
    const t = doc.getText("t");
    t.insert(0, "hello world");
    t.format(2, 5, { bold: true });
    t.insert(3, "Z", { italic: true });
    const other = newDoc(2, gc);
    sync(doc, other);
    return { doc, other };
  },
  specs: ({ doc }) => everyIndex(T, doc.getText("t").length),
  mutate: ({ doc, other }) => {
    other.getText("t").format(0, 4, { underline: true });
    other.getText("t").insert(1, "Q");
    sync(other, doc);
  },
});

addCase("nested_map_text", {
  setup: (gc) => {
    const doc = newDoc(1, gc);
    const m = doc.getMap("m");
    m.set("k", new Y.Text("nested"));
    m.set("arr", Y.Array.from([1, 2]));
    const other = newDoc(2, gc);
    sync(doc, other);
    return { doc, other };
  },
  specs: () => [
    ...everyIndex({ root: "m", key: "k", kind: "text" }, 6),
    ...everyIndex({ root: "m", key: "arr", kind: "array" }, 2),
  ],
  mutate: ({ doc, other }) => {
    other.getMap("m").get("k").insert(0, "very ");
    other.getMap("m").get("arr").insert(1, ["x"]);
    doc.getMap("m").get("k").insert(6, "!");
    sync(other, doc);
  },
});

addCase("array_values", {
  setup: (gc) => {
    const doc = newDoc(1, gc);
    const a = doc.getArray("a");
    a.push([1, 2, 3]);
    a.insert(1, ["x", "y"]);
    a.push([{ obj: true }, new Uint8Array([1, 2])]);
    a.push([new Y.Text("inner")]);
    const other = newDoc(2, gc);
    sync(doc, other);
    return { doc, other };
  },
  specs: ({ doc }) => everyIndex(A, doc.getArray("a").length),
  mutate: ({ doc, other }) => {
    other.getArray("a").insert(2, ["r"]);
    doc.getArray("a").delete(0, 1);
    doc.getArray("a").delete(3, 1);
    sync(other, doc);
  },
});

const parentDeleted = (gc) => ({
  gc,
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getMap("m").set("k", new Y.Text("abc"));
    return { doc };
  },
  specs: () => everyIndex({ root: "m", key: "k", kind: "text" }, 3),
  mutate: ({ doc }) => {
    doc.getMap("m").delete("k");
  },
});

addCase("parent_deleted_gc", {
  note: "the parent text is deleted and garbage collected: Yjs returns null for every position",
  ...parentDeleted(true),
});

addCase("parent_deleted_no_gc", {
  note: "the parent text is deleted but kept (gc: false): Yjs returns index 0, y-octo returns None on purpose",
  ...parentDeleted(false),
});

addCase("pending_structs", {
  note: "positions point to structs the final document has not received",
  setup: (gc) => {
    const final = newDoc(1, gc);
    final.getText("t").insert(0, "abc");
    const doc = newDoc(2, gc);
    sync(final, doc);
    doc.getText("t").insert(1, "XYZ");
    doc.getMap("m").set("k", new Y.Text("new"));
    return { doc, final };
  },
  specs: () => [
    ...everyIndex(T, 6),
    ...everyIndex({ root: "m", key: "k", kind: "text" }, 3),
  ],
});

addCase("missing_root", {
  note: "Yjs creates the missing root type and resolves into it; y-octo returns None on purpose",
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getText("t").insert(0, "abc");
    return { doc };
  },
  raw: [
    new Y.RelativePosition(null, "nope", null, 0),
    new Y.RelativePosition(null, "nope", null, -1),
  ],
});

addCase("assoc_extremes", {
  note: "assoc beyond 32 bits keeps its sign; up to Number.MAX_SAFE_INTEGER round trips",
  setup: (gc) => {
    const doc = newDoc(1, gc);
    doc.getText("t").insert(0, "ab");
    return { doc };
  },
  raw: [
    2 ** 31,
    -(2 ** 31) - 1,
    2 ** 32,
    -(2 ** 40),
    Number.MAX_SAFE_INTEGER,
    -Number.MAX_SAFE_INTEGER,
  ].flatMap((assoc) => [
    new Y.RelativePosition(null, null, Y.createID(1, 0), assoc),
    new Y.RelativePosition(null, "t", null, assoc),
  ]),
});

const tracked = (gc, text) => {
  const doc = newDoc(1, gc);
  const t = doc.getText("t");
  const um = new Y.UndoManager(t, { captureTimeout: 0 });
  t.insert(0, text);
  um.stopCapturing();
  return { doc, um };
};

addCase("redo_once", {
  setup: (gc) => {
    const ctx = tracked(gc, "hello");
    ctx.doc.getText("t").insert(5, " world");
    ctx.um.stopCapturing();
    return ctx;
  },
  specs: () => everyIndex(T, 11),
  mutate: ({ um }) => {
    um.undo();
    um.redo();
  },
});

addCase("redo_chain", {
  note: "undo/redo twice: old -> new -> newer",
  setup: (gc) => tracked(gc, "abcdef"),
  specs: () => everyIndex(T, 6),
  mutate: ({ doc, um }) => {
    um.undo();
    um.redo();
    um.undo();
    um.redo();
    doc.getText("t").insert(0, ">");
  },
});

addCase("redo_split_old_and_new", {
  note: "a remote peer splits the original (deleted) item and the redone copy",
  setup: (gc) => {
    const ctx = tracked(gc, "abcdef");
    ctx.other = newDoc(2, gc);
    sync(ctx.doc, ctx.other);
    return ctx;
  },
  specs: () => everyIndex(T, 6),
  mutate: ({ doc, um, other }) => {
    um.undo();
    um.redo();
    // `other` has not seen the undo: inserting at 3 splits the original item
    other.getText("t").insert(3, "X");
    sync(other, doc);
    sync(doc, other);
    // now `other` sees the redone copy: inserting inside it splits the copy
    const t = other.getText("t");
    const s = t.toString();
    t.insert(s.indexOf("e"), "Y");
    sync(other, doc);
  },
});

addCase("redo_nested_type", {
  note: "undoing a map key deletion recreates the nested text and its characters under new ids",
  setup: (gc) => {
    const doc = newDoc(1, gc);
    const m = doc.getMap("m");
    m.set("k", new Y.Text("abc"));
    const um = new Y.UndoManager(m, { captureTimeout: 0 });
    return { doc, um };
  },
  specs: () => everyIndex({ root: "m", key: "k", kind: "text" }, 3),
  mutate: ({ doc, um }) => {
    doc.getMap("m").delete("k");
    um.stopCapturing();
    um.undo();
  },
});

writeFileSync(
  new URL(`./yjs-${YJS_VERSION}.json`, import.meta.url),
  JSON.stringify({ yjs: YJS_VERSION, json: [...jsonShapes.values()], cases }) +
    "\n",
);
console.log(`wrote ${cases.length} cases`);
