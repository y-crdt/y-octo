import fs from "node:fs";
import { fileURLToPath } from "node:url";
import { gzipCorpus } from "./format.mjs";
import * as old from "yjs-13-6-21";
import * as current from "yjs-13-6-33";

function doc(Y, id, gc = true) {
  const d = new Y.Doc({ guid: `concurrent-${id}`, gc });
  d.clientID = id;
  d.getText("text");
  d.getArray("array");
  d.getMap("map");
  return d;
}
function id(value) {
  return value ? [value.client, value.clock] : null;
}
function shape(Y, t) {
  if (t instanceof Y.Text) {
    const visible_identities = [];
    for (let item = t._start; item; item = item.right) {
      if (
        !item.deleted &&
        item.countable &&
        typeof item.content.str === "string"
      ) {
        for (let offset = 0; offset < item.content.str.length; offset++)
          visible_identities.push([
            item.id.client,
            item.id.clock + offset,
            item.content.str.charCodeAt(offset),
          ]);
      }
    }
    return {
      kind: "text",
      id: id(t._item?.id),
      value: t.toString(),
      delta: t.toDelta(),
      visible_identities,
    };
  }
  if (t instanceof Y.Array)
    return {
      kind: "array",
      id: id(t._item?.id),
      value: t.toArray().map((v) => shape(Y, v)),
    };
  if (t instanceof Y.Map)
    return {
      kind: "map",
      id: id(t._item?.id),
      value: Object.fromEntries(
        [...t]
          .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
          .map(([k, v]) => [k, shape(Y, v)]),
      ),
    };
  return { kind: "any", value: t };
}
function snapshot(Y, d) {
  const full = Y.encodeStateAsUpdate(d);
  return {
    text: d.getText("text").toString(),
    delta: d.getText("text").toDelta(),
    array: d.getArray("array").toJSON(),
    map: d.getMap("map").toJSON(),
    state_vector: [...Y.decodeStateVector(Y.encodeStateVector(d))].sort(
      (a, b) => a[0] - b[0],
    ),
    delete_set: [...Y.decodeUpdate(full).ds.clients]
      .sort((a, b) => a[0] - b[0])
      .map(([c, rs]) => [c, rs.map((r) => [r.clock, r.len])]),
    structure: {
      text: shape(Y, d.getText("text")),
      array: shape(Y, d.getArray("array")),
      map: shape(Y, d.getMap("map")),
    },
  };
}
function recorder(Y, name, gc = true) {
  const a = doc(Y, 101, gc),
    b = doc(Y, 202, gc),
    updates = [],
    actions = [];
  const emit = (label, d, fn, batch = true) => {
    const captured = [];
    const handler = (u) => captured.push([...u]);
    d.on("update", handler);
    if (batch) d.transact(fn);
    else fn();
    d.off("update", handler);
    const indices = captured.map((u) => {
      updates.push(u);
      return updates.length - 1;
    });
    actions.push({
      label,
      author: d.clientID,
      updates: indices,
      expected_author: snapshot(Y, d),
    });
    return indices;
  };
  const deliver = (d, indices) =>
    indices.forEach((i) =>
      Y.applyUpdate(d, new Uint8Array(updates[i]), "remote"),
    );
  const plan = (label, order) => {
    const d = doc(Y, 303, gc),
      steps = [];
    for (const i of order) {
      Y.applyUpdate(d, new Uint8Array(updates[i]));
      steps.push({
        update: i,
        pending: !!(d.store.pendingStructs || d.store.pendingDs),
        expected: snapshot(Y, d),
      });
    }
    return { label, steps };
  };
  return { a, b, updates, actions, emit, deliver, plan, name, gc };
}
function permutations(xs) {
  if (!xs.length) return [[]];
  return xs.flatMap((x, i) =>
    permutations(xs.filter((_, j) => j !== i)).map((p) => [x, ...p]),
  );
}
function concurrent(Y) {
  const r = recorder(Y, "concurrent-text-overlap"),
    { a, b, emit, deliver } = r;
  const initial = emit("A inserts xy", a, () =>
    a.getText("text").insert(0, "xy"),
  );
  deliver(b, initial);
  const middle = emit("B inserts in the middle", b, () =>
    b.getText("text").insert(1, "内"),
  );
  deliver(a, middle);
  const da = emit("A deletes overlapping left range", a, () =>
    a.getText("text").delete(0, 2),
  );
  const db = emit("B deletes overlapping right range", b, () =>
    b.getText("text").delete(1, 2),
  );
  deliver(a, db);
  deliver(b, da);
  return {
    ...r,
    plans: permutations([0, 1, 2, 3]).map((p, i) =>
      r.plan(`permutation-${i}`, p.concat(p)),
    ),
    final_author: snapshot(Y, a),
  };
}
function formats(Y, same) {
  const r = recorder(
      Y,
      same ? "concurrent-format-same-key" : "concurrent-format-different-keys",
    ),
    { a, b, emit, deliver } = r;
  deliver(
    b,
    emit("initial formatted text", a, () =>
      a.getText("text").insert(0, "a😀bc", { bold: true }),
    ),
  );
  const ua = emit("A formats range", a, () =>
    a.getText("text").format(1, 3, { color: "red" }),
  );
  const ub = emit("B formats overlapping range", b, () =>
    b.getText("text").format(0, 4, same ? { color: "blue" } : { italic: true }),
  );
  deliver(a, ub);
  deliver(b, ua);
  // Applying remote formatted updates can emit separate cleanup transactions.
  // Full author state below remains an additional semantic convergence oracle.
  return {
    ...r,
    plans: [
      [0, 1, 2],
      [0, 2, 1],
      [2, 1, 0, 2, 1],
    ].map((p, i) => r.plan(`arrival-${i}`, p)),
    final_author: snapshot(Y, a),
  };
}
function nested(Y) {
  const r = recorder(Y, "nested-create-delete-parent"),
    { a, b, emit, deliver } = r;
  const init = emit("create distinct nested text array and map", a, () => {
    const parent = new Y.Map();
    a.getMap("map").set("parent", parent);
    const t = new Y.Text();
    parent.set("text", t);
    t.insert(0, "nested😀");
    const ar = new Y.Array();
    parent.set("array", ar);
    ar.insert(0, [1, { opaque: true }, ["x"]]);
    const m = new Y.Map();
    parent.set("map", m);
    m.set("key", "value");
    const sibling = new Y.Map();
    a.getArray("array").insert(0, [sibling]);
    sibling.set("key", "sibling");
  });
  deliver(b, init);
  const change = emit("remote modifies nested children", b, () => {
    const p = b.getMap("map").get("parent");
    p.get("text").insert(0, "B");
    p.get("array").delete(1, 1);
    p.get("map").set("key", "remote");
  });
  deliver(a, change);
  emit("delete parent and all three children", a, () =>
    a.getMap("map").delete("parent"),
  );
  return {
    ...r,
    plans: [
      [0, 1, 2],
      [2, 1, 0, 1, 2],
      [1, 0, 2, 0],
    ].map((p, i) => r.plan(`arrival-${i}`, p)),
  };
}
function undoText(Y) {
  const r = recorder(Y, "undo-concurrent-text"),
    { a, b, emit, deliver } = r;
  // Explicit stopCapturing calls define boundaries; a very large timeout keeps
  // a capture window deterministic even on a heavily loaded build machine.
  const um = new Y.UndoManager(a.getText("text"), {
    captureTimeout: Number.MAX_SAFE_INTEGER,
    ignoreRemoteMapChanges: false,
  });
  deliver(
    b,
    emit("A inserts xy", a, () => a.getText("text").insert(0, "xy")),
  );
  um.stopCapturing();
  deliver(
    a,
    emit("B inserts middle", b, () => b.getText("text").insert(1, "内")),
  );
  emit("A undo preserves B", a, () => um.undo(), false);
  emit("A redo", a, () => um.redo(), false);
  emit("A undo again follows redone IDs", a, () => um.undo(), false);
  emit("A redo again", a, () => um.redo(), false);
  um.stopCapturing();
  emit("local overlapping deletion", a, () => a.getText("text").delete(0, 2));
  emit("undo deletion", a, () => um.undo(), false);
  emit("redo deletion", a, () => um.redo(), false);
  um.destroy();
  return {
    ...r,
    plans: [
      r.plan(
        "incremental",
        r.updates.map((_, i) => i),
      ),
      r.plan(
        "reverse-then-repeat",
        r.updates
          .map((_, i) => i)
          .reverse()
          .concat(r.updates.map((_, i) => i)),
      ),
    ],
  };
}
function undo757(Y) {
  const r = recorder(Y, "undo-nested-map-757"),
    { a, emit } = r;
  emit("initial parent and child attributes", a, () => {
    const child = new Y.Map();
    a.getMap("map").set("parent", child);
    child.set("type", "button");
    child.set("test", true);
  });
  const um = new Y.UndoManager(a.getMap("map"), {
    captureTimeout: Number.MAX_SAFE_INTEGER,
    ignoreRemoteMapChanges: false,
  });
  um.stopCapturing();
  emit("change nested attribute in capture window", a, () =>
    a.getMap("map").get("parent").set("type", "paragraph"),
  );
  emit("delete parent in same capture window", a, () =>
    a.getMap("map").delete("parent"),
  );
  emit(
    "undo attribute and parent deletion together",
    a,
    () => um.undo(),
    false,
  );
  const firstUndoUpdate = Y.encodeStateAsUpdate(a);
  const firstUndoRemote = doc(Y, 404);
  Y.applyUpdate(firstUndoRemote, firstUndoUpdate);
  const bug_checkpoint = {
    update: [...firstUndoUpdate],
    author: snapshot(Y, a),
    remote: snapshot(Y, firstUndoRemote),
  };
  emit("redo attribute and parent deletion", a, () => um.redo(), false);
  emit("undo again", a, () => um.undo(), false);
  um.destroy();
  const plans = [
    r.plan(
      "incremental",
      r.updates.map((_, i) => i),
    ),
  ];
  // The original #757 failure is a local/encoded-remote discrepancy. Record
  // both sides explicitly; old wire output must never stand in for the author.
  const full = Y.encodeStateAsUpdate(a),
    fresh = doc(Y, 404);
  Y.applyUpdate(fresh, full);
  return {
    ...r,
    plans,
    bug_checkpoint,
    final_update: [...full],
    final_author: snapshot(Y, a),
    final_remote: snapshot(Y, fresh),
  };
}
function positions(Y, gc = true) {
  const r = recorder(
      Y,
      gc ? "relative-positions" : "relative-positions-retained-parent",
      gc,
    ),
    { a, emit } = r;
  const positions = [];
  emit("create root and nested text", a, () => {
    a.getText("text").insert(0, "a😀z");
    const t = new Y.Text();
    a.getMap("map").set("nested", t);
    t.insert(0, "n😀t");
  });
  for (const [target, t] of [
    ["root", a.getText("text")],
    ["nested", a.getMap("map").get("nested")],
  ]) {
    for (const index of [0, 1, 2, 3, 4])
      for (const assoc of [-1, 0, 1]) {
        const rel = Y.createRelativePositionFromTypeIndex(t, index, assoc);
        const binary = Y.encodeRelativePosition(rel);
        const decoded = Y.decodeRelativePosition(binary);
        if (String(binary) !== String(Y.encodeRelativePosition(decoded)))
          throw new Error("RelativePosition binary round trip changed bytes");
        const before = Y.createAbsolutePositionFromRelativePosition(rel, a);
        const after = Y.createAbsolutePositionFromRelativePosition(decoded, a);
        if (
          before.type !== after.type ||
          before.index !== after.index ||
          before.assoc !== after.assoc
        )
          throw new Error(
            "RelativePosition binary round trip changed resolution",
          );
        positions.push({
          name: `${target}-${index}-${assoc}`,
          target,
          index,
          assoc,
          json: Y.relativePositionToJSON(rel),
          binary: [...binary],
        });
      }
  }
  emit("insert at emoji boundary", a, () => a.getText("text").insert(1, "X"));
  emit("delete anchor targets", a, () => a.getText("text").delete(2, 2));
  emit("delete nested parent", a, () => a.getMap("map").delete("nested"));
  const index = (d, p) => {
    const abs = Y.createAbsolutePositionFromRelativePosition(
      Y.decodeRelativePosition(new Uint8Array(p.binary)),
      d,
    );
    if (!abs) return null;
    return {
      type: abs.type._item
        ? { item: id(abs.type._item.id) }
        : { root: [...d.share].find(([, t]) => t === abs.type)[0] },
      index: abs.index,
      assoc: abs.assoc,
      parent_deleted: !!abs.type._item?.deleted,
    };
  };
  const orders = [
    [0, 1, 2, 3],
    [1, 2, 3, 0, 3],
    [3, 2, 1, 0, 1, 2, 3],
  ];
  const plans = orders.map((order, i) => {
    const d = doc(Y, 303, gc);
    const steps = [
      {
        update: null,
        expected: snapshot(Y, d),
        positions: positions.map((p) => index(d, p)),
      },
    ];
    for (const u of order) {
      Y.applyUpdate(d, new Uint8Array(r.updates[u]));
      steps.push({
        update: u,
        expected: snapshot(Y, d),
        positions: positions.map((p) => index(d, p)),
      });
    }
    return { label: `arrival-${i}`, steps };
  });
  return { ...r, positions, plans };
}
function undoFormat(Y, same) {
  const r = recorder(
      Y,
      same ? "undo-format-same-key" : "undo-format-different-keys",
    ),
    { a, b, emit, deliver } = r;
  deliver(
    b,
    emit("initial rich text", a, () =>
      a.getText("text").insert(0, "a😀bc", { bold: true }),
    ),
  );
  const um = new Y.UndoManager(a.getText("text"), {
    captureTimeout: Number.MAX_SAFE_INTEGER,
    ignoreRemoteMapChanges: false,
  });
  emit("local formatting", a, () =>
    a.getText("text").format(1, 3, { color: "red" }),
  );
  deliver(
    a,
    emit("remote overlapping formatting", b, () =>
      b
        .getText("text")
        .format(0, 4, same ? { color: "blue" } : { italic: true }),
    ),
  );
  emit("undo local formatting preserves remote", a, () => um.undo(), false);
  emit("redo local formatting", a, () => um.redo(), false);
  um.destroy();
  return {
    ...r,
    plans: [
      r.plan(
        "incremental",
        r.updates.map((_, i) => i),
      ),
      r.plan(
        "reverse-repeat",
        r.updates
          .map((_, i) => i)
          .reverse()
          .concat(r.updates.map((_, i) => i)),
      ),
    ],
  };
}
function undoNested(Y) {
  const r = recorder(Y, "undo-nested-children"),
    { a, emit } = r;
  emit("initial nested text array map", a, () => {
    const parent = new Y.Map();
    a.getMap("map").set("parent", parent);
    const t = new Y.Text();
    parent.set("text", t);
    t.insert(0, "a😀bc", { bold: true });
    const ar = new Y.Array();
    parent.set("array", ar);
    ar.insert(0, [1, 2, 3]);
    const m = new Y.Map();
    parent.set("map", m);
    m.set("key", "value");
  });
  const um = new Y.UndoManager(a.getMap("map"), {
    captureTimeout: Number.MAX_SAFE_INTEGER,
    ignoreRemoteMapChanges: false,
  });
  emit("edit all nested children", a, () => {
    const p = a.getMap("map").get("parent");
    p.get("text").format(0, 3, { italic: true });
    p.get("array").delete(1, 1);
    p.get("map").set("key", "changed");
  });
  emit("delete parent in same capture window", a, () =>
    a.getMap("map").delete("parent"),
  );
  emit("undo restores all nested children", a, () => um.undo(), false);
  emit("redo nested edits and deletion", a, () => um.redo(), false);
  um.destroy();
  return {
    ...r,
    plans: [
      r.plan(
        "incremental",
        r.updates.map((_, i) => i),
      ),
      r.plan(
        "reverse-repeat",
        r.updates
          .map((_, i) => i)
          .reverse()
          .concat(r.updates.map((_, i) => i)),
      ),
    ],
  };
}
function clean(r) {
  return Object.fromEntries(
    Object.entries(r).filter(
      ([k]) => !["a", "b", "emit", "deliver", "plan"].includes(k),
    ),
  );
}
const versions = Object.fromEntries(
  [
    ["13.6.21", old],
    ["13.6.33", current],
  ].map(([v, Y]) => [
    v,
    [
      concurrent(Y),
      formats(Y, true),
      formats(Y, false),
      nested(Y),
      undoText(Y),
      undo757(Y),
      positions(Y),
      positions(Y, false),
      undoFormat(Y, true),
      undoFormat(Y, false),
      undoNested(Y),
    ].map(clean),
  ]),
);
const differences = versions["13.6.33"]
  .filter(
    (s, i) => JSON.stringify(s) !== JSON.stringify(versions["13.6.21"][i]),
  )
  .map((s) => s.name);
if (!differences.includes("undo-nested-map-757"))
  throw new Error("Missing expected #757 version difference");
const output = {
  schema: 1,
  authoritative_version: "13.6.33",
  version_differences: differences,
  versions,
};
const path = fileURLToPath(new URL("./concurrent.jsonl.gz", import.meta.url));
const bytes = gzipCorpus(output);
if (process.argv.includes("--check")) {
  if (!fs.readFileSync(path).equals(bytes))
    throw new Error("concurrent.jsonl.gz differs");
  console.log("concurrent.jsonl.gz is byte-for-byte reproducible");
} else fs.writeFileSync(path, bytes);
