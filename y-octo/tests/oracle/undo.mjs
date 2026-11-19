// Scripted UndoManager scenarios. Each scenario is data: a scope and a list of
// steps (edits, syncs, undo/redo/stopCapturing/clear). Yjs runs every script
// under both pinned versions and records the result of every step; Rust
// replays the same script with its own UndoManager (tests/yjs_undo_oracle.rs).
import fs from "node:fs";
import { fileURLToPath } from "node:url";
import { gzipCorpus } from "./format.mjs";
import { doc as sharedDoc, snapshot } from "./snapshot.mjs";
import * as old from "yjs-13-6-21";
import * as current from "yjs-13-6-33";

const CLIENTS = { a: 101, b: 202 };

const doc = (Y, client) => sharedDoc(Y, client, "undo");

// A target is a root name followed by map keys.
function target(d, path) {
  let t =
    path[0] === "text"
      ? d.getText("text")
      : path[0] === "array"
        ? d.getArray("array")
        : d.getMap("map");
  for (const key of path.slice(1)) t = t.get(key);
  return t;
}
function value(Y, v) {
  if (v && typeof v === "object" && "new" in v)
    return v.new === "text"
      ? new Y.Text()
      : v.new === "array"
        ? new Y.Array()
        : new Y.Map();
  return v;
}
function edit(Y, d, e) {
  const t = target(d, e.target);
  switch (e.kind) {
    case "insert":
      // explicit attributes, as applyDelta (and Rust apply_delta) insert:
      // without them Yjs insert would inherit the formatting at the index
      if (t instanceof Y.Text) t.insert(e.index, e.text, e.attrs ?? {});
      else
        t.insert(
          e.index,
          e.values.map((v) => value(Y, v)),
        );
      break;
    case "delete":
      t.delete(e.index, e.len);
      break;
    case "format":
      t.format(e.index, e.len, e.attrs);
      break;
    case "set":
      t.set(e.key, value(Y, e.value));
      break;
    case "remove":
      t.delete(e.key);
      break;
    default:
      throw Error(`unknown edit ${e.kind}`);
  }
}

function run(Y, scenario) {
  const docs = { a: doc(Y, CLIENTS.a), b: doc(Y, CLIENTS.b) };
  // 13.6.21 takes only types as scope; a document scope came later
  if (
    scenario.scope === "doc" &&
    !Y.UndoManager.toString().includes("instanceof Doc")
  )
    return { ...scenario, unsupported: "document scope" };
  const scope =
    scenario.scope === "doc"
      ? docs.a
      : scenario.scope.map((root) => target(docs.a, [root]));
  const um = new Y.UndoManager(scope, {
    // explicit stops define the capture windows, never the wall clock
    captureTimeout: Number.MAX_SAFE_INTEGER,
    ignoreRemoteMapChanges: false,
  });
  const steps = scenario.steps.map((step) => {
    let performed = null;
    switch (step.op) {
      case "tx":
        docs[step.doc].transact(
          () => step.edits.forEach((e) => edit(Y, docs[step.doc], e)),
          step.origin ?? null,
        );
        break;
      case "sync":
        Y.applyUpdate(
          docs[step.to],
          Y.encodeStateAsUpdate(
            docs[step.from],
            Y.encodeStateVector(docs[step.to]),
          ),
          "remote",
        );
        break;
      case "undo":
        performed = um.undo() !== null;
        break;
      case "redo":
        performed = um.redo() !== null;
        break;
      case "stop":
        um.stopCapturing();
        break;
      case "clear":
        um.clear();
        break;
      default:
        throw Error(`unknown step ${step.op}`);
    }
    return {
      performed,
      can_undo: um.canUndo(),
      can_redo: um.canRedo(),
      a: snapshot(Y, docs.a),
      b: snapshot(Y, docs.b),
    };
  });
  um.destroy();
  return { ...scenario, expected: steps };
}

// Step helpers.
const tx = (doc, ...edits) => ({ op: "tx", doc, edits });
const untracked = (doc, ...edits) => ({
  op: "tx",
  doc,
  origin: "untracked",
  edits,
});
const sync = (from, to) => ({ op: "sync", from, to });
const both = [sync("a", "b"), sync("b", "a")];
const undo = { op: "undo" },
  redo = { op: "redo" },
  stop = { op: "stop" },
  clear = { op: "clear" };
const ins = (path, index, text, attrs) => ({
  kind: "insert",
  target: path,
  index,
  text,
  ...(attrs ? { attrs } : {}),
});
const push = (path, index, ...values) => ({
  kind: "insert",
  target: path,
  index,
  values,
});
const del = (path, index, len) => ({
  kind: "delete",
  target: path,
  index,
  len,
});
const fmt = (path, index, len, attrs) => ({
  kind: "format",
  target: path,
  index,
  len,
  attrs,
});
const set = (path, key, value) => ({ kind: "set", target: path, key, value });
const remove = (path, key) => ({ kind: "remove", target: path, key });
const T = ["text"],
  A = ["array"],
  M = ["map"];

const scenarios = [
  {
    name: "text-undo-redo",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "hello")),
      stop,
      tx("a", ins(T, 5, " world")),
      stop,
      tx("a", del(T, 2, 5)),
      undo,
      undo,
      undo,
      undo,
      redo,
      redo,
      redo,
      redo,
      undo,
      sync("a", "b"),
    ],
  },
  {
    name: "text-remote-insert-inside-undone-range",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "abcd")),
      sync("a", "b"),
      stop,
      tx("b", ins(T, 2, "XY")),
      sync("b", "a"),
      undo,
      sync("a", "b"),
      redo,
      sync("a", "b"),
      undo,
      redo,
      ...both,
    ],
  },
  {
    name: "text-deletion-with-remote-edits",
    scope: ["text"],
    steps: [
      untracked("a", ins(T, 0, "hello world")),
      sync("a", "b"),
      tx("a", del(T, 0, 6)),
      sync("a", "b"),
      tx("b", ins(T, 5, "!"), del(T, 0, 1)),
      sync("b", "a"),
      undo,
      ...both,
      redo,
      ...both,
      undo,
      ...both,
    ],
  },
  {
    name: "text-same-window-insert-and-delete",
    scope: ["text"],
    steps: [
      untracked("a", ins(T, 0, "ab")),
      tx("a", ins(T, 1, "xyz"), del(T, 2, 1), del(T, 0, 1)),
      tx("a", ins(T, 0, "q")),
      undo,
      redo,
      undo,
    ],
  },
  {
    name: "text-remote-deletes-undone-insertion",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "abc")),
      stop,
      tx("a", del(T, 1, 1)),
      sync("a", "b"),
      tx("b", del(T, 0, 2)),
      sync("b", "a"),
      undo,
      undo,
      redo,
      redo,
      ...both,
    ],
  },
  {
    name: "text-format-undo-keeps-remote-format",
    scope: ["text"],
    steps: [
      untracked("a", ins(T, 0, "abcdef", { bold: true })),
      sync("a", "b"),
      tx("a", fmt(T, 1, 3, { color: "red" })),
      stop,
      tx("a", fmt(T, 0, 2, { bold: null })),
      tx("b", fmt(T, 2, 4, { italic: true })),
      ...both,
      undo,
      undo,
      redo,
      ...both,
      redo,
      ...both,
    ],
  },
  {
    name: "text-formatted-insert-and-deletion",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "plain "), ins(T, 6, "bold", { bold: true })),
      stop,
      tx("a", del(T, 4, 4)),
      sync("a", "b"),
      tx("b", ins(T, 5, "x", { italic: true })),
      sync("b", "a"),
      undo,
      redo,
      undo,
      undo,
      redo,
      ...both,
    ],
  },
  {
    name: "array-undo-keeps-remote-positions",
    scope: ["array"],
    steps: [
      untracked("a", push(A, 0, 1, 2, 3)),
      sync("a", "b"),
      tx("a", del(A, 1, 1)),
      sync("a", "b"),
      tx("b", push(A, 1, 9)),
      sync("b", "a"),
      undo,
      ...both,
      stop,
      tx("a", push(A, 0, "x"), del(A, 3, 1)),
      undo,
      redo,
      redo,
      ...both,
    ],
  },
  {
    name: "map-undo-chain",
    scope: ["map"],
    steps: [
      tx("a", set(M, "k", 1)),
      stop,
      tx("a", set(M, "k", 2)),
      stop,
      tx("a", set(M, "k", 3)),
      stop,
      tx("a", remove(M, "k")),
      undo,
      undo,
      undo,
      undo,
      redo,
      redo,
      redo,
      redo,
      sync("a", "b"),
    ],
  },
  {
    name: "map-remote-overwrite-is-kept",
    scope: ["map"],
    steps: [
      untracked("a", set(M, "k", 1), set(M, "other", 1)),
      sync("a", "b"),
      tx("a", set(M, "k", 2), set(M, "other", 2)),
      sync("a", "b"),
      tx("b", set(M, "k", "remote")),
      sync("b", "a"),
      undo,
      ...both,
      redo,
      ...both,
    ],
  },
  {
    name: "map-remote-delete-then-undo",
    scope: ["map"],
    steps: [
      untracked("a", set(M, "k", 1)),
      tx("a", set(M, "k", 2)),
      sync("a", "b"),
      tx("b", remove(M, "k")),
      sync("b", "a"),
      undo,
      ...both,
      redo,
      ...both,
    ],
  },
  {
    name: "nested-block-delete-and-restore",
    scope: ["map"],
    steps: [
      untracked("a", set(M, "p", { new: "map" })),
      untracked(
        "a",
        set(["map", "p"], "text", { new: "text" }),
        set(["map", "p"], "type", "paragraph"),
      ),
      untracked("a", ins(["map", "p", "text"], 0, "a😀bc", { bold: true })),
      sync("a", "b"),
      tx(
        "a",
        ins(["map", "p", "text"], 4, "d"),
        set(["map", "p"], "type", "h1"),
      ),
      stop,
      tx("a", remove(M, "p")),
      sync("a", "b"),
      undo,
      sync("a", "b"),
      tx("b", ins(["map", "p", "text"], 0, ">")),
      sync("b", "a"),
      undo,
      redo,
      redo,
      undo,
      ...both,
    ],
  },
  {
    name: "nested-children-edited-and-parent-deleted-together",
    scope: ["map"],
    steps: [
      untracked("a", set(M, "parent", { new: "map" })),
      untracked(
        "a",
        set(["map", "parent"], "text", { new: "text" }),
        set(["map", "parent"], "array", { new: "array" }),
        set(["map", "parent"], "map", { new: "map" }),
      ),
      untracked(
        "a",
        ins(["map", "parent", "text"], 0, "a😀bc", { bold: true }),
        push(["map", "parent", "array"], 0, 1, 2, 3),
        set(["map", "parent", "map"], "key", "value"),
      ),
      tx(
        "a",
        fmt(["map", "parent", "text"], 0, 3, { italic: true }),
        del(["map", "parent", "array"], 1, 1),
        set(["map", "parent", "map"], "key", "changed"),
      ),
      tx("a", remove(M, "parent")),
      undo,
      redo,
      undo,
      sync("a", "b"),
    ],
  },
  {
    name: "nested-map-757",
    scope: ["map"],
    steps: [
      untracked(
        "a",
        set(M, "parent", { new: "map" }),
        set(["map", "parent"], "type", "button"),
        set(["map", "parent"], "test", true),
      ),
      tx("a", set(["map", "parent"], "type", "paragraph")),
      tx("a", remove(M, "parent")),
      undo,
      sync("a", "b"),
      redo,
      undo,
      sync("a", "b"),
    ],
  },
  {
    name: "nested-type-created-in-scope",
    scope: ["array"],
    steps: [
      tx("a", push(A, 0, { new: "text" })),
      tx("a", ins(["array", 0], 0, "abc")),
      stop,
      tx("a", ins(["array", 0], 3, "def")),
      undo,
      undo,
      redo,
      sync("a", "b"),
    ],
  },
  {
    name: "redo-cleared-by-local-edit-not-by-remote",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "ab")),
      undo,
      sync("a", "b"),
      tx("b", ins(T, 0, "remote ")),
      sync("b", "a"),
      redo,
      undo,
      tx("a", ins(T, 0, "x")),
      redo,
      ...both,
    ],
  },
  {
    name: "scope-and-untracked-origins",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "tracked"), push(A, 0, "out of scope")),
      untracked("a", ins(T, 0, "untracked ")),
      stop,
      tx("a", set(M, "k", "out of scope")),
      undo,
      undo,
      redo,
    ],
  },
  {
    name: "document-scope",
    scope: "doc",
    steps: [
      tx("a", ins(T, 0, "abc"), push(A, 0, 1), set(M, "k", 1)),
      stop,
      tx("a", del(T, 0, 1), set(M, "k", 2)),
      undo,
      undo,
      redo,
      sync("a", "b"),
    ],
  },
  {
    name: "clear-forgets-history",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "abc")),
      stop,
      tx("a", del(T, 0, 2)),
      undo,
      clear,
      undo,
      redo,
      tx("a", del(T, 0, 1)),
      undo,
      sync("a", "b"),
    ],
  },
  {
    name: "remote-author-also-edits-undo-scope",
    scope: ["text"],
    steps: [
      tx("a", ins(T, 0, "one ")),
      sync("a", "b"),
      tx("b", ins(T, 4, "two ")),
      sync("b", "a"),
      stop,
      tx("a", ins(T, 8, "three")),
      sync("a", "b"),
      tx("b", del(T, 2, 8)),
      sync("b", "a"),
      undo,
      undo,
      ...both,
      redo,
      redo,
      ...both,
    ],
  },
];

const versions = Object.fromEntries(
  [
    ["13.6.21", old],
    ["13.6.33", current],
  ].map(([v, Y]) => [v, scenarios.map((s) => run(Y, s))]),
);
const differences = versions["13.6.33"]
  .filter(
    (s, i) => JSON.stringify(s) !== JSON.stringify(versions["13.6.21"][i]),
  )
  .map((s) => s.name);
const output = {
  schema: 1,
  authoritative_version: "13.6.33",
  clients: CLIENTS,
  version_differences: differences,
  versions,
};
const path = fileURLToPath(new URL("./undo.jsonl.gz", import.meta.url));
const bytes = gzipCorpus(output);
if (process.argv.includes("--check")) {
  if (!fs.readFileSync(path).equals(bytes))
    throw new Error("undo.jsonl.gz differs");
  console.log("undo.jsonl.gz is byte-for-byte reproducible");
} else fs.writeFileSync(path, bytes);
console.error(
  `undo: ${scenarios.length} scenarios, ${bytes.length} bytes, version differences: ${JSON.stringify(differences)}`,
);
