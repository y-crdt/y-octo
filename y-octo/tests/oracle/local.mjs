// The reference captures only the renderer transaction. Replay also checks
// dependent peer updates that arrive before it and must wait for integration.
import fs from "node:fs";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { gzipCorpus } from "./format.mjs";
import { doc as sharedDoc, snapshot } from "./snapshot.mjs";
import * as old from "yjs-13-6-21";
import * as current from "yjs-13-6-33";

const doc = (Y, client) => sharedDoc(Y, client, "local");
// wire bytes as lowercase hex, like the other corpora
const bytes = (u) => Buffer.from(u).toString("hex");
const diff = (Y, from, to) =>
  Y.encodeStateAsUpdate(from, Y.encodeStateVector(to));

/// The renderer and remote material, and the renderer after each native step.
function scenario(Y) {
  const native = doc(Y, 101);
  native.getText("text").insert(0, "base");
  const initial = Y.encodeStateAsUpdate(native);

  const renderer = doc(Y, 303);
  Y.applyUpdate(renderer, initial);
  renderer.transact(() => {
    const t = renderer.getText("text");
    t.insert(4, " typed");
    t.format(0, 4, { bold: true });
    t.delete(0, 1);
    const block = new Y.Text();
    renderer.getMap("map").set("block", block);
    block.insert(0, "nested");
  }, "renderer");
  const local = diff(Y, renderer, native);

  // Remote updates carry only their own transaction (a state diff would also
  // carry every deletion the peer knows, the renderer's included).
  const own = (d, edit) => {
    let update;
    const handler = (u) => (update = u);
    d.on("update", handler);
    edit();
    d.off("update", handler);
    return update;
  };
  // a peer that got the renderer's update edits after it
  const peer = doc(Y, 202);
  Y.applyUpdate(peer, initial);
  Y.applyUpdate(peer, local);
  const remote = own(peer, () =>
    peer.getText("text").insert(peer.getText("text").length, "!"),
  );
  // another peer only deletes one of the renderer's characters
  const deleter = doc(Y, 404);
  Y.applyUpdate(deleter, initial);
  Y.applyUpdate(deleter, local);
  const deletion = own(deleter, () => deleter.getText("text").delete(4, 1)); // the space of " typed"

  // expected native history: the renderer transaction alone is captured
  // (authored like the native document, not applied: Yjs would take an
  // update with its own client ID for a remote using it and switch IDs)
  const expected = doc(Y, 101);
  expected.getText("text").insert(0, "base");
  const um = new Y.UndoManager(
    [expected.getText("text"), expected.getMap("map")],
    {
      captureTimeout: Number.MAX_SAFE_INTEGER,
      trackedOrigins: new Set(["renderer"]),
    },
  );
  Y.applyUpdate(expected, local, "renderer");
  Y.applyUpdate(expected, remote, "remote");
  Y.applyUpdate(expected, deletion, "remote");
  const steps = [{ op: "apply", native: snapshot(Y, expected) }];
  // the renderer follows the native document as a remote
  Y.applyUpdate(renderer, diff(Y, expected, renderer), "remote");
  for (const op of ["undo", "redo", "undo"]) {
    const performed = um[op]() !== null;
    const update = diff(Y, expected, renderer);
    Y.applyUpdate(renderer, update, "remote");
    steps.push({
      op,
      performed,
      can_undo: um.canUndo(),
      can_redo: um.canRedo(),
      native: snapshot(Y, expected),
      renderer: snapshot(Y, renderer),
      // after applying the native update the renderer has nothing to send
      echo: Y.decodeUpdate(diff(Y, renderer, expected)).structs.length,
    });
  }
  um.destroy();
  return {
    name: "renderer-local-with-pending-remote",
    initial: bytes(initial),
    local: bytes(local),
    remote: bytes(remote),
    deletion: bytes(deletion),
    steps,
  };
}

const versions = Object.fromEntries(
  [
    ["13.6.21", old],
    ["13.6.33", current],
  ].map(([v, Y]) => [v, [scenario(Y)]]),
);
const differences = versions["13.6.33"]
  .filter(
    (s, i) => JSON.stringify(s) !== JSON.stringify(versions["13.6.21"][i]),
  )
  .map((s) => s.name);

if (process.argv.includes("--verify")) {
  // stdin: {version, updates: [hex]} — the native updates Rust sent after the
  // initial sync, one per step after "apply"
  const input = JSON.parse(fs.readFileSync(0, "utf8"));
  for (const { version, updates } of input) {
    const Y = version === "13.6.21" ? old : current;
    const s = versions[version][0];
    const renderer = doc(Y, 303);
    Y.applyUpdate(renderer, Buffer.from(s.initial, "hex"));
    Y.applyUpdate(renderer, Buffer.from(s.local, "hex"));
    Y.applyUpdate(renderer, Buffer.from(updates[0], "hex"), "remote");
    updates.slice(1).forEach((hex, i) => {
      Y.applyUpdate(renderer, Buffer.from(hex, "hex"), "remote");
      const step = s.steps[i + 1];
      assert.deepEqual(
        {
          text: renderer.getText("text").toDelta(),
          map: renderer.getMap("map").toJSON(),
        },
        { text: step.renderer.delta, map: step.renderer.map },
        `${version} renderer after Rust ${step.op}`,
      );
    });
  }
  console.log("Yjs renderers read the Rust undo/redo updates");
} else {
  const output = {
    schema: 1,
    authoritative_version: "13.6.33",
    version_differences: differences,
    versions,
  };
  const path = fileURLToPath(new URL("./local.jsonl.gz", import.meta.url));
  const gz = gzipCorpus(output);
  if (process.argv.includes("--check")) {
    if (!fs.readFileSync(path).equals(gz))
      throw new Error("local.jsonl.gz differs");
    console.log("local.jsonl.gz is byte-for-byte reproducible");
  } else fs.writeFileSync(path, gz);
  console.error(
    `local: ${gz.length} bytes, version differences: ${JSON.stringify(differences)}`,
  );
}
