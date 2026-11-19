// Persistent authored replicas and persistent receivers of Rust commit updates.
import assert from "node:assert/strict";
import readline from "node:readline";
import { isDeepStrictEqual } from "node:util";
const Y = await import(
  process.argv[2] === "13.6.21" ? "yjs-13-6-21" : "yjs-13-6-33"
);
const gc = process.argv[3] === "true";
const clients = [101, 202];
const states = (sv) => [...sv].sort((a, b) => a[0] - b[0]);
const ranges = (ds) =>
  [...ds.clients]
    .sort((a, b) => a[0] - b[0])
    .map(([client, r]) => [client, r.map(({ clock, len }) => [clock, len])]);
// Rust coalesces adjacent text with structurally equal visible attributes.
// Compare that same presentation here, keeping the wire, SV and DS intact.
function visibleDelta(text) {
  const delta = [];
  for (const op of text.toDelta()) {
    const last = delta.at(-1);
    if (
      typeof last?.insert === "string" &&
      typeof op.insert === "string" &&
      isDeepStrictEqual(last.attributes, op.attributes)
    ) {
      last.insert += op.insert;
    } else {
      delta.push(op);
    }
  }
  return delta;
}
function snapshot(d) {
  return {
    text: d.getText("text").toString(),
    delta: visibleDelta(d.getText("text")),
    array: d.getArray("array").toJSON(),
    map: d.getMap("map").toJSON(),
    state_vector: states(Y.decodeStateVector(Y.encodeStateVector(d))),
    delete_set: ranges(Y.decodeUpdate(Y.encodeStateAsUpdate(d)).ds),
  };
}
function create(client) {
  const d = new Y.Doc({ gc });
  d.clientID = client;
  d.getText("text");
  d.getArray("array");
  d.getMap("map");
  return d;
}
let docs = [],
  mirrors = [],
  events = [];
let incoming = new WeakMap();
// Commit events report first-time effective deletions. Rust decodes ContentDeleted as
// already deleted; Yjs also lists newly imported tombstone/GC ranges in its
// transaction DS. Exclude only that incoming, never-visible intersection.
function effectiveDeleted(tx, d) {
  const rows = ranges(tx.deleteSet);
  if (tx.local) return rows;
  const old = incoming.get(d) || [];
  return rows.flatMap(([client, rs]) => {
    let result = rs.map(([start, len]) => [start, start + len]);
    for (const s of old.filter((s) => s.id.client === client)) {
      const start = Math.max(s.id.clock, tx.beforeState.get(client) || 0),
        end = Math.min(s.id.clock + s.length, tx.afterState.get(client) || 0);
      if (start >= end) continue;
      result = result.flatMap(([a, b]) =>
        b <= start || a >= end
          ? [[a, b]]
          : [
              ...(a < start ? [[a, start]] : []),
              ...(b > end ? [[end, b]] : []),
            ],
      );
    }
    return result.length ? [[client, result.map(([a, b]) => [a, b - a])]] : [];
  });
}
function applyWire(d, update) {
  incoming.set(
    d,
    Y.decodeUpdate(update).structs.filter(
      (s) =>
        s.constructor === Y.GC ||
        s.content?.constructor.name === "ContentDeleted",
    ),
  );
  Y.applyUpdate(d, update, "wire");
  incoming.delete(d);
}
function reset() {
  for (const d of [...docs, ...mirrors]) d.destroy();
  docs = clients.map(create);
  mirrors = [303, 404].map(create);
  events = [[], []];
  docs.forEach((d, actor) => {
    const rows = new WeakMap();
    d.on("afterTransaction", (tx) => {
      const before = states(tx.beforeState),
        after = states(tx.afterState),
        deleted = effectiveDeleted(tx, d);
      if (
        JSON.stringify(before) === JSON.stringify(after) &&
        deleted.length === 0
      )
        return;
      const inserted = after.flatMap(([c, end]) => {
        const start = tx.beforeState.get(c) || 0;
        return end > start ? [[c, [[start, end - start]]]] : [];
      });
      const changed = [...tx.changed]
        .filter(
          ([t]) =>
            !t._item ||
            (!t._item.deleted &&
              t._item.id.clock < (tx.beforeState.get(t._item.id.client) || 0)),
        )
        .map(([t]) => [...d.share].find(([, v]) => v === t)?.[0])
        .filter(Boolean)
        .sort();
      const row = {
        local: tx.local,
        before,
        after,
        deleted,
        inserted,
        changed,
      };
      events[actor].push(row);
      rows.set(tx, row);
    });
    d.on("update", (u, _origin, _doc, tx) => {
      const row = rows.get(tx);
      assert(row);
      row.update = Buffer.from(u).toString("hex");
    });
  });
}
reset();
for await (const line of readline.createInterface({ input: process.stdin })) {
  const command = JSON.parse(line);
  if (command.op.kind === "reset") reset();
  else {
    const op = command.op,
      d = docs[op.actor || 0],
      text = d.getText("text");
    switch (op.kind) {
      case "delta":
        text.applyDelta(op.value);
        break;
      case "remove":
        text.delete(op.index, op.length);
        break;
      case "sync": {
        const from = docs[op.from],
          to = docs[op.to];
        const update = Y.encodeStateAsUpdate(from, Y.encodeStateVector(to));
        applyWire(to, update);
        if (op.repeat) applyWire(to, update);
        break;
      }
      default:
        throw Error(op.kind);
    }
  }
  for (let actor = 0; actor < 2; actor++)
    for (const hex of command.rust_updates[actor])
      Y.applyUpdate(mirrors[actor], Buffer.from(hex, "hex"), "wire");
  const response = {
    states: docs.map(snapshot),
    mirrors: mirrors.map(snapshot),
    events,
  };
  process.stdout.write(JSON.stringify(response) + "\n");
  events = [[], []];
}
