// Storage oracle only: decode raw material before any Doc integration or GC.
import assert from "node:assert/strict";
import { value, snapshot } from "./projection.mjs";

const hex = (bytes) => Buffer.from(bytes).toString("hex");
const id = (v) => (v ? [v.client, v.clock] : null);
const key = (v) => v?.join(":");

export function wireState(Y, update) {
  const decoded = Y.decodeUpdate(update),
    atoms = new Map();
  for (const s of decoded.structs) {
    const kind = s.constructor.name;
    for (let offset = 0; offset < s.length; offset++) {
      const item = { id: [s.id.client, s.id.clock + offset], kind };
      assert(!atoms.has(key(item.id)), "overlapping struct clocks");
      if (s instanceof Y.Item) {
        item.origin = offset
          ? [s.id.client, s.id.clock + offset - 1]
          : id(s.origin);
        item.right_origin = id(s.rightOrigin);
        item.parent =
          typeof s.parent === "string"
            ? { root: s.parent }
            : s.parent
              ? { item: id(s.parent) }
              : null;
        item.parent_sub = s.parentSub;
        const c = s.content,
          ref = c.getRef();
        let payload;
        switch (ref) {
          case 1:
            payload = null;
            break; // deleted content, clock length retained
          case 4:
            payload = c.str.charCodeAt(offset);
            break; // UTF-16 clocks
          case 6:
            payload = [c.key, value(c.value)];
            break;
          case 7:
            payload = { type: c.type.constructor.name };
            if (c.type.nodeName !== undefined)
              payload.node_name = c.type.nodeName;
            if (c.type.hookName !== undefined)
              payload.hook_name = c.type.hookName;
            break;
          case 9:
            payload = { guid: c.doc.guid, opts: value(c.opts) };
            break;
          default:
            payload = value(c.getContent()[offset]);
        }
        item.content = [ref, payload];
      }
      atoms.set(key(item.id), item);
    }
  }
  // A split tail inherits its parent's identity/key through an origin. Resolve
  // that spelling without integrating (unavailable origins stay explicit).
  const parents = new Map();
  function parent(item) {
    if (parents.has(key(item.id))) return parents.get(key(item.id));
    let result;
    if (item.parent) result = [item.parent, item.parent_sub];
    else {
      const neighbor =
        atoms.get(key(item.origin)) ?? atoms.get(key(item.right_origin));
      result =
        neighbor?.kind === "Item"
          ? parent(neighbor)
          : [{ external: [item.origin, item.right_origin] }, null];
    }
    parents.set(key(item.id), result);
    return result;
  }
  const structs = [...atoms.values()].sort(
    (a, b) => a.id[0] - b.id[0] || a.id[1] - b.id[1],
  );
  for (const item of structs)
    if (item.kind === "Item") [item.parent, item.parent_sub] = parent(item);
  const ds = [...decoded.ds.clients]
    .sort(([a], [b]) => a - b)
    .map(([client, ranges]) => {
      const out = [];
      for (const r of [...ranges].sort((a, b) => a.clock - b.clock)) {
        const last = out.at(-1);
        if (last && last[0] + last[1] >= r.clock)
          last[1] = Math.max(last[0] + last[1], r.clock + r.len) - last[0];
        else out.push([r.clock, r.len]);
      }
      return [client, out];
    });
  return { structs, ds };
}

export function storageSeed(Y, gc) {
  const a = new Y.Doc({ guid: "storage-source", gc });
  a.clientID = 101;
  a.transact(() => {
    a.getText("text").insert(0, "base😀", {
      bold: true,
      future_format: { opaque: [true, 7] },
    });
    a.getArray("array").insert(0, ["seed", { unknown: "kept" }]);
    const map = a.getMap("map"),
      keep = new Y.Map(),
      discard = new Y.Map();
    map.set("keep", keep);
    for (const owner of [keep, discard]) {
      const array = new Y.Array(),
        childMap = new Y.Map();
      array.insert(0, [1, { future: "value" }]);
      childMap.set("unknown_flavour", { attrs: { x: [1, false] } });
      owner.set("text", new Y.Text("nested😀"));
      owner.set("array", array);
      owner.set("map", childMap);
    }
    map.set("discard", discard);
    map.set("round", -1);
  });
  const base = Y.encodeStateAsUpdate(a),
    packets = [];
  const b = new Y.Doc({ guid: "storage-deferred", gc });
  b.clientID = 202;
  Y.applyUpdate(b, base);
  b.on("update", (u) => packets.push(hex(u)));
  b.transact(() => {
    const later = new Y.Map();
    b.getMap("map").set("later", later);
    later.set("text", new Y.Text());
    later.set("array", new Y.Array());
  });
  b.transact(() => {
    const later = b.getMap("map").get("later");
    later.get("text").insert(0, "queued😀");
    later.get("array").insert(0, ["kept", "deleted"]);
  });
  b.transact(() => {
    const later = b.getMap("map").get("later");
    later.get("text").delete(0, 1);
    later.get("array").delete(1, 1);
  });
  assert.equal(packets.length, 3);
  const deletion = Y.decodeUpdate(Buffer.from(packets[2], "hex"));
  assert.equal(deletion.structs.length, 0);
  assert(deletion.ds.clients.size > 0);
  // Negative control: apply+export loses raw deleted struct material with GC,
  // even though the visible document is the same.
  let deleted;
  a.on("update", (u) => {
    deleted = u;
  });
  a.getMap("map").delete("discard");
  const control = new Y.Doc({ guid: "storage-control", gc });
  control.clientID = 909090;
  for (const [name, type] of [
    ["text", Y.Text],
    ["array", Y.Array],
    ["map", Y.Map],
  ])
    control.get(name, type);
  Y.applyUpdate(control, Y.mergeUpdates([base, deleted]));
  assert.deepEqual(snapshot(Y, control), snapshot(Y, a));
  return {
    base: hex(base),
    parent: packets[0],
    child: packets[1],
    deletion: packets[2],
    parent_deletion: hex(deleted),
    collected: hex(Y.encodeStateAsUpdate(a)),
  };
}
