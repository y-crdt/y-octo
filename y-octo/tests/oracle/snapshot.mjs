// Document snapshots shared by the scripted oracles (undo.mjs, local.mjs),
// in the shape checked by support/concurrent.rs.
export function doc(Y, client, prefix) {
  const d = new Y.Doc({ guid: `${prefix}-${client}`, gc: true });
  d.clientID = client;
  d.getText("text");
  d.getArray("array");
  d.getMap("map");
  return d;
}
function id(value) {
  return value ? [value.client, value.clock] : null;
}
export function shape(Y, t) {
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
export function snapshot(Y, d) {
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
