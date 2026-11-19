const hex = (bytes) => Buffer.from(bytes).toString("hex");
export function value(v) {
  if (v === undefined) return { $any: "undefined" };
  if (typeof v === "bigint") return { $any: "bigint", value: String(v) };
  if (typeof v === "number" && (Object.is(v, -0) || !Number.isFinite(v)))
    return { $any: Object.is(v, -0) ? "-0" : String(v) };
  if (v instanceof Uint8Array) return { $any: "binary", hex: hex(v) };
  if (Array.isArray(v)) return v.map(value);
  if (v && typeof v === "object")
    return Object.fromEntries(
      Object.keys(v)
        .sort()
        .map((k) => [k, value(v[k])]),
    );
  return v;
}
const identity = (t) =>
  t._item ? [t._item.id.client, t._item.id.clock] : null;
function delta(Y, t) {
  const out = [];
  for (const raw of t.toDelta()) {
    const op =
        raw.insert instanceof Y.AbstractType
          ? {
              insert: { $shared: shape(Y, raw.insert) },
              ...(raw.attributes ? { attributes: value(raw.attributes) } : {}),
            }
          : value(raw),
      last = out.at(-1);
    if (
      last &&
      typeof last.insert === "string" &&
      typeof op.insert === "string" &&
      JSON.stringify(last.attributes) === JSON.stringify(op.attributes)
    )
      last.insert += op.insert;
    else out.push(op);
  }
  return out;
}
function shape(Y, t) {
  if (t instanceof Y.Text) {
    const units = [];
    for (let item = t._start; item; item = item.right)
      if (
        !item.deleted &&
        item.countable &&
        typeof item.content.str === "string"
      )
        for (let i = 0; i < item.content.str.length; i++)
          units.push([
            item.id.client,
            item.id.clock + i,
            item.content.str.charCodeAt(i),
          ]);
    return {
      kind: "text",
      id: identity(t),
      text: t.toString().toWellFormed(),
      delta: delta(Y, t),
      units,
    };
  }
  if (t instanceof Y.Array)
    return {
      kind: "array",
      id: identity(t),
      value: t.toArray().map((v) => shape(Y, v)),
    };
  if (t instanceof Y.Map)
    return {
      kind: "map",
      id: identity(t),
      value: Object.fromEntries(
        [...t]
          .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
          .map(([k, v]) => [k, shape(Y, v)]),
      ),
    };
  return { kind: "any", value: value(t) };
}
export function snapshot(Y, d, roots) {
  const full = Y.encodeStateAsUpdate(d);
  return {
    roots: Object.fromEntries(
      [...d.share]
        .filter(([name]) => !roots || Object.hasOwn(roots, name))
        .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
        .map(([k, t]) => [k, shape(Y, t)]),
    ),
    sv: [...Y.decodeStateVector(Y.encodeStateVector(d))].sort(
      (a, b) => a[0] - b[0],
    ),
    ds: [...Y.decodeUpdate(full).ds.clients]
      .sort((a, b) => a[0] - b[0])
      .map(([c, rs]) => [c, rs.map((r) => [r.clock, r.len])]),
    pending: !!(d.store.pendingStructs || d.store.pendingDs),
  };
}
