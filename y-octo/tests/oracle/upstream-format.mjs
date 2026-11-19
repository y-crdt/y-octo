import { digest } from "./digest.mjs";
export function availableProjection(original) {
  const state = structuredClone(original),
    missing = [];
  const pointer = (k) => String(k).replaceAll("~", "~0").replaceAll("/", "~1");
  function visit(node, path) {
    if (node.kind === "text" && node.delta.some((op) => op.insert?.$shared)) {
      missing.push(path);
      delete node.units;
      const delta = [];
      for (const op of node.delta.filter((op) => !op.insert?.$shared)) {
        const last = delta.at(-1);
        if (
          last &&
          typeof last.insert === "string" &&
          typeof op.insert === "string" &&
          JSON.stringify(last.attributes) === JSON.stringify(op.attributes)
        )
          last.insert += op.insert;
        else delta.push(op);
      }
      node.delta = delta;
    } else if (node.kind === "map")
      for (const [k, v] of Object.entries(node.value))
        visit(v, `${path}/value/${pointer(k)}`);
    else if (node.kind === "array")
      node.value.forEach((v, i) => visit(v, `${path}/value/${i}`));
  }
  for (const [k, v] of Object.entries(state.roots))
    visit(v, `/roots/${pointer(k)}`);
  return { state, missing };
}
// Full stress streams stay under target/ and in CI artifacts. Git carries this
// manifest, which pins every case, event stream and expected end state.
export function manifest(corpus) {
  const { updates, states, records, ...header } = corpus;
  const documents = [],
    digests = [],
    docIds = new Map(),
    digestIds = new Map();
  const intern = (value, table, ids) => {
    const key = JSON.stringify(value);
    if (!ids.has(key)) {
      ids.set(key, table.length);
      table.push(value);
    }
    return ids.get(key);
  };
  const hash = (value) => intern(digest(value), digests, digestIds);
  const stateHashes = new Map(),
    streamHashes = new Map();
  const stateHash = (i) => {
    if (!stateHashes.has(i)) stateHashes.set(i, hash(states[i]));
    return stateHashes.get(i);
  };
  const streamHash = (indices) => {
    const key = JSON.stringify(indices);
    if (!streamHashes.has(key))
      streamHashes.set(key, hash(indices.map((i) => updates[i])));
    return streamHashes.get(key);
  };
  return {
    ...header,
    digest_encoding: "tagged-json-sha256-v1",
    records: records.map((record) => ({
      ...record,
      ...(record.docs
        ? {
            docs: record.docs.map((doc) => {
              const {
                updates: indices,
                expected,
                native_end,
                native_update,
                available,
                ...meta
              } = doc;
              return intern(
                {
                  ...meta,
                  update_count: indices.length,
                  updates_digest: streamHash(indices),
                  expected_digest: stateHash(expected),
                  ...(available !== undefined
                    ? { available_digest: stateHash(available) }
                    : {}),
                  ...(native_end !== undefined
                    ? {
                        native_end_digest: stateHash(native_end),
                        native_update_digest: hash(updates[native_update]),
                      }
                    : {}),
                },
                documents,
                docIds,
              );
            }),
          }
        : {}),
    })),
    documents,
    digests,
  };
}
export function expandManifest(manifest) {
  const { documents, digests, ...header } = manifest;
  const expanded = documents.map((doc) =>
    Object.fromEntries(
      Object.entries(doc).map(([k, v]) => [
        k,
        k.endsWith("_digest") ? digests[v] : v,
      ]),
    ),
  );
  return {
    ...header,
    records: manifest.records.map((r) => ({
      ...r,
      ...(r.docs ? { docs: r.docs.map((i) => expanded[i]) } : {}),
    })),
  };
}
export function subset(corpus, names) {
  const records = corpus.records.filter((r) => names.includes(r.name));
  const updateIds = new Map(),
    stateIds = new Map(),
    updates = [],
    states = [];
  const remap = (i, source, table, ids) => {
    if (!ids.has(i)) {
      ids.set(i, table.length);
      table.push(source[i]);
    }
    return ids.get(i);
  };
  return {
    ...corpus,
    updates,
    states,
    records: records.map((r) => ({
      ...r,
      docs: r.docs.map((d) => ({
        ...d,
        updates: d.updates.map((i) =>
          remap(i, corpus.updates, updates, updateIds),
        ),
        expected: remap(d.expected, corpus.states, states, stateIds),
        ...(d.available !== undefined
          ? { available: remap(d.available, corpus.states, states, stateIds) }
          : {}),
        ...(d.native_end !== undefined
          ? {
              native_end: remap(d.native_end, corpus.states, states, stateIds),
              native_update: remap(
                d.native_update,
                corpus.updates,
                updates,
                updateIds,
              ),
            }
          : {}),
      })),
    })),
  };
}
