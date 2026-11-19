import { gzipSync } from "node:zlib";
// JSONL keeps generated fixtures compact and gives each scenario its own diff
// line. Equal scenarios share one versions provenance list.
// Only wire bytes become hex; action/update indices remain numeric.
function wireHex(value, key = "") {
  if (Array.isArray(value)) {
    if (["update", "full_update", "final_update", "binary"].includes(key))
      return Buffer.from(value).toString("hex");
    if (key === "updates" && value.length && Array.isArray(value[0]))
      return value.map((bytes) => Buffer.from(bytes).toString("hex"));
    return value.map((v) => wireHex(v));
  }
  if (value && typeof value === "object")
    return Object.fromEntries(
      Object.entries(value).map(([k, v]) => [k, wireHex(v, k)]),
    );
  return value;
}
export function jsonl(output) {
  const { versions, ...header } = output;
  header.schema = 2;
  const records = new Map();
  for (const [version, scenarios] of Object.entries(versions)) {
    for (const scenario of scenarios) {
      const identity = JSON.stringify(scenario);
      const existing = records.get(identity);
      if (existing) existing.versions.push(version);
      else records.set(identity, { versions: [version], ...wireHex(scenario) });
    }
  }
  return (
    [
      JSON.stringify(header),
      ...[...records.values()].map((record) => JSON.stringify(record)),
    ].join("\n") + "\n"
  );
}

export function gzipCorpus(output) {
  return gzipSync(Buffer.from(jsonl(output)), { level: 9, mtime: 0 });
}
