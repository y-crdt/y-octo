// Validate complete Rust exports for the exact registered text-reader gap.
// This checks fields omitted by current APIs against the full Yjs digest.
import fs from "node:fs";
import { spawnSync } from "node:child_process";
import { gunzipSync } from "node:zlib";
import { fileURLToPath } from "node:url";
import { digest } from "./digest.mjs";
import { snapshot } from "./projection.mjs";
import { expandManifest } from "./upstream-format.mjs";
// Keep each reference version in its own process: every Doc, constructor and
// projection below belongs to exactly one Yjs module instance.
const versionArg = process.argv.find((arg) => arg.startsWith("--version="));
if (!versionArg) {
  for (const version of ["13.6.21", "13.6.33"]) {
    const child = spawnSync(
      process.execPath,
      [
        fileURLToPath(import.meta.url),
        ...process.argv.slice(2),
        `--version=${version}`,
      ],
      { stdio: "inherit" },
    );
    if (child.error) throw child.error;
    if (child.status !== 0) process.exit(child.status ?? 1);
  }
  process.exit(0);
}
const version = versionArg.slice("--version=".length);
if (!["13.6.21", "13.6.33"].includes(version))
  throw Error("unsupported reference version");
const input =
  process.argv.slice(2).find((arg) => !arg.startsWith("--")) ??
  fileURLToPath(
    new URL("../../../target/yjs-oracle/known-exports.jsonl", import.meta.url),
  );
const lines = fs
  .readFileSync(input, "utf8")
  .trim()
  .split("\n")
  .filter(Boolean)
  .map(JSON.parse);
const known = JSON.parse(
  fs.readFileSync(new URL("./upstream-known-failures.json", import.meta.url)),
);
const manifest = expandManifest(
  JSON.parse(
    gunzipSync(
      fs.readFileSync(new URL("./upstream-manifest.json.gz", import.meta.url)),
    ),
  ),
);
const small = process.argv.includes("--small");
const expectedKeys = new Set();
for (const entry of known.cases) {
  if (small && entry.case !== "y-text.tests.js:testTypesAsEmbed") continue;
  for (const [start, length] of entry.replica_ranges)
    for (let i = start; i < start + length; i++)
      for (const version of entry.versions)
        expectedKeys.add(`${entry.case}/${i}/${version}`);
}
const actualKeys = lines.flatMap((r) =>
  r.versions.map((v) => `${r.case}/${r.replica}/${v}`),
);
if (
  actualKeys.length !== expectedKeys.size ||
  actualKeys.some((k) => !expectedKeys.has(k)) ||
  new Set(actualKeys).size !== actualKeys.length
)
  throw Error("missing or duplicated registered export");
{
  const Y = await import(version === "13.6.21" ? "yjs-13-6-21" : "yjs-13-6-33");
  let count = 0;
  for (const record of lines) {
    if (!record.versions.includes(version)) continue;
    const doc = new Y.Doc({ gc: record.gc });
    doc.clientID = 900000;
    for (const [name, kind] of Object.entries(record.roots))
      doc.get(name, { text: Y.Text, array: Y.Array, map: Y.Map }[kind]);
    Y.applyUpdate(doc, new Uint8Array(Buffer.from(record.update, "hex")));
    const target = manifest.records.find(
      (r) => r.name === record.case && r.versions.includes(version),
    ).docs[record.replica].expected_digest;
    const actual = digest(snapshot(Y, doc, record.roots));
    if (record.expected_digest !== target || actual !== target)
      throw Error(
        `${record.case} replica=${record.replica} version=${version}: full Rust export digest differs (${actual} != ${record.expected_digest})`,
      );
    count++;
  }
  console.log(
    `${version}: ${count} full Rust exports match the complete Yjs state digest`,
  );
}
