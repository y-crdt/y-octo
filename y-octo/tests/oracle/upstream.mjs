// Fetch/patch only temporary upstream sources. No upstream tests are vendored.
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { execFileSync } from "node:child_process";
import { gzipBytes } from "./format.mjs";
import { gunzipSync } from "node:zlib";
import { manifest, subset, availableProjection } from "./upstream-format.mjs";
const here = path.dirname(fileURLToPath(import.meta.url));
const versions = {
  "13.6.21": "89dddc2a95079460b7203bde07f45dffd56629f2",
  "13.6.33": "9ea3a4fb57b814292ce18dfd13c4f422e44e6c5c",
};
const args = process.argv.slice(2);
if (args[0] === "--unpack") {
  const input = args.includes("--small")
    ? path.join(here, "upstream-small.json.gz")
    : path.resolve(here, "../../../target/yjs-oracle/upstream.json.gz");
  const corpus = JSON.parse(gunzipSync(fs.readFileSync(input)));
  const records = corpus.records.filter((r) => r.name === args[1]);
  if (!records.length) throw Error(`unknown case ${args[1]}`);
  console.log(
    JSON.stringify(
      records.map((r) => ({
        ...r,
        ...(r.docs
          ? {
              docs: r.docs.map((d, i) => ({
                ...d,
                replica: i,
                updates: d.updates.map((i) => corpus.updates[i]),
                expected: corpus.states[d.expected],
                ...(d.native_end !== undefined
                  ? { native_end: corpus.states[d.native_end] }
                  : {}),
              })),
            }
          : {}),
      })),
      null,
      2,
    ),
  );
  process.exit(0);
}
if (args[0] === "--report") {
  const data = fs.readFileSync(path.join(here, "upstream-manifest.json.gz")),
    m = JSON.parse(gunzipSync(data));
  console.log(
    `# Upstream Yjs oracle\n\nSeed: ${m.seed}; canonical reference: ${m.canonical_version}; manifest: ${data.length} bytes.\n`,
  );
  for (const version of Object.keys(versions)) {
    const counts = {};
    for (const r of m.records.filter((r) => r.versions.includes(version)))
      counts[r.status] = (counts[r.status] ?? 0) + 1;
    console.log(
      `${version}: ${JSON.stringify(counts)}; commit ${versions[version]}`,
    );
  }
  console.log("\n## Version differences\n");
  console.log(
    m.version_differences.length
      ? m.version_differences.join("\n")
      : "No common recorded test differs between the pinned versions. Existing handcrafted #757/nested-children differences remain in concurrent.jsonl.gz.",
  );
  console.log("\nAvailability changes:");
  for (const v of m.version_availability)
    console.log(`- ${v.name}: ${v.versions.join(", ")}`);
  console.log("\n## Excluded or upstream-skipped cases\n");
  for (const r of m.records.filter((r) =>
    ["excluded", "upstream_skip", "generation_failure"].includes(r.status),
  ))
    console.log(
      `- ${r.name} (${r.versions.join(", ")}): ${JSON.stringify(r.reasons ?? r.upstream_conditions ?? r.reason)}`,
    );
  process.exit(0);
}
const scratch = fs.mkdtempSync(path.join(os.tmpdir(), "yjs-oracle-"));
try {
  const outputs = [];
  for (const [version, commit] of Object.entries(versions)) {
    const source = path.join(scratch, version),
      output = path.join(scratch, `${version}.json`);
    execFileSync(
      "git",
      [
        "clone",
        "--quiet",
        "--depth",
        "1",
        "--branch",
        `v${version}`,
        "https://github.com/yjs/yjs.git",
        source,
      ],
      { stdio: "pipe" },
    );
    if (
      execFileSync("git", ["-C", source, "rev-parse", "HEAD"], {
        encoding: "utf8",
      }).trim() !== commit
    )
      throw Error(`upstream tag moved: ${version}`);
    fs.symlinkSync(
      path.join(here, "node_modules"),
      path.join(source, "node_modules"),
      "dir",
    );
    const docFile = path.join(source, "src/utils/Doc.js");
    let doc = fs.readFileSync(docFile, "utf8");
    if (version === "13.6.21")
      doc = doc.replace(
        "generateNewClientId = random.uint32",
        "generateNewClientId = random.uint53",
      );
    doc = doc.replace(
      /generateNewClientId = random.uint(?:32|53)/,
      "generateNewClientId = () => globalThis.__factoryNextId()",
    );
    doc = doc.replace(
      "guid = random.uuidv4()",
      "guid = globalThis.__factoryGuid()",
    );
    doc = doc.replace(
      "this.isDestroyed = false",
      "this.isDestroyed = false; globalThis.__factoryRegister(this)",
    );
    fs.writeFileSync(docFile, doc);
    execFileSync(
      process.execPath,
      [
        "--no-warnings",
        "--experimental-loader",
        path.join(here, "upstream-loader.mjs"),
        path.join(here, "upstream-worker.mjs"),
        source,
        version,
        output,
      ],
      {
        env: { ...process.env, YJS_FACTORY_SOURCE: source },
        stdio: ["ignore", "ignore", "inherit"],
      },
    );
    outputs.push({
      version,
      tests: JSON.parse(fs.readFileSync(output, "utf8")),
    });
  }
  const wire = [],
    states = [],
    packets = new Map(),
    stateIds = new Map(),
    records = new Map();
  const intern = (value, table, ids) => {
    const key = JSON.stringify(value);
    if (!ids.has(key)) {
      ids.set(key, table.length);
      table.push(value);
    }
    return ids.get(key);
  };
  const differences = new Map();
  for (const { version, tests } of outputs)
    for (const test of tests) {
      const record = { ...test };
      if (record.docs)
        record.docs = record.docs.map((d) => ({
          ...d,
          updates: d.updates.map((u) => intern(u, wire, packets)),
          expected: intern(d.expected, states, stateIds),
          ...(d.native_end
            ? {
                native_end: intern(d.native_end, states, stateIds),
                native_update: intern(d.native_update, wire, packets),
              }
            : {}),
        }));
      const key = JSON.stringify(record);
      const existing = records.get(key);
      if (existing) existing.versions.push(version);
      else records.set(key, { versions: [version], ...record });
      const ids = differences.get(test.name) ?? [];
      ids.push({ version, key });
      differences.set(test.name, ids);
    }
  const output = {
    schema: 1,
    wire_format: "UpdateV1",
    canonical_version: "13.6.33",
    upstream: versions,
    affine_patch:
      "13.6.21 client ID generator: uint32 -> uint53; factory replaces randomness with deterministic IDs in both versions",
    seed: 42,
    version_availability: [...differences]
      .filter(([, v]) => v.length === 1)
      .map(([name, v]) => ({ name, versions: v.map((x) => x.version) })),
    version_differences: [...differences]
      .filter(([, v]) => v.length === 2 && v[0].key !== v[1].key)
      .map(([name]) => name),
    updates: wire,
    states,
    records: [...records.values()],
  };
  // Preserve the full Yjs target while adding a separately scoped digest of
  // fields readable through the current live/frozen text APIs.
  const availableCache = new Map();
  for (const record of output.records)
    for (const doc of record.docs ?? []) {
      if (!availableCache.has(doc.expected)) {
        const available = availableProjection(output.states[doc.expected]);
        availableCache.set(
          doc.expected,
          available.missing.length
            ? {
                available: intern(available.state, states, stateIds),
                missing_text_paths: available.missing,
              }
            : {},
        );
      }
      Object.assign(doc, availableCache.get(doc.expected));
    }
  const runtimeDir = path.resolve(here, "../../../target/yjs-oracle");
  fs.mkdirSync(runtimeDir, { recursive: true });
  const data = gzipBytes(Buffer.from(JSON.stringify(output) + "\n"));
  fs.writeFileSync(path.join(runtimeDir, "upstream.json.gz"), data);
  const sampleNames = [
    "updates.tests.js:testKeyEncoding",
    "snapshot.tests.js:testRestoreSnapshotWithSubType",
    "undo-redo.tests.js:testConsecutiveRedoBug",
    "y-text.tests.js:testFalsyFormats",
    "y-text.tests.js:testSplitSurrogateCharacter",
    "y-text.tests.js:testTypesAsEmbed",
  ];
  const sample = gzipBytes(
    Buffer.from(JSON.stringify(subset(output, sampleNames)) + "\n"),
  );
  const samplePath = path.join(here, "upstream-small.json.gz");
  if (process.argv.includes("--check")) {
    if (!fs.readFileSync(samplePath).equals(sample))
      throw Error("upstream small vectors differ");
  } else fs.writeFileSync(samplePath, sample);
  const checked = path.join(here, "upstream-manifest.json.gz");
  const summary = gzipBytes(
    Buffer.from(JSON.stringify(manifest(output)) + "\n"),
  );
  if (process.argv.includes("--check")) {
    if (!fs.readFileSync(checked).equals(summary))
      throw Error(
        "upstream manifest: missing/changed case, stream or expected digest",
      );
  } else fs.writeFileSync(checked, summary);
  console.error(
    `upstream: runtime ${data.length} bytes; checked manifest ${summary.length} bytes; small vectors ${sample.length} bytes; ${records.size} records, ${wire.length} packets, ${states.length} states`,
  );
} finally {
  fs.rmSync(scratch, { recursive: true, force: true });
}
