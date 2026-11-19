// All checked test payloads share one budget; generated pressure streams stay
// under ignored target/ and may be uploaded as CI artifacts.
import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
const root = fileURLToPath(new URL("../../../", import.meta.url));
const limit = 512 * 1024;
const sources = new Set([".rs", ".js", ".mjs", ".ts", ".toml", ".md"]);
const packages = new Set(["package.json", "package-lock.json"]);
const files = new Set(
  execFileSync(
    "git",
    ["ls-files", "--cached", "--others", "--exclude-standard", "-z"],
    {
      cwd: root,
      encoding: "utf8",
    },
  )
    .split("\0")
    .filter(Boolean),
);
const groups = new Map();
for (const name of [...files].sort()) {
  let group;
  if (name.startsWith("y-octo-utils/fuzz/seed_corpus/"))
    group = "Fuzz seed corpus";
  else if (name.startsWith("y-octo/proptest-regressions/"))
    group = "Proptest regressions";
  else if (name.startsWith("y-octo/src/fixtures/"))
    group = "Legacy codec fixtures";
  else if (name.startsWith("y-octo/fixtures/")) group = "Public API fixtures";
  else if (name.startsWith("y-octo/tests/traces/")) group = "Operation traces";
  else if (name.startsWith("y-octo/tests/oracle/"))
    group = "Yjs oracle payloads";
  else continue;
  if (sources.has(path.extname(name)) || packages.has(path.basename(name)))
    continue;
  const file = path.join(root, name);
  if (!fs.existsSync(file)) continue; // A local, not-yet-staged deletion.
  const entry = groups.get(group) ?? { files: 0, bytes: 0 };
  entry.files++;
  const bytes = fs.statSync(file).size;
  entry.bytes += bytes;
  if (process.argv.includes("--list")) console.log(`${bytes}\t${name}`);
  groups.set(group, entry);
}
let total = 0,
  count = 0;
for (const [name, entry] of groups) {
  console.log(`${name}: ${entry.bytes} bytes (${entry.files} files)`);
  total += entry.bytes;
  count += entry.files;
}
console.log(
  `Test payload budget: ${total}/${limit} bytes (${count} files; ${limit - total} bytes remaining)`,
);
if (total > limit) {
  console.error(
    "Test payload budget exceeded: deduplicate/compact checked materials or generate pressure data in CI.",
  );
  process.exitCode = 1;
}
