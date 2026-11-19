import fs from "node:fs";
import { gunzipSync } from "node:zlib";
import { fileURLToPath } from "node:url";
// node unpack.mjs live.jsonl.gz [scenario-name]
const [file, name] = process.argv.slice(2);
if (!file)
  throw new Error("usage: node unpack.mjs <file.jsonl.gz> [scenario-name]");
const path = fileURLToPath(new URL(file, import.meta.url));
const records = gunzipSync(fs.readFileSync(path))
  .toString()
  .trimEnd()
  .split("\n")
  .map((line) => JSON.parse(line))
  .filter((record) => !name || record.name === name);
console.log(JSON.stringify(records, null, 2));
