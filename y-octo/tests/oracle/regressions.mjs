import fs from "node:fs";
import { gunzipSync } from "node:zlib";
import { gzipBytes } from "./format.mjs";
import { fileURLToPath } from "node:url";
import { request } from "./trace.mjs";

const dir = fileURLToPath(new URL("../traces/", import.meta.url));
const args = process.argv.slice(2);
if (args[0] === "--unpack") {
  const stored = fs.readFileSync(`${dir}/${args[1]}.json.gz`);
  console.log(JSON.stringify(JSON.parse(gunzipSync(stored)), null, 2));
  process.exit(0);
}
if (args[0] === "--import") {
  const trace = JSON.parse(fs.readFileSync(args[1], "utf8"));
  delete trace.expected;
  fs.writeFileSync(
    `${dir}/${trace.name}.json.gz`,
    gzipBytes(Buffer.from(JSON.stringify(trace))),
  );
}
for (const name of fs
  .readdirSync(dir)
  .filter((n) => n.endsWith(".json.gz"))
  .sort()) {
  const path = `${dir}/${name}`,
    stored = fs.readFileSync(path);
  const { expected, versions, ...trace } = JSON.parse(gunzipSync(stored));
  const outputs = [];
  for (const version of versions ?? ["13.6.21", "13.6.33"]) {
    await request({ kind: "reset", trace, version });
    let result;
    for (const step of trace.steps)
      result = await request({ kind: "step", step });
    outputs.push(result.snapshots);
  }
  if (
    outputs.length > 1 &&
    JSON.stringify(outputs[0]) !== JSON.stringify(outputs[1])
  )
    throw Error(
      `${name}: new version difference; preserve both expectations explicitly`,
    );
  const generated = gzipBytes(
    Buffer.from(
      JSON.stringify({
        ...trace,
        versions: versions ?? ["13.6.21", "13.6.33"],
        expected: outputs.at(-1),
      }) + "\n",
    ),
  );
  if (process.argv.includes("--check")) {
    if (!stored.equals(generated))
      throw Error(`${name} differs from pinned Yjs generation`);
  } else fs.writeFileSync(path, generated);
  console.log(`${name}: ${generated.length} bytes, Yjs-authored expectations`);
}
