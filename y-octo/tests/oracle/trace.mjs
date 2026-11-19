import readline from "node:readline";
import { snapshot as projectSnapshot } from "./projection.mjs";
import { fileURLToPath } from "node:url";
import { storageSeed, wireState } from "./storage.mjs";

let Y, trace, docs, messages, shadows;
const snapshot = (d) => projectSnapshot(Y, d);
const hex = (bytes) => Buffer.from(bytes).toString("hex");
const bytes = (value) => new Uint8Array(Buffer.from(value, "hex"));
function decode(v) {
  if (v?.$any) {
    switch (v.$any) {
      case "undefined":
        return undefined;
      case "bigint":
        return BigInt(v.value);
      case "-0":
        return -0;
      case "NaN":
        return NaN;
      case "Infinity":
        return Infinity;
      case "-Infinity":
        return -Infinity;
      case "binary":
        return bytes(v.hex);
      default:
        throw Error(`unknown Any ${v.$any}`);
    }
  }
  if (Array.isArray(v)) return v.map(decode);
  if (v && typeof v === "object")
    return Object.fromEntries(
      Object.entries(v).map(([k, x]) => [k, decode(x)]),
    );
  return v;
}
function make(client) {
  const d = new Y.Doc({ guid: `trace-${client}`, gc: trace.gc ?? true });
  d.clientID = client;
  for (const [name, kind] of Object.entries(trace.roots))
    d.get(name, { text: Y.Text, array: Y.Array, map: Y.Map }[kind]);
  return d;
}
function target(d, path) {
  let t = d.share.get(path[0]);
  for (const part of path.slice(1)) t = t?.get(part);
  if (!t) throw Error(`missing target ${JSON.stringify(path)}`);
  return t;
}
function index(t, p, remove = false) {
  let positions;
  if (t instanceof Y.Text) {
    positions = [0];
    let n = 0;
    for (const op of t.toDelta()) {
      if (typeof op.insert === "string") {
        for (const ch of op.insert) {
          n += ch.length;
          positions.push(n);
        }
      } else {
        n++;
        positions.push(n);
      }
    }
  } else positions = Array.from({ length: t.length + 1 }, (_, i) => i);
  if (remove && positions.length > 1) positions.pop();
  if (p === "begin") return positions[0];
  if (p === "middle") return positions[Math.floor((positions.length - 1) / 2)];
  if (p === "end") return positions[positions.length - 1];
  return p;
}
function operate(step) {
  const at = step.op === "sync" ? step.to : step.at,
    d = docs[at],
    sv = Y.encodeStateVector(d);
  if (step.op === "sync") {
    if (step.since) {
      Y.applyUpdate(
        d,
        Y.encodeStateAsUpdate(
          docs[step.from],
          Y.encodeStateVector(new Map(step.since)),
        ),
        "remote",
      );
    } else {
      let selected =
        step.updates === "all"
          ? messages[step.from].map((_, i) => i)
          : step.updates;
      if (step.reverse) selected = [...selected].reverse();
      for (let r = 0; r < (step.repeat ?? 1); r++)
        for (const i of selected) {
          if (!messages[step.from][i])
            throw Error(`unknown packet ${step.from}/${i}`);
          Y.applyUpdate(d, bytes(messages[step.from][i]), "remote");
        }
    }
  } else if (step.op === "apply") {
    Y.applyUpdate(d, bytes(step.update), "external");
  } else if (step.op === "gc") {
    d.transact(() => {});
  } else {
    const t = target(d, step.target),
      pos = index(t, step.index ?? "end", step.op.endsWith("remove"));
    switch (step.op) {
      case "text_insert":
        t.insert(pos, step.value);
        break;
      case "text_remove":
        if (t.length) t.delete(pos, Math.min(step.length ?? 1, t.length - pos));
        break;
      case "format":
        if (t.length)
          t.format(
            pos,
            Math.min(step.length ?? 1, t.length - pos),
            decode(step.attributes),
          );
        break;
      case "text_embed":
        t.insertEmbed(pos, decode(step.value));
        break;
      case "array_insert":
        t.insert(pos, [decode(step.value)]);
        break;
      case "array_remove":
        if (t.length) t.delete(pos, Math.min(step.length ?? 1, t.length - pos));
        break;
      case "map_insert":
        t.set(step.key, decode(step.value));
        break;
      case "map_remove":
        t.delete(step.key);
        break;
      case "create": {
        const child = new { text: Y.Text, array: Y.Array, map: Y.Map }[
          step.kind
        ]();
        if (t instanceof Y.Map) t.set(step.key, child);
        else if (t instanceof Y.Array) t.insert(pos, [child]);
        else throw Error("shared type parent must be map/array");
        break;
      }
      default:
        throw Error(`unsupported operation ${step.op}`);
    }
  }
  messages[at].push(hex(Y.encodeStateAsUpdate(d, sv)));
  return {
    at,
    snapshots: docs.map(snapshot),
    full: hex(Y.encodeStateAsUpdate(d)),
    update: messages[at].at(-1),
  };
}
export async function request(r) {
  if (r.kind === "reset") {
    trace = r.trace;
    Y = await import(r.version === "13.6.21" ? "yjs-13-6-21" : "yjs-13-6-33");
    docs = trace.replicas.map(make);
    shadows = trace.replicas.map((_, i) => make(900000 + i));
    messages = docs.map(() => []);
    return { ok: true };
  }
  if (r.kind === "step") return operate(r.step);
  if (r.kind === "storage_seed") return storageSeed(Y, trace.gc);
  if (r.kind === "storage_wire") {
    const merged = Y.mergeUpdates(r.updates.map(bytes));
    return {
      merged: hex(merged),
      expected: wireState(Y, merged),
      actual: wireState(Y, bytes(r.actual)),
    };
  }
  if (r.kind === "cross") {
    Y.applyUpdate(shadows[r.at], bytes(r.update), "rust");
    return {
      snapshot: snapshot(shadows[r.at]),
      full: hex(Y.encodeStateAsUpdate(shadows[r.at])),
    };
  }
  throw Error(`unknown request ${r.kind}`);
}
if (process.argv[1] === fileURLToPath(import.meta.url)) {
  for await (const line of readline.createInterface({
    input: process.stdin,
    crlfDelay: Infinity,
  })) {
    let incoming;
    try {
      incoming = JSON.parse(line);
      console.log(
        JSON.stringify({ ok: true, result: await request(incoming) }),
      );
    } catch (e) {
      const code =
        incoming?.kind === "cross"
          ? "cross_apply_rejected"
          : incoming?.kind === "step"
            ? "invalid_operation"
            : "protocol_failure";
      console.log(
        JSON.stringify({ ok: false, code, error: String(e.stack ?? e) }),
      );
    }
  }
}
