import { createInterface } from "node:readline";

const version = process.argv[2] === "13.6.21" ? "13.6.21" : "13.6.33";
const Y = await import(version === "13.6.21" ? "yjs-13-6-21" : "yjs-13-6-33");

function buildCases() {
  const cases = [];

  // 1. Single-transaction text + array + map + format + binary
  {
    const doc = new Y.Doc({ gc: true });
    doc.clientID = 11;
    doc.transact(() => {
      doc.getText("text").insert(0, "hello world", { bold: true });
      doc
        .getArray("arr")
        .insert(0, [1, "two", { k: true }, new Uint8Array([9, 8, 7])]);
      doc.getMap("map").set("a", 42);
      doc.getMap("map").set("b", "val");
    });
    cases.push({
      name: "single-tx-mixed",
      update: Array.from(Y.encodeStateAsUpdate(doc)),
      svs: [
        Array.from(Y.encodeStateVector(new Y.Doc())),
        Array.from(Y.encodeStateVector(doc)),
      ],
    });
  }

  // 2. GC snapshot after deletions
  {
    const doc = new Y.Doc({ gc: true });
    doc.clientID = 22;
    const t = doc.getText("t");
    t.insert(0, "abcdef");
    const midSv = Y.encodeStateVector(doc);
    t.delete(1, 3);
    t.insert(3, "XYZ");
    cases.push({
      name: "gc-snapshot",
      update: Array.from(Y.encodeStateAsUpdate(doc)),
      svs: [
        Array.from(Y.encodeStateVector(new Y.Doc())),
        Array.from(midSv),
        Array.from(Y.encodeStateVector(doc)),
      ],
    });
  }

  // 3. Merged update with internal Skip (client 33 has clocks 0..3 and 6..9, missing 3..6)
  {
    const doc = new Y.Doc({ gc: true });
    doc.clientID = 33;
    const t = doc.getText("t");
    t.insert(0, "aaa");
    const u1 = Y.encodeStateAsUpdate(doc);
    const sv1 = Y.encodeStateVector(doc);
    t.insert(3, "bbb");
    const sv2 = Y.encodeStateVector(doc);
    t.insert(6, "ccc");
    const u3 = Y.encodeStateAsUpdate(doc, sv2);
    const mergedWithSkip = Y.mergeUpdates([u1, u3]);
    cases.push({
      name: "merged-with-skip",
      update: Array.from(mergedWithSkip),
      svs: [
        Array.from(Y.encodeStateVector(new Y.Doc())),
        Array.from(sv1),
        Array.from(sv2),
      ],
    });
  }

  // 4. UTF-16 surrogate pair A😀B split at offsets 1, 2, 3
  {
    const doc = new Y.Doc({ gc: true });
    doc.clientID = 44;
    doc.getText("t").insert(0, "A😀B");
    const update = Y.encodeStateAsUpdate(doc);
    const makeSv = (clock) => {
      const m = new Map();
      if (clock > 0) m.set(44, clock);
      return Array.from(Y.encodeStateVector(m));
    };
    cases.push({
      name: "utf16-surrogate-a-emoji-b",
      update: Array.from(update),
      svs: [makeSv(0), makeSv(1), makeSv(2), makeSv(3), makeSv(4)],
    });
  }

  // 5. ContentAny multi-element split
  {
    const doc = new Y.Doc({ gc: true });
    doc.clientID = 55;
    doc.getArray("arr").insert(0, [10, "str", null, true, { nested: [1, 2] }]);
    const update = Y.encodeStateAsUpdate(doc);
    const makeSv = (clock) => {
      const m = new Map();
      if (clock > 0) m.set(55, clock);
      return Array.from(Y.encodeStateVector(m));
    };
    cases.push({
      name: "content-any-split",
      update: Array.from(update),
      svs: [makeSv(0), makeSv(1), makeSv(2), makeSv(4), makeSv(5)],
    });
  }

  // 6. Three-client mixed writes & deletions:
  //    client 10 fully covered, client 20 partially covered (mid-struct split),
  //    client 30 absent from sv.
  {
    const docA = new Y.Doc({ gc: true });
    docA.clientID = 10;
    docA.getText("t").insert(0, "alpha");
    docA.getMap("m").set("a", 1);

    const docB = new Y.Doc({ gc: true });
    docB.clientID = 20;
    Y.applyUpdate(docB, Y.encodeStateAsUpdate(docA));
    docB.getText("t").insert(5, "beta-mid");
    docB.getArray("arr").insert(0, [1, 2, 3, 4]);
    docB.getText("t").delete(1, 2);

    const docC = new Y.Doc({ gc: true });
    docC.clientID = 30;
    Y.applyUpdate(docC, Y.encodeStateAsUpdate(docB));
    docC.getText("t").insert(0, "gamma");
    docC.getMap("m").set("c", "end");

    const update = Y.encodeStateAsUpdate(docC);
    const svPartial = new Map();
    svPartial.set(10, 6); // fully covers client 10
    svPartial.set(20, 4); // lands inside client 20's "beta-mid" text struct
    // client 30 intentionally omitted

    cases.push({
      name: "three-client-mixed",
      update: Array.from(update),
      svs: [
        Array.from(Y.encodeStateVector(new Y.Doc())),
        Array.from(Y.encodeStateVector(svPartial)),
        Array.from(Y.encodeStateVector(docC)),
      ],
    });
  }

  return cases;
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
for await (const line of rl) {
  if (!line.trim()) continue;
  const req = JSON.parse(line);
  if (req.op === "sv") {
    const out = Y.encodeStateVectorFromUpdate(new Uint8Array(req.update));
    process.stdout.write(JSON.stringify({ bytes: Array.from(out) }) + "\n");
  } else if (req.op === "diff") {
    const out = Y.diffUpdate(
      new Uint8Array(req.update),
      new Uint8Array(req.sv),
    );
    process.stdout.write(JSON.stringify({ bytes: Array.from(out) }) + "\n");
  } else if (req.op === "build_cases") {
    process.stdout.write(JSON.stringify({ cases: buildCases() }) + "\n");
  } else {
    throw new Error(`unknown op: ${req.op}`);
  }
}
