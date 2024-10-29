import test from "ava";
import * as Y from "@y-octo/node";

test.skip("testAfterTransactionRecursion", (t) => {
  const ydoc = new Y.Doc();
  const yxml = ydoc.getXmlFragment("");
  ydoc.on("afterTransaction", (tr) => {
    if (tr.origin === "test") {
      yxml.toJSON();
    }
  });
  ydoc.transact((_tr) => {
    for (let i = 0; i < 15000; i++) {
      yxml.push([new Y.XmlText("a")]);
    }
  }, "test");
});

test.skip("testOriginInTransaction", (t) => {
  const doc = new Y.Doc();
  const ytext = doc.getText();
  /**
   * @type {Array<string>}
   */
  const origins = [];
  doc.on("afterTransaction", (tr) => {
    origins.push(tr.origin);
    if (origins.length <= 1) {
      ytext.toDelta(Y.snapshot(doc)); // adding a snapshot forces toDelta to create a cleanup transaction
      doc.transact(() => {
        ytext.insert(0, "a");
      }, "nested");
    }
  });
  doc.transact(() => {
    ytext.insert(0, "0");
  }, "first");
  t.deepEqual(origins, ["first", "cleanup", "nested"]);
});

/**
 * Client id should be changed when an instance receives updates from another client using the same client id.
 */
test("testClientIdDuplicateChange", (t) => {
  const doc1 = new Y.Doc(0);
  const doc2 = new Y.Doc(0);
  t.assert(doc2.clientId === doc1.clientId);
  doc1.getArray("a").insert(0, [1, 2]);
  Y.applyUpdate(doc2, Y.encodeStateAsUpdate(doc1), false);
  t.assert(doc2.clientId !== doc1.clientId);
});

test("testGetTypeEmptyId", (t) => {
  const doc1 = new Y.Doc();
  doc1.getText("").insert(0, "h");
  doc1.getText().insert(1, "i");
  const doc2 = new Y.Doc();
  Y.applyUpdate(doc2, Y.encodeStateAsUpdate(doc1));
  t.assert(doc2.getText().toString() === "hi");
  t.assert(doc2.getText("").toString() === "hi");
});

test.skip("testToJSON", (t) => {
  const doc = new Y.Doc();
  t.deepEqual(doc.toJSON(), {}, "doc.toJSON yields empty object");

  const arr = doc.getArray("array");
  arr.push(["test1"]);

  const map = doc.getMap("map");
  map.set("k1", "v1");
  const map2 = new Y.Map();
  map.set("k2", map2);
  map2.set("m2k1", "m2v1");

  t.deepEqual(
    doc.toJSON(),
    {
      array: ["test1"],
      map: {
        k1: "v1",
        k2: {
          m2k1: "m2v1",
        },
      },
    },
    "doc.toJSON has array and recursive map",
  );
});

test.skip("testSubdoc", (t) => {
  const doc = new Y.Doc();
  doc.load(); // doesn't do anything
  {
    /**
     * @type {Array<any>|null}
     */
    let event = /** @type {any} */ null;
    doc.on("subdocs", (subdocs) => {
      event = [
        Array.from(subdocs.added).map((x) => x.guid),
        Array.from(subdocs.removed).map((x) => x.guid),
        Array.from(subdocs.loaded).map((x) => x.guid),
      ];
    });
    const subdocs = doc.getMap("mysubdocs");
    const docA = new Y.Doc({ guid: "a" });
    docA.load();
    subdocs.set("a", docA);
    t.deepEqual(event, [["a"], [], ["a"]]);

    event = null;
    subdocs.get("a").load();
    t.assert(event === null);

    event = null;
    subdocs.get("a").destroy();
    t.deepEqual(event, [["a"], ["a"], []]);
    subdocs.get("a").load();
    t.deepEqual(event, [[], [], ["a"]]);

    subdocs.set("b", new Y.Doc({ guid: "a", shouldLoad: false }));
    t.deepEqual(event, [["a"], [], []]);
    subdocs.get("b").load();
    t.deepEqual(event, [[], [], ["a"]]);

    const docC = new Y.Doc({ guid: "c" });
    docC.load();
    subdocs.set("c", docC);
    t.deepEqual(event, [["c"], [], ["c"]]);

    t.deepEqual(Array.from(doc.getSubdocGuids()), ["a", "c"]);
  }

  const doc2 = new Y.Doc();
  {
    t.deepEqual(Array.from(doc2.getSubdocs()), []);
    /**
     * @type {Array<any>|null}
     */
    let event = /** @type {any} */ null;
    doc2.on("subdocs", (subdocs) => {
      event = [
        Array.from(subdocs.added).map((d) => d.guid),
        Array.from(subdocs.removed).map((d) => d.guid),
        Array.from(subdocs.loaded).map((d) => d.guid),
      ];
    });
    Y.applyUpdate(doc2, Y.encodeStateAsUpdate(doc));
    t.deepEqual(event, [["a", "a", "c"], [], []]);

    doc2.getMap("mysubdocs").get("a").load();
    t.deepEqual(event, [[], [], ["a"]]);

    t.deepEqual(Array.from(doc2.getSubdocGuids()), ["a", "c"]);

    doc2.getMap("mysubdocs").delete("a");
    t.deepEqual(event, [[], ["a"], []]);
    t.deepEqual(Array.from(doc2.getSubdocGuids()), ["a", "c"]);
  }
});

test.skip("testSubdocLoadEdgeCases", (t) => {
  const ydoc = new Y.Doc();
  const yarray = ydoc.getArray();
  const subdoc1 = new Y.Doc();
  /**
   * @type {any}
   */
  let lastEvent = null;
  ydoc.on("subdocs", (event) => {
    lastEvent = event;
  });
  yarray.insert(0, [subdoc1]);
  t.assert(subdoc1.shouldLoad);
  t.assert(subdoc1.autoLoad === false);
  t.assert(lastEvent !== null && lastEvent.loaded.has(subdoc1));
  t.assert(lastEvent !== null && lastEvent.added.has(subdoc1));
  // destroy and check whether lastEvent adds it again to added (it shouldn't)
  subdoc1.destroy();
  const subdoc2 = yarray.get(0);
  t.assert(subdoc1 !== subdoc2);
  t.assert(lastEvent !== null && lastEvent.added.has(subdoc2));
  t.assert(lastEvent !== null && !lastEvent.loaded.has(subdoc2));
  // load
  subdoc2.load();
  t.assert(lastEvent !== null && !lastEvent.added.has(subdoc2));
  t.assert(lastEvent !== null && lastEvent.loaded.has(subdoc2));
  // apply from remote
  const ydoc2 = new Y.Doc();
  ydoc2.on("subdocs", (event) => {
    lastEvent = event;
  });
  Y.applyUpdate(ydoc2, Y.encodeStateAsUpdate(ydoc));
  const subdoc3 = ydoc2.getArray().get(0);
  t.assert(subdoc3.shouldLoad === false);
  t.assert(subdoc3.autoLoad === false);
  t.assert(lastEvent !== null && lastEvent.added.has(subdoc3));
  t.assert(lastEvent !== null && !lastEvent.loaded.has(subdoc3));
  // load
  subdoc3.load();
  t.assert(subdoc3.shouldLoad);
  t.assert(lastEvent !== null && !lastEvent.added.has(subdoc3));
  t.assert(lastEvent !== null && lastEvent.loaded.has(subdoc3));
});

test.skip("testSubdocLoadEdgeCasesAutoload", (t) => {
  const ydoc = new Y.Doc();
  const yarray = ydoc.getArray();
  const subdoc1 = new Y.Doc({ autoLoad: true });
  /**
   * @type {any}
   */
  let lastEvent = null;
  ydoc.on("subdocs", (event) => {
    lastEvent = event;
  });
  yarray.insert(0, [subdoc1]);
  t.assert(subdoc1.shouldLoad);
  t.assert(subdoc1.autoLoad);
  t.assert(lastEvent !== null && lastEvent.loaded.has(subdoc1));
  t.assert(lastEvent !== null && lastEvent.added.has(subdoc1));
  // destroy and check whether lastEvent adds it again to added (it shouldn't)
  subdoc1.destroy();
  const subdoc2 = yarray.get(0);
  t.assert(subdoc1 !== subdoc2);
  t.assert(lastEvent !== null && lastEvent.added.has(subdoc2));
  t.assert(lastEvent !== null && !lastEvent.loaded.has(subdoc2));
  // load
  subdoc2.load();
  t.assert(lastEvent !== null && !lastEvent.added.has(subdoc2));
  t.assert(lastEvent !== null && lastEvent.loaded.has(subdoc2));
  // apply from remote
  const ydoc2 = new Y.Doc();
  ydoc2.on("subdocs", (event) => {
    lastEvent = event;
  });
  Y.applyUpdate(ydoc2, Y.encodeStateAsUpdate(ydoc));
  const subdoc3 = ydoc2.getArray().get(0);
  t.assert(subdoc1.shouldLoad);
  t.assert(subdoc1.autoLoad);
  t.assert(lastEvent !== null && lastEvent.added.has(subdoc3));
  t.assert(lastEvent !== null && lastEvent.loaded.has(subdoc3));
});

test.skip("testSubdocsUndo", (t) => {
  const ydoc = new Y.Doc();
  const elems = ydoc.getXmlFragment();
  const undoManager = new Y.UndoManager(elems);
  const subdoc = new Y.Doc();
  // @ts-ignore
  elems.insert(0, [subdoc]);
  undoManager.undo();
  undoManager.redo();
  t.assert(elems.length === 1);
});

test.skip("testLoadDocsEvent", async (t) => {
  const ydoc = new Y.Doc();
  t.assert(ydoc.isLoaded === false);
  let loadedEvent = false;
  ydoc.on("load", () => {
    loadedEvent = true;
  });
  ydoc.emit("load", [ydoc]);
  await ydoc.whenLoaded;
  t.assert(loadedEvent);
  t.assert(ydoc.isLoaded);
});

test.skip("testSyncDocsEvent", async (t) => {
  const ydoc = new Y.Doc();
  t.assert(ydoc.isLoaded === false);
  t.assert(ydoc.isSynced === false);
  let loadedEvent = false;
  ydoc.once("load", () => {
    loadedEvent = true;
  });
  let syncedEvent = false;
  ydoc.once(
    "sync",
    /** @param {any} isSynced */ (isSynced) => {
      syncedEvent = true;
      t.assert(isSynced);
    },
  );
  ydoc.emit("sync", [true, ydoc]);
  await ydoc.whenLoaded;
  const oldWhenSynced = ydoc.whenSynced;
  await ydoc.whenSynced;
  t.assert(loadedEvent);
  t.assert(syncedEvent);
  t.assert(ydoc.isLoaded);
  t.assert(ydoc.isSynced);
  let loadedEvent2 = false;
  ydoc.on("load", () => {
    loadedEvent2 = true;
  });
  let syncedEvent2 = false;
  ydoc.on("sync", (isSynced) => {
    syncedEvent2 = true;
    t.assert(isSynced === false);
  });
  ydoc.emit("sync", [false, ydoc]);
  t.assert(!loadedEvent2);
  t.assert(syncedEvent2);
  t.assert(ydoc.isLoaded);
  t.assert(!ydoc.isSynced);
  t.assert(ydoc.whenSynced !== oldWhenSynced);
});
