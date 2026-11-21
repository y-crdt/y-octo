// Node.js Wasm <-> Yjs@13.6.21 / Yjs@13.6.33 / y-protocols@1.0.6 interop tests.
import fs from "node:fs";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { loadYOctoWasm } from "../js/index.mjs";

const require = createRequire(
  fileURLToPath(
    new URL("../../y-octo/tests/oracle/package.json", import.meta.url),
  ),
);
const wasmPath =
  process.argv[2] ??
  fileURLToPath(
    new URL(
      "../../target/wasm32-unknown-unknown/release/y_octo_wasm.wasm",
      import.meta.url,
    ),
  );

const wasmBytes = fs.readFileSync(wasmPath);
const api = await loadYOctoWasm(wasmBytes);
assert.equal(api.abiVersion, 1, "wasm_abi_version must be 1");
const awarenessProtocol = await import(
  require.resolve("y-protocols/awareness")
);

for (const version of ["yjs-13-6-21", "yjs-13-6-33"]) {
  const Y = await import(require.resolve(version));

  // 1. Nested begin_tx/commit_tx with mid-tx read-your-writes + exception-in-callback commit
  {
    const session = new api.DocSession(101, "tx-test", {
      captureTimeoutMs: 500,
    });
    session.advanceTime(1000);
    const root = session.ensureRoot("meta", "Map");
    const target = { Identity: root };

    const { commit } = session.transact(() => {
      assert.equal(session.mapSet(target, "a", { Any: 1 }), null);
      assert.deepEqual(session.getMapValue(target, "a"), { Any: 1 });
      const nested = session.transact(() => {
        assert.equal(session.mapSet(target, "b", { Any: "two" }), null);
        assert.deepEqual(session.getMapValue(target, "b"), { Any: "two" });
      }, "Untracked");
      assert.equal(nested.commit, null, `${version}: inner commit must defer`);
      assert.equal(session.txDepth(), 1);
    }, "Tracked");

    assert.ok(commit, `${version}: outer commit produces single event`);
    assert.equal(commit.origin_kind, "LocalTransact");
    assert.equal(commit.is_local, true);
    assert.equal(commit.can_undo, true);
    assert.deepEqual(commit.changed[0].keys, ["a", "b"]);

    // Verify Yjs reads the single update cleanly
    const ydoc = new Y.Doc();
    Y.applyUpdate(ydoc, commit.update);
    assert.equal(ydoc.getMap("meta").get("a"), 1);
    assert.equal(ydoc.getMap("meta").get("b"), "two");

    // Exception inside transact still commits in finally (matching Yjs doc.transact)
    session.advanceTime(2000);
    let caught = null;
    try {
      session.transact(() => {
        session.mapSet(target, "beforeThrow", { Any: true });
        assert.deepEqual(session.getMapValue(target, "beforeThrow"), {
          Any: true,
        });
        throw new Error("boom");
      }, "Tracked");
    } catch (e) {
      caught = e;
    }
    assert.ok(caught && caught.message === "boom");
    assert.ok(caught.commit, `${version}: exception path still commits`);
    assert.equal(session.txDepth(), 0);
    Y.applyUpdate(ydoc, caught.commit.update);
    assert.equal(ydoc.getMap("meta").get("beforeThrow"), true);

    // Undo pops the exception commit first, then the nested commit as one unit
    const u1 = session.undo();
    assert.deepEqual(u1.origin_kind, { Undo: { stack_id: 0 } });
    assert.equal(session.getMapValue(target, "beforeThrow"), null);
    assert.deepEqual(session.getMapValue(target, "a"), { Any: 1 });
    assert.deepEqual(session.getMapValue(target, "b"), { Any: "two" });

    const u2 = session.undo();
    assert.deepEqual(u2.origin_kind, { Undo: { stack_id: 0 } });
    assert.equal(session.getMapValue(target, "a"), null);
    assert.equal(session.getMapValue(target, "b"), null);
    session.free();
  }

  // 2. Dual-peer concurrent insertions + selective undo/redo + selection_meta + RelativePosition
  {
    const session = new api.DocSession(201, "collab", {
      captureTimeoutMs: 500,
    });
    session.advanceTime(1000);
    const textId = session.ensureRoot("body", "Text");
    const textTarget = { Identity: textId };

    const c1 = session.textInsert(textTarget, 0, "hello");
    session.setUndoSelectionMeta(new Uint8Array([1, 2, 3]));
    const rpos = session.createRelativePosition(textTarget, 5, 0);

    const ydoc = new Y.Doc();
    ydoc.clientID = 202;
    Y.applyUpdate(ydoc, c1.update);
    ydoc.getText("body").insert(5, " peer");
    const peerUpdate = Y.encodeStateAsUpdate(
      ydoc,
      session.encodeStateVectorV1(),
    );

    const remoteCommits = session.applyUpdateV1(peerUpdate);
    assert.equal(remoteCommits.length, 1);
    const remoteCommit = remoteCommits[0];
    assert.equal(remoteCommit.origin_kind, "RemoteSync");
    assert.equal(remoteCommit.is_local, false);
    assert.equal(session.readTextString(textTarget), "hello peer");

    // Local edit after capture window
    session.advanceTime(3000);
    const c2 = session.textInsert(textTarget, 10, "!");
    session.setUndoSelectionMeta(new Uint8Array([9, 8]));
    assert.equal(session.readTextString(textTarget), "hello peer!");
    Y.applyUpdate(ydoc, c2.update);
    assert.equal(ydoc.getText("body").toString(), "hello peer!");

    // RelativePosition roundtrips with Yjs
    const yRpos = Y.decodeRelativePosition(rpos.bytes);
    const yAbs = Y.createAbsolutePositionFromRelativePosition(yRpos, ydoc);
    const wAbs = session.resolveRelativePosition(rpos.bytes, false);
    assert.equal(wAbs.index, yAbs.index);

    // Selective undo removes ONLY local edits, preserving peer's " peer"
    const u1 = session.undo();
    assert.deepEqual(u1.origin_kind, { Undo: { stack_id: 0 } });
    assert.deepEqual(u1.selection_meta, new Uint8Array([9, 8]));
    assert.equal(session.readTextString(textTarget), "hello peer");
    Y.applyUpdate(ydoc, u1.update);
    assert.equal(ydoc.getText("body").toString(), "hello peer");

    const u2 = session.undo();
    assert.deepEqual(u2.selection_meta, new Uint8Array([1, 2, 3]));
    assert.equal(session.readTextString(textTarget), " peer");
    Y.applyUpdate(ydoc, u2.update);
    assert.equal(ydoc.getText("body").toString(), " peer");

    const r1 = session.redo();
    assert.deepEqual(r1.origin_kind, { Redo: { stack_id: 0 } });
    assert.equal(session.readTextString(textTarget), "hello peer");
    Y.applyUpdate(ydoc, r1.update);
    assert.equal(ydoc.getText("body").toString(), "hello peer");
    session.free();
  }

  // 3. revert_update_v1: deletions-only, insertions-only, mixed + GC + concurrent merge
  {
    const ydoc = new Y.Doc({ gc: true });
    ydoc.clientID = 301;
    ydoc.getText("body").insert(0, "alpha beta gamma");
    ydoc.getMap("meta").set("title", "v1");
    ydoc.getArray("items").insert(0, ["x", "y"]);
    const targetSnap = Y.encodeStateAsUpdate(ydoc);

    // Case A: deletions-only (with GC enabled on current!)
    const delDoc = new Y.Doc({ gc: true });
    delDoc.clientID = 302;
    Y.applyUpdate(delDoc, targetSnap);
    delDoc.getText("body").delete(6, 5); // "alpha gamma"
    delDoc.getMap("meta").delete("title");
    delDoc.getArray("items").delete(0, 1); // ["y"]
    const delSnap = Y.encodeStateAsUpdate(delDoc);
    const revertDel = api.revertUpdateV1(delSnap, targetSnap);
    Y.applyUpdate(delDoc, revertDel);
    assert.equal(
      delDoc.getText("body").toString(),
      "alpha beta gamma",
      `${version} del-only text`,
    );
    assert.equal(
      delDoc.getMap("meta").get("title"),
      "v1",
      `${version} del-only map`,
    );
    assert.deepEqual(
      delDoc.getArray("items").toArray(),
      ["x", "y"],
      `${version} del-only array`,
    );

    // Case B: insertions-only
    const insDoc = new Y.Doc({ gc: true });
    insDoc.clientID = 303;
    Y.applyUpdate(insDoc, targetSnap);
    insDoc.getText("body").insert(16, " delta");
    insDoc.getMap("meta").set("extra", 123);
    insDoc.getArray("items").push(["z"]);
    const insSnap = Y.encodeStateAsUpdate(insDoc);
    const revertIns = api.revertUpdateV1(insSnap, targetSnap);
    Y.applyUpdate(insDoc, revertIns);
    assert.equal(
      insDoc.getText("body").toString(),
      "alpha beta gamma",
      `${version} ins-only text`,
    );
    assert.equal(
      insDoc.getMap("meta").get("extra"),
      undefined,
      `${version} ins-only map`,
    );
    assert.deepEqual(
      insDoc.getArray("items").toArray(),
      ["x", "y"],
      `${version} ins-only array`,
    );

    // Case C: mixed insertions + deletions + concurrent peer edit after revert
    const mixDoc = new Y.Doc({ gc: true });
    mixDoc.clientID = 304;
    Y.applyUpdate(mixDoc, targetSnap);
    mixDoc.getText("body").delete(0, 6);
    mixDoc.getText("body").insert(0, "OMEGA ");
    mixDoc.getMap("meta").set("title", "v2");
    mixDoc.getMap("meta").set("temp", true);
    const mixSnap = Y.encodeStateAsUpdate(mixDoc);

    const concurrentPeer = new Y.Doc({ gc: true });
    concurrentPeer.clientID = 305;
    Y.applyUpdate(concurrentPeer, mixSnap);
    concurrentPeer.getMap("meta").set("concurrentKey", "alive");
    const concurrentUpdate = Y.encodeStateAsUpdate(
      concurrentPeer,
      Y.encodeStateVector(mixDoc),
    );

    const revertMix = api.revertUpdateV1(mixSnap, targetSnap);
    api.validateUpdateV1(revertMix);
    Y.applyUpdate(mixDoc, revertMix);
    assert.equal(
      mixDoc.getText("body").toString(),
      "alpha beta gamma",
      `${version} mix text`,
    );
    assert.equal(
      mixDoc.getMap("meta").get("title"),
      "v1",
      `${version} mix map`,
    );
    assert.equal(
      mixDoc.getMap("meta").get("temp"),
      undefined,
      `${version} mix temp`,
    );

    Y.applyUpdate(mixDoc, concurrentUpdate);
    Y.applyUpdate(concurrentPeer, revertMix);
    assert.equal(
      mixDoc.getText("body").toString(),
      concurrentPeer.getText("body").toString(),
    );
    assert.equal(
      mixDoc.getMap("meta").get("title"),
      concurrentPeer.getMap("meta").get("title"),
    );
    assert.equal(mixDoc.getMap("meta").get("concurrentKey"), "alive");
    assert.equal(concurrentPeer.getMap("meta").get("concurrentKey"), "alive");
  }

  // 4. Nested whiteboard element path reads/writes & unknown field preservation
  {
    const session = new api.DocSession(401, "whiteboard", {
      captureTimeoutMs: 500,
    });
    const blocksRoot = session.ensureRoot("blocks", "Map");
    session.mapSet({ Identity: blocksRoot }, "surface-1", {
      Map: [
        ["sys:flavour", { Any: "affine:surface" }],
        [
          "prop:elements",
          {
            Map: [
              [
                "value",
                {
                  Map: [
                    [
                      "elem-1",
                      {
                        Map: [
                          ["type", { Any: "shape" }],
                          ["xywh", { Any: "[0,0,100,100]" }],
                          [
                            "unknownFutureField",
                            { Any: { nested: [1, 2, 3] } },
                          ],
                          [
                            "label",
                            {
                              Text: [{ insert: "Box", format: { bold: true } }],
                            },
                          ],
                        ],
                      },
                    ],
                  ],
                },
              ],
            ],
          },
        ],
      ],
    });

    const elemPath = {
      root: "blocks",
      segments: [
        { Key: "surface-1" },
        { Key: "prop:elements" },
        { Key: "value" },
        { Key: "elem-1" },
      ],
    };
    const elemId = session.resolvePath(elemPath);
    assert.ok(elemId);
    const status = session.typeStatus(elemId);
    assert.equal(status.alive, true);
    assert.equal(status.kind, "Map");
    assert.deepEqual(status.path, elemPath);

    const c = session.mapSet({ Path: elemPath }, "xywh", {
      Any: "[10,20,200,150]",
    });
    assert.deepEqual(c.changed[0].path, elemPath);
    assert.deepEqual(c.changed[0].keys, ["xywh"]);

    assert.deepEqual(
      session.getMapValue({ Path: elemPath }, "unknownFutureField"),
      {
        Any: { nested: [1, 2, 3] },
      },
    );
    const ydoc = new Y.Doc();
    Y.applyUpdate(ydoc, session.encodeUpdateV1());
    const yElem = ydoc
      .getMap("blocks")
      .get("surface-1")
      .get("prop:elements")
      .get("value")
      .get("elem-1");
    assert.equal(yElem.get("xywh"), "[10,20,200,150]");
    assert.deepEqual(yElem.get("unknownFutureField"), { nested: [1, 2, 3] });
    assert.deepEqual(yElem.get("label").toDelta(), [
      { insert: "Box", attributes: { bold: true } },
    ]);
    session.free();
  }

  // 5. Awareness interop with y-protocols@1.0.6 + client_required() rotation
  {
    const ydoc = new Y.Doc();
    ydoc.clientID = 502;
    const yAwareness = new awarenessProtocol.Awareness(ydoc);
    yAwareness.setLocalState({ user: "yjs-peer", cursor: 7 });
    const onlineBytes = awarenessProtocol.encodeAwarenessUpdate(
      yAwareness,
      [502],
    );

    const wAwareness = new api.Awareness(501);
    wAwareness.setLocalState(JSON.stringify({ user: "wasm-peer", cursor: 1 }));
    const evOnline = wAwareness.applyUpdateV1(onlineBytes);
    assert.deepEqual(evOnline.added, [502]);
    assert.equal(wAwareness.getStates().get(502).deleted, false);

    const peerClock = wAwareness.getStates().get(502).clock;
    const ydoc2 = new Y.Doc();
    ydoc2.clientID = 502;
    const yAw2 = new awarenessProtocol.Awareness(ydoc2);
    yAw2.meta.set(502, { clock: peerClock, lastUpdated: Date.now() });
    yAw2.states.delete(502);
    const equalClockNullBytes = awarenessProtocol.encodeAwarenessUpdate(
      yAw2,
      [502],
    );

    const evOffline = wAwareness.applyUpdateV1(equalClockNullBytes);
    assert.deepEqual(
      evOffline.removed,
      [502],
      `${version}: equal-clock null removes peer`,
    );
    assert.equal(wAwareness.getStates().get(502).deleted, true);

    const session = new api.DocSession(501, "collide");
    session.ensureRoot("t", "Text");
    const collider = new Y.Doc();
    collider.clientID = 501;
    collider.getText("t").insert(0, "remote");
    session.applyUpdateV1(Y.encodeStateAsUpdate(collider));
    assert.equal(
      session.clientRequired(),
      true,
      `${version}: collision sets client_required`,
    );

    session.setClient(601);
    assert.equal(session.clientRequired(), false);
    const rotEv = wAwareness.setLocalId(601);
    assert.deepEqual(rotEv.removed, [501]);
    assert.deepEqual(rotEv.added, [601]);
    const rotBytes = wAwareness.encodeUpdate([501, 601]);
    awarenessProtocol.applyAwarenessUpdate(yAwareness, rotBytes, "remote");
    assert.equal(yAwareness.getStates().has(501), false);
    assert.deepEqual(yAwareness.getStates().get(601), {
      user: "wasm-peer",
      cursor: 1,
    });

    // Empty client filter [] must encode 0 entries ([0]), matching y-protocols
    const emptyWasm = wAwareness.encodeUpdate([]);
    const emptyYjs = awarenessProtocol.encodeAwarenessUpdate(yAwareness, []);
    assert.deepEqual(emptyWasm, new Uint8Array([0]));
    assert.deepEqual(emptyWasm, emptyYjs);

    session.free();
    wAwareness.free();
    yAwareness.destroy();
    yAw2.destroy();
  }

  // 6. YXml* (XMLFragment, XMLElement, XMLText, XMLHook) bidirectional sync with Yjs
  {
    const session = new api.DocSession(701, "xml-interop", {
      captureTimeoutMs: 0,
    });
    const frag = session.ensureRoot("doc", "XMLFragment");
    session.arrayPush({ Identity: frag }, [
      {
        XmlElement: {
          tag: "p",
          attrs: [["align", "center"]],
          children: [
            {
              XmlText: [
                { insert: "Hello ", format: undefined },
                { insert: "YXml", format: { b: true } },
              ],
            },
          ],
        },
      },
    ]);
    const pPath = { root: "doc", segments: [{ Index: 0 }] };
    session.xmlSetAttr({ Path: pPath }, "id", "p-1");
    assert.equal(session.xmlName({ Path: pPath }), "p");
    assert.equal(session.xmlGetAttr({ Path: pPath }, "align"), "center");
    assert.deepEqual(session.xmlAttrs({ Path: pPath }), [
      ["align", "center"],
      ["id", "p-1"],
    ]);

    const expectedXml = '<p align="center" id="p-1">Hello <b>YXml</b></p>';
    assert.equal(session.xmlToString({ Identity: frag }), expectedXml);

    // Sync Wasm -> Yjs
    const ydoc = new Y.Doc();
    ydoc.clientID = 702;
    Y.applyUpdate(ydoc, session.encodeUpdateV1());
    const yFrag = ydoc.getXmlFragment("doc");
    assert.equal(yFrag.toString(), expectedXml, `${version}: Wasm -> Yjs XML`);

    // Mutate in Yjs and sync back Yjs -> Wasm
    const ySpan = new Y.XmlElement("span");
    ySpan.setAttribute("role", "note");
    const yTxt = new Y.XmlText();
    yTxt.insert(0, "!");
    ySpan.insert(0, [yTxt]);
    yFrag.insert(1, [ySpan]);

    const diffFromYjs = Y.encodeStateAsUpdate(
      ydoc,
      session.encodeStateVectorV1(),
    );
    const xmlCommits = session.applyUpdateV1(diffFromYjs);
    assert.equal(xmlCommits.length, 1);
    assert.equal(xmlCommits[0].origin_kind, "RemoteSync");
    assert.equal(
      session.xmlToString({ Identity: frag }),
      `${expectedXml}<span role="note">!</span>`,
      `${version}: Yjs -> Wasm XML`,
    );

    const children = session.readArray({ Identity: frag });
    assert.equal(children.length, 2);
    assert.equal(children[0].XmlElement.tag, "p");
    assert.equal(children[1].XmlElement.tag, "span");

    // Invalid YTypeKind throws; camelCase XmlFragment alias works; single-object Embed works
    assert.throws(
      () => session.ensureRoot("bad", "NotAKind"),
      /Invalid YTypeKind/,
    );
    const camelFrag = session.ensureRoot("camelFrag", "XmlFragment");
    assert.deepEqual(camelFrag, { Root: "camelFrag" });

    const embedText = session.ensureRoot("embedText", "Text");
    session.textApplyDelta({ Identity: embedText }, [
      { insert: { image: "https://example.com/a.png" } },
    ]);
    const yEmbedDoc = new Y.Doc();
    Y.applyUpdate(yEmbedDoc, session.encodeUpdateV1());
    assert.deepEqual(yEmbedDoc.getText("embedText").toDelta(), [
      { insert: { image: "https://example.com/a.png" } },
    ]);

    session.free();
  }

  // 7. Multi-stack Undo + Named Origin + Disabled mode
  {
    const disabled = new api.DocSession(801, "disabled-undo", {
      undo: "disabled",
    });
    const dt = disabled.ensureRoot("t", "Text");
    const dc = disabled.textInsert({ Identity: dt }, 0, "no-history");
    assert.equal(dc.can_undo, false);
    assert.equal(disabled.canUndo(), false);
    assert.equal(disabled.undo(), null);
    disabled.free();

    const session = new api.DocSession(802, "multi-undo", {
      undo: "custom",
    });
    const m = session.ensureRoot("m", "Map");
    const target = { Identity: m };
    const stackUser = session.createUndoStack([], 0, [{ Named: "user" }]);
    const stackBot = session.createUndoStack([], 0, [{ Named: "bot" }]);

    const { commit: cUser } = session.transact(
      () => session.mapSet(target, "u", { Any: "human" }),
      { Named: "user" },
    );
    assert.deepEqual(cUser.origin_kind, { LocalNamed: "user" });

    const { commit: cBot } = session.transact(
      () => session.mapSet(target, "b", { Any: "agent" }),
      { Named: "bot" },
    );
    assert.deepEqual(cBot.origin_kind, { LocalNamed: "bot" });

    assert.equal(session.canUndoStack(stackUser), true);
    assert.equal(session.canUndoStack(stackBot), true);

    const uBot = session.undoStack(stackBot);
    assert.deepEqual(uBot.origin_kind, { Undo: { stack_id: stackBot } });
    assert.equal(session.getMapValue(target, "b"), null);
    assert.deepEqual(session.getMapValue(target, "u"), { Any: "human" });

    assert.equal(session.destroyUndoStack(stackBot), true);
    assert.equal(session.destroyUndoStack(stackBot), false);
    assert.equal(session.canUndoStack(stackBot), false);
    assert.equal(session.canUndoStack(stackUser), true);
    session.free();
  }

  // 9. Fable/Astra probe: Date.now() numbers, bigint precision, __proto__ own property
  {
    const ts = 1795241592333;
    const session = new api.DocSession(951, "num-proto-probe");
    const root = { Identity: session.ensureRoot("meta", "Map") };
    session.mapSet(root, "createDate", { Any: ts });
    session.mapSet(root, "page", { Any: { id: "p1", createDate: ts, n: 42 } });
    session.mapSet(root, "row", { Map: [["updatedAt", { Any: ts }]] });
    const rowId = session.getMapValue(root, "row").Map;
    session.mapSet({ Identity: rowId }, "viaItemIdentity", { Any: ts });

    // BigInt roundtrip (small and > Number.MAX_SAFE_INTEGER)
    session.mapSet(root, "biSmall", { Any: 42n });
    session.mapSet(root, "biLarge", { Any: 9007199254740993n });
    assert.equal(session.getMapValue(root, "biSmall").Any, 42n);
    assert.equal(typeof session.getMapValue(root, "biSmall").Any, "bigint");
    assert.equal(session.getMapValue(root, "biLarge").Any, 9007199254740993n);
    assert.equal(typeof session.getMapValue(root, "biLarge").Any, "bigint");

    // Own property "__proto__" must be preserved
    const protoObj = Object.defineProperty({}, "__proto__", {
      value: 1,
      enumerable: true,
      writable: true,
      configurable: true,
    });
    session.mapSet(root, "protoHolder", { Any: protoObj });
    const readProto = session.getMapValue(root, "protoHolder").Any;
    assert.equal(Object.hasOwn(readProto, "__proto__"), true);
    assert.equal(readProto["__proto__"], 1);

    // Yjs must read all Date.now() numbers as JS number and JSON.stringify(toJSON()) must succeed
    const ydoc = new Y.Doc();
    Y.applyUpdate(ydoc, session.encodeUpdateV1());
    const meta = ydoc.getMap("meta");
    assert.equal(typeof meta.get("createDate"), "number");
    assert.equal(meta.get("createDate"), ts);
    assert.equal(typeof meta.get("page").createDate, "number");
    assert.equal(meta.get("page").createDate, ts);
    assert.equal(meta.get("page").n, 42);
    assert.equal(typeof meta.get("row").get("updatedAt"), "number");
    assert.equal(meta.get("row").get("updatedAt"), ts);
    assert.equal(typeof meta.get("row").get("viaItemIdentity"), "number");
    assert.equal(meta.get("row").get("viaItemIdentity"), ts);
    meta.delete("biSmall");
    meta.delete("biLarge");
    assert.doesNotThrow(() => JSON.stringify(meta.toJSON()));
    session.free();
  }

  // 10. Remote rich-text conflict triggers local FormattingCleanup as 2nd commit
  {
    const session = new api.DocSession(1001, "fmt-cleanup");
    const t = { Identity: session.ensureRoot("t", "Text") };
    const c1 = session.textInsert(t, 0, "hello");

    const ydoc = new Y.Doc();
    ydoc.clientID = 1002;
    Y.applyUpdate(ydoc, c1.update);
    const peerSvBefore = Y.encodeStateVector(ydoc);
    ydoc.getText("t").format(0, 5, { bold: true });
    const peerFmt = Y.encodeStateAsUpdate(ydoc, peerSvBefore);

    const cLocalFmt = session.textFormat(t, 0, 5, { bold: true });
    const commits = session.applyUpdateV1(peerFmt);
    assert.equal(
      commits.length,
      2,
      `${version}: remote format conflict yields [RemoteSync, FormattingCleanup]`,
    );
    assert.equal(commits[0].is_local, false);
    assert.equal(commits[0].origin_kind, "RemoteSync");
    assert.equal(commits[1].is_local, true);
    assert.equal(commits[1].origin_kind, "FormattingCleanup");
    assert.equal(commits[1].revision, commits[0].revision + 1);

    // Broadcasting local commits back to Yjs converges both peers
    Y.applyUpdate(ydoc, cLocalFmt.update);
    Y.applyUpdate(ydoc, commits[1].update);
    assert.deepEqual(ydoc.getText("t").toDelta(), [
      { insert: "hello", attributes: { bold: true } },
    ]);
    assert.deepEqual(session.readTextDelta(t), [
      { insert: "hello", format: { bold: true } },
    ]);
    session.free();
  }

  // 8. > 4 MiB payload triggering memory.grow + high-water scratch trim without detached ArrayBuffer
  {
    const session = new api.DocSession(901, "big-payload", {
      undo: "disabled",
    });
    const m = session.ensureRoot("blobs", "Map");
    const target = { Identity: m };
    const bigBytes = new Uint8Array(4 * 1024 * 1024 + 65536);
    for (let i = 0; i < bigBytes.length; i += 4096) {
      bigBytes[i] = (i >>> 12) & 0xff;
    }

    const cBig = session.mapSet(target, "payload", { Any: bigBytes });
    assert.ok(cBig && cBig.update.length > 4 * 1024 * 1024);

    // Small follow-up call triggers high-water auto-trim of in_buf/out_buf; must not crash!
    const cSmall = session.mapSet(target, "small", { Any: "ok" });
    assert.ok(cSmall);
    assert.deepEqual(session.getMapValue(target, "small"), { Any: "ok" });

    const readBack = session.getMapValue(target, "payload");
    assert.equal(readBack.Any.length, bigBytes.length);
    assert.equal(readBack.Any[0], 0);
    assert.equal(readBack.Any[4096], 1);

    // Sync large payload into Yjs
    const ydoc = new Y.Doc();
    Y.applyUpdate(ydoc, session.encodeUpdateV1());
    const yBlob = ydoc.getMap("blobs").get("payload");
    assert.equal(yBlob.length, bigBytes.length);
    assert.equal(yBlob[4096], 1);

    api.trimScratch();
    assert.deepEqual(session.getMapValue(target, "small"), { Any: "ok" });
    session.free();
  }

  // 11. Reentrant getter / Proxy reads during in_buf encoding + exception recovery
  {
    const session = new api.DocSession(1101, "reentrant-getter");
    const m = { Identity: session.ensureRoot("meta", "Map") };
    const t = { Identity: session.ensureRoot("title", "Text") };
    session.mapSet(m, "seed", { Any: "from-seed" });
    session.textInsert(t, 0, "hello-world");

    const getterObj = {
      a: 1,
      get computed() {
        const seed = session.getMapValue(m, "seed").Any;
        const txt = session.readTextString(t);
        return `${seed}:${txt}`;
      },
      b: "tail",
    };
    const proxied = new Proxy(getterObj, {
      get(target, prop, receiver) {
        if (prop === "b") {
          const again = session.getMapValue(m, "seed").Any;
          return `${Reflect.get(target, prop, receiver)}:${again}`;
        }
        return Reflect.get(target, prop, receiver);
      },
    });

    const c = session.mapSet(m, "meta", { Any: proxied });
    assert.ok(c);
    assert.deepEqual(session.getMapValue(m, "meta").Any, {
      a: 1,
      computed: "from-seed:hello-world",
      b: "tail:from-seed",
    });

    const ydoc = new Y.Doc();
    Y.applyUpdate(ydoc, session.encodeUpdateV1());
    assert.deepEqual(ydoc.getMap("meta").get("meta"), {
      a: 1,
      computed: "from-seed:hello-world",
      b: "tail:from-seed",
    });

    // Getter throwing must leave encodeDepth balanced and session healthy
    const throwingObj = {
      get boom() {
        session.getMapValue(m, "seed");
        throw new Error("getter-boom");
      },
    };
    assert.throws(
      () => session.mapSet(m, "bad", { Any: throwingObj }),
      /getter-boom/,
    );
    assert.equal(session.getMapValue(m, "bad"), null);
    assert.ok(session.mapSet(m, "afterBoom", { Any: "healthy" }));
    assert.deepEqual(session.getMapValue(m, "afterBoom"), { Any: "healthy" });
    session.free();
  }

  // 12. UTF-8 BOM (U+FEFF) preservation & { Any: undefined } roundtrip
  {
    const session = new api.DocSession(1201, "bom-undef");
    const m = { Identity: session.ensureRoot("m", "Map") };

    session.mapSet(m, "\uFEFFkey", { Any: "\uFEFFvalue" });
    session.mapSet(m, "key", { Any: "plain" });
    assert.deepEqual(session.getMapValue(m, "\uFEFFkey"), {
      Any: "\uFEFFvalue",
    });
    assert.deepEqual(session.getMapValue(m, "key"), { Any: "plain" });
    const entries = session.readMap(m);
    assert.equal(entries.length, 2);
    assert.ok(
      entries.some(([k, v]) => k === "\uFEFFkey" && v.Any === "\uFEFFvalue"),
    );

    // { Any: undefined } roundtrip vs missing key (null)
    session.mapSet(m, "undefKey", { Any: undefined });
    const readUndef = session.getMapValue(m, "undefKey");
    assert.ok(readUndef !== null && Object.hasOwn(readUndef, "Any"));
    assert.equal(readUndef.Any, undefined);
    assert.equal(session.getMapValue(m, "missingKey"), null);

    // Roundtrip the exact returned { Any: undefined } object back into mapSet/arrayPush
    const a = { Identity: session.ensureRoot("a", "Array") };
    assert.ok(session.mapSet(m, "undefKey2", readUndef));
    assert.ok(session.arrayPush(a, [readUndef]));
    const arrRead = session.readArray(a);
    assert.equal(arrRead.length, 1);
    assert.ok(Object.hasOwn(arrRead[0], "Any"));
    assert.equal(arrRead[0].Any, undefined);
    session.free();
  }

  // 13. Fast-path f64 getter reentrancy on child Map (Identity.Item) + mergeUpdatesV1 ArrayBuffer/generator
  {
    const session = new api.DocSession(1301, "fastpath-and-merge");
    const metaRoot = { Identity: session.ensureRoot("meta", "Map") };
    session.mapSet(metaRoot, "title", { Any: "hello" });
    session.mapSet(metaRoot, "child", { Map: [] });
    const childTarget = {
      Identity: session.getMapValue(metaRoot, "child").Map,
    };

    let getterCalls = 0;
    const c = session.mapSet(childTarget, "score", {
      get Any() {
        getterCalls++;
        const title = session.getMapValue(
          { Identity: { Root: "meta" } },
          "title",
        ).Any;
        return title.length + 0.5;
      },
    });
    assert.ok(c);
    assert.equal(getterCalls, 1, `${version}: value.Any getter called once`);
    assert.deepEqual(session.getMapValue(childTarget, "score"), { Any: 5.5 });
    assert.deepEqual(session.readMap(childTarget), [["score", { Any: 5.5 }]]);

    // mergeUpdatesV1 with ArrayBuffer inputs and single-pass generator
    const s1 = new api.DocSession(1302, "merge-a");
    const r1 = { Identity: s1.ensureRoot("m", "Map") };
    s1.mapSet(r1, "k1", { Any: "v1" });
    const u1 = s1.encodeUpdateV1();

    const s2 = new api.DocSession(1303, "merge-b");
    const r2 = { Identity: s2.ensureRoot("m", "Map") };
    s2.mapSet(r2, "k2", { Any: "v2" });
    const u2 = s2.encodeUpdateV1();

    const mergedFromBuffers = api.mergeUpdatesV1([
      u1.buffer.slice(u1.byteOffset, u1.byteOffset + u1.byteLength),
      u2.buffer.slice(u2.byteOffset, u2.byteOffset + u2.byteLength),
    ]);
    const mergedFromGen = api.mergeUpdatesV1(
      (function* () {
        yield u1;
        yield u2;
      })(),
    );
    assert.deepEqual(mergedFromBuffers, mergedFromGen);

    const check = new api.DocSession(1304, "merge-check");
    check.applyUpdateV1(mergedFromBuffers);
    const checkRoot = { Identity: { Root: "m" } };
    assert.deepEqual(check.getMapValue(checkRoot, "k1"), { Any: "v1" });
    assert.deepEqual(check.getMapValue(checkRoot, "k2"), { Any: "v2" });

    session.free();
    s1.free();
    s2.free();
    check.free();
  }

  // 14. Undeclared Unknown XML root xmlToString, legacy Content::Json exact f64 roundtrip,
  //     and deferred trimScratch() during reentrant getter encoding
  {
    // (a) Undeclared Y.XmlFragment("xml") from Yjs -> xmlToString returns "<p></p>", kind remains "Unknown"
    const yXmlDoc = new Y.Doc();
    yXmlDoc.clientID = 1401;
    const frag = yXmlDoc.getXmlFragment("xml");
    frag.insert(0, [new Y.XmlElement("p")]);
    const xmlSnap = Y.encodeStateAsUpdate(yXmlDoc);

    const sXml = new api.DocSession(1402, "unknown-xml");
    sXml.applyUpdateV1(xmlSnap);
    const xmlRootId = { Root: "xml" };
    assert.equal(
      sXml.xmlToString({ Identity: xmlRootId }),
      "<p></p>",
      `${version}: undeclared Unknown root xmlToString traverses children`,
    );
    assert.equal(
      sXml.typeStatus(xmlRootId).kind,
      "Unknown",
      `${version}: xmlToString does not solidify Unknown root`,
    );
    sXml.free();

    // (b) Legacy V1 Content::Json (tag 2) with 0.36442474781641604 exact float_roundtrip
    // Hand-encoded V1 update: 1 client (7), 1 struct at clock 0, info=2 (Content::Json),
    // parent=named root "jarr", len=1, elem="0.36442474781641604", empty delete set.
    const numStr = "0.36442474781641604";
    const enc = new TextEncoder();
    const rootBytes = enc.encode("jarr");
    const numBytes = enc.encode(numStr);
    const legacyJsonUpdate = new Uint8Array([
      1, // 1 client
      1, // 1 struct
      7, // client id
      0, // clock
      2, // info: Content::Json (tag 2)
      1, // parent is named root
      rootBytes.length,
      ...rootBytes,
      1, // 1 json element
      numBytes.length,
      ...numBytes,
      0, // empty delete set
    ]);
    const sJson = new api.DocSession(1403, "legacy-json-f64");
    sJson.applyUpdateV1(legacyJsonUpdate);
    const jarrTarget = { Identity: { Root: "jarr" } };
    const jarrAll = sJson.readArray(jarrTarget);
    assert.equal(jarrAll.length, 1);
    assert.equal(
      Object.is(jarrAll[0].Any, 0.36442474781641604),
      true,
      `${version}: readArray Content::Json exact f64 roundtrip`,
    );
    const jarrAt0 = sJson.readArrayAt(jarrTarget, 0);
    assert.equal(
      Object.is(jarrAt0.Any, 0.36442474781641604),
      true,
      `${version}: readArrayAt Content::Json exact f64 roundtrip`,
    );
    sJson.free();

    // (c) trimScratch() called inside getter during large (> 256 KiB) mapSet encoding
    const sTrim = new api.DocSession(1404, "deferred-trim");
    const mTrim = { Identity: sTrim.ensureRoot("m", "Map") };
    sTrim.mapSet(mTrim, "seed", { Any: "ok" });
    const bigStr = "x".repeat(300 * 1024);

    // Case 1: getter calls only api.trimScratch() (no nested read)
    const objTrimOnly = {
      prefix: bigStr,
      get trigger() {
        api.trimScratch();
        return "trimmed-only";
      },
      suffix: "tail-1",
    };
    assert.ok(sTrim.mapSet(mTrim, "case1", { Any: objTrimOnly }));

    // Case 2: getter calls both nested read and api.trimScratch()
    const objNestedAndTrim = {
      prefix: bigStr,
      get trigger() {
        const seed = sTrim.getMapValue(mTrim, "seed").Any;
        api.trimScratch();
        return `${seed}+trimmed`;
      },
      suffix: "tail-2",
    };
    assert.ok(sTrim.mapSet(mTrim, "case2", { Any: objNestedAndTrim }));

    const yTrimPeer = new Y.Doc();
    Y.applyUpdate(yTrimPeer, sTrim.encodeUpdateV1());
    const yMap = yTrimPeer.getMap("m");
    assert.equal(yMap.get("case1").prefix.length, bigStr.length);
    assert.equal(yMap.get("case1").trigger, "trimmed-only");
    assert.equal(yMap.get("case1").suffix, "tail-1");
    assert.equal(yMap.get("case2").prefix.length, bigStr.length);
    assert.equal(yMap.get("case2").trigger, "ok+trimmed");
    assert.equal(yMap.get("case2").suffix, "tail-2");
    sTrim.free();
  }

  console.log(
    `y-octo-wasm interop passed against ${version} + y-protocols@1.0.6`,
  );
}
