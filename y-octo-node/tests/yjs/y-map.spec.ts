import assert, { deepEqual } from "node:assert";
import { randomInt } from "node:crypto";
import test from "ava";

import { init, compare, applyRandomTests } from "./testHelper.js";

import * as Y from "../../index";
import * as prng from "lib0/prng";

const production = false;

let gen: prng.PRNG;
test.beforeEach(() => {
  gen = prng.create(randomInt(0, 0xffffffff));
});

test("testIterators", (t) => {
  const ydoc = new Y.Doc();
  const ymap = ydoc.createMap();
  // we are only checking if the type assumptions are correct
  const vals = Array.from(ymap.values());
  const entries = Array.from(ymap.entries());
  const keys = Array.from(ymap.keys());
  t.is(vals.length, 0);
  t.is(entries.length, 0);
  t.is(keys.length, 0);
});

/**
 * Computing event changes after transaction should result in an error. See yjs#539
 */
test.skip("testMapEventError", (t) => {
  const doc = new Y.Doc();
  const ymap = doc.createMap();

  let event: any = null;
  ymap.observe((e) => {
    event = e;
  });
  t.throws(() => {
    t.info(event.keys);
  });
  t.throws(() => {
    t.info(event.keys);
  });
});

test("testMapHavingIterableAsConstructorParamTests", (t) => {
  const { users, map0, testConnector } = init(gen, { users: 1 });

  const m1 = users[0].createMap(Object.entries({ number: 1, string: "hello" }));
  map0.set("m1", m1);
  t.assert(m1.get("number") === 1);
  t.assert(m1.get("string") === "hello");

  const m2 = users[0].createMap([
    ["object", { x: 1 }],
    ["boolean", true],
  ]);
  map0.set("m2", m2);
  t.assert(m2.get<any>("object").x === 1);
  t.assert(m2.get("boolean") === true);

  const m3 = users[0].createMap([...m1.entries(), ...m2.entries()]);
  map0.set("m3", m3);
  t.assert(m3.get("number") === 1);
  t.assert(m3.get("string") === "hello");
  t.assert(m3.get<any>("object").x === 1);
  t.assert(m3.get("boolean") === true);
  testConnector.disconnectAll();
});

test.skip("testBasicMapTests", (t) => {
  const { testConnector, users, map0, map1, map2 } = init(gen, { users: 3 });

  users[2].disconnect();

  map0.set("null", null);
  map0.set("number", 1);
  map0.set("string", "hello Y");
  map0.set("object", { key: { key2: "value" } });
  map0.set("y-map", new Y.Map());
  map0.set("boolean1", true);
  map0.set("boolean0", false);
  const map = map0.get<Y.Map>("y-map");
  map.set("y-array", new Y.Array());
  const array = map.get<Y.Array>("y-array");
  array.insert(0, [0]);
  array.insert(0, [-1]);

  t.assert(map0.get("null") === null, "client 0 computed the change (null)");
  t.assert(map0.get("number") === 1, "client 0 computed the change (number)");
  t.assert(
    map0.get("string") === "hello Y",
    "client 0 computed the change (string)",
  );
  t.assert(
    map0.get("boolean0") === false,
    "client 0 computed the change (boolean)",
  );
  t.assert(
    map0.get("boolean1") === true,
    "client 0 computed the change (boolean)",
  );
  t.deepEqual(
    map0.get("object"),
    { key: { key2: "value" } },
    "client 0 computed the change (object)",
  );
  t.assert(
    map0.get<Y.Map>("y-map").get<Y.Array>("y-array").get(0) === -1,
    "client 0 computed the change (type)",
  );
  t.assert(map0.size === 7, "client 0 map has correct size");

  users[2].connect();
  testConnector.flushAllMessages();

  t.assert(map1.get("null") === null, "client 1 received the update (null)");
  t.assert(map1.get("number") === 1, "client 1 received the update (number)");
  t.assert(
    map1.get("string") === "hello Y",
    "client 1 received the update (string)",
  );
  t.assert(
    map1.get("boolean0") === false,
    "client 1 computed the change (boolean)",
  );
  t.assert(
    map1.get("boolean1") === true,
    "client 1 computed the change (boolean)",
  );
  t.deepEqual(
    map1.get("object"),
    { key: { key2: "value" } },
    "client 1 received the update (object)",
  );
  t.assert(
    map1.get<Y.Map>("y-map").get<Y.Array>("y-array").get(0) === -1,
    "client 1 received the update (type)",
  );
  t.assert(map1.size === 7, "client 1 map has correct size");

  // compare disconnected user
  t.assert(
    map2.get("null") === null,
    "client 2 received the update (null) - was disconnected",
  );
  t.assert(
    map2.get("number") === 1,
    "client 2 received the update (number) - was disconnected",
  );
  t.assert(
    map2.get("string") === "hello Y",
    "client 2 received the update (string) - was disconnected",
  );
  t.assert(
    map2.get("boolean0") === false,
    "client 2 computed the change (boolean)",
  );
  t.assert(
    map2.get("boolean1") === true,
    "client 2 computed the change (boolean)",
  );
  t.deepEqual(
    map2.get("object"),
    { key: { key2: "value" } },
    "client 2 received the update (object) - was disconnected",
  );
  t.assert(
    map2.get<Y.Map>("y-map").get<Y.Array>("y-array").get(0) === -1,
    "client 2 received the update (type) - was disconnected",
  );
  compare(users);
});

test.skip("testGetAndSetOfMapProperty", (t) => {
  const { testConnector, users, map0 } = init(gen, { users: 2 });

  map0.set("stuff", "stuffy");
  map0.set("undefined", undefined);
  map0.set("null", null);
  t.deepEqual(map0.get("stuff"), "stuffy");

  testConnector.flushAllMessages();

  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.deepEqual(u.get("stuff"), "stuffy");
    t.assert(u.get("undefined") === undefined, "undefined");
    t.deepEqual(u.get("null"), null, "null");
  }
  compare(users);
});

test.skip("testYmapSetsYmap", (t) => {
  const { users, map0 } = init(gen, { users: 2 });

  const map = map0.set("Map", users[0].createMap());
  t.assert(Y.compareIds(map0.get<Y.Map>("Map").itemId, map.itemId));
  map.set("one", 1);
  t.deepEqual(map.get("one"), 1);
  compare(users);
});

test.skip("testYmapSetsYarray", (t) => {
  const { users, map0 } = init(gen, { users: 2 });

  const array = map0.set("Array", new Y.Array());
  t.assert(array === map0.get("Array"));
  array.insert(0, [1, 2, 3]);
  // @ts-ignore
  t.deepEqual(map0.toJSON(), { Array: [1, 2, 3] });
  compare(users);
});

test.skip("testGetAndSetOfMapPropertySyncs", (t) => {
  const { testConnector, users, map0 } = init(gen, { users: 2 });

  map0.set("stuff", "stuffy");
  t.deepEqual(map0.get("stuff"), "stuffy");
  testConnector.flushAllMessages();
  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.deepEqual(u.get("stuff"), "stuffy");
  }
  compare(users);
});

test.skip("testGetAndSetOfMapPropertyWithConflict", (t) => {
  const { testConnector, users, map0, map1 } = init(gen, { users: 3 });

  map0.set("stuff", "c0");
  map1.set("stuff", "c1");
  testConnector.flushAllMessages();
  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.deepEqual(u.get("stuff"), "c1");
  }
  compare(users);
});

test("testSizeAndDeleteOfMapProperty", (t) => {
  const { map0, testConnector } = init(gen, { users: 1 });

  map0.set("stuff", "c0");
  map0.set("otherstuff", "c1");
  t.assert(map0.size === 2, `map size is ${map0.size} expected 2`);
  map0.delete("stuff");
  t.assert(
    map0.size === 1,
    `map size after delete is ${map0.size}, expected 1`,
  );
  map0.delete("otherstuff");
  t.assert(
    map0.size === 0,
    `map size after delete is ${map0.size}, expected 0`,
  );
  testConnector.disconnectAll();
});

test("testGetAndSetAndDeleteOfMapProperty", (t) => {
  const { testConnector, users, map0, map1 } = init(gen, { users: 3 });

  map0.set("stuff", "c0");
  map1.set("stuff", "c1");
  map1.delete("stuff");
  testConnector.flushAllMessages();
  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.is(u.get("stuff"), null);
  }
  compare(users);
});

test.skip("testSetAndClearOfMapProperties", (t) => {
  const { testConnector, users, map0 } = init(gen, { users: 1 });

  map0.set("stuff", "c0");
  map0.set("otherstuff", "c1");
  map0.clear();
  testConnector.flushAllMessages();
  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.is(u.get("stuff"), null);
    t.is(u.get("otherstuff"), null);
    t.is(u.size, 0, `map size after clear is ${u.size}, expected 0`);
  }
  compare(users);
});

test.skip("testSetAndClearOfMapPropertiesWithConflicts", (t) => {
  const { testConnector, users, map0, map1, map2, map3 } = init(gen, {
    users: 4,
  });

  map0.set("stuff", "c0");
  map1.set("stuff", "c1");
  map1.set("stuff", "c2");
  map2.set("stuff", "c3");
  testConnector.flushAllMessages();
  map0.set("otherstuff", "c0");
  map1.set("otherstuff", "c1");
  map2.set("otherstuff", "c2");
  map3.set("otherstuff", "c3");
  map3.clear();
  testConnector.flushAllMessages();
  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.assert(u.get("stuff") === undefined);
    t.assert(u.get("otherstuff") === undefined);
    t.assert(u.size === 0, `map size after clear is ${u.size}, expected 0`);
  }
  compare(users);
});

test.skip("testGetAndSetOfMapPropertyWithThreeConflicts", (t) => {
  const { testConnector, users, map0, map1, map2 } = init(gen, { users: 3 });

  map0.set("stuff", "c0");
  map1.set("stuff", "c1");
  map1.set("stuff", "c2");
  map2.set("stuff", "c3");
  testConnector.flushAllMessages();
  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.deepEqual(u.get("stuff"), "c3");
  }
  compare(users);
});

test.skip("testGetAndSetAndDeleteOfMapPropertyWithThreeConflicts", (t) => {
  const { testConnector, users, map0, map1, map2, map3 } = init(gen, {
    users: 4,
  });

  map0.set("stuff", "c0");
  map1.set("stuff", "c1");
  map1.set("stuff", "c2");
  map2.set("stuff", "c3");
  testConnector.flushAllMessages();
  map0.set("stuff", "deleteme");
  map1.set("stuff", "c1");
  map2.set("stuff", "c2");
  map3.set("stuff", "c3");
  map3.delete("stuff");
  testConnector.flushAllMessages();
  for (const user of users) {
    const u = user.getOrCreateMap("map");
    t.assert(u.get("stuff") === undefined);
  }
  compare(users);
});

test.skip("testObserveDeepProperties", (t) => {
  const { testConnector, users, map1, map2, map3 } = init(gen, { users: 4 });

  const _map1 = map1.set("map", users[0].createMap());
  let calls = 0;
  let dmapid;
  map1.observeDeep((events) => {
    events.forEach((event) => {
      calls++;
      // @ts-ignore
      t.assert(event.keysChanged.has("deepmap"));
      t.assert(event.path.length === 1);
      t.assert(event.path[0] === "map");
      // @ts-ignore
      dmapid = event.target.get("deepmap")._item.id;
    });
  });
  testConnector.flushAllMessages();
  const _map3 = map3.get<Y.Map>("map");
  _map3.set("deepmap", new Y.Map());
  testConnector.flushAllMessages();
  const _map2 = map2.get<Y.Map>("map");
  _map2.set("deepmap", new Y.Map());
  testConnector.flushAllMessages();
  const dmap1 = _map1.get<Y.Map>("deepmap");
  const dmap2 = _map2.get<Y.Map>("deepmap");
  const dmap3 = _map3.get<Y.Map>("deepmap");
  t.assert(calls > 0);
  t.assert(Y.compareIds(dmap1.itemId, dmap2.itemId));
  t.assert(Y.compareIds(dmap1.itemId, dmap3.itemId));
  // @ts-ignore we want the possibility of dmapid being undefined
  t.assert(compareIDs(dmap1._item.id, dmapid));
  compare(users);
});

test.skip("testObserversUsingObservedeep", (t) => {
  const { users, map0 } = init(gen, { users: 2 });

  const pathes: Array<Array<string | number>> = [];
  let calls = 0;
  map0.observeDeep((events) => {
    events.forEach((event) => {
      pathes.push(event.path);
    });
    calls++;
  });
  map0.set("map", new Y.Map());
  map0.get<Y.Map>("map").set("array", new Y.Array());
  map0.get<Y.Map>("map").get<Y.Array>("array").insert(0, ["content"]);
  t.assert(calls === 3);
  t.deepEqual(pathes, [[], ["map"], ["map", "array"]]);
  compare(users);
});

test.skip("testPathsOfSiblingEvents", (t) => {
  const { users, map0 } = init(gen, { users: 2 });

  const pathes: Array<Array<string | number>> = [];
  let calls = 0;
  const doc = users[0];
  map0.set("map", users[0].createMap());
  map0.get<Y.Map>("map").set("text1", users[0].createText("initial"));
  map0.observeDeep((events) => {
    events.forEach((event) => {
      pathes.push(event.path);
    });
    calls++;
  });
  doc.transact(() => {
    map0.get<Y.Map>("map").get<Y.Text>("text1").insert(0, "post-");
    map0.get<Y.Map>("map").set("text2", users[0].createText("new"));
  });
  t.assert(calls === 1);
  t.deepEqual(pathes, [["map"], ["map", "text1"]]);
  compare(users);
});

// TODO: Test events in Y.Map
/**
 * @param {Object<string,any>} is
 * @param {Object<string,any>} should
 */
const compareEvent = (
  is: { [s: string]: any },
  should: { [s: string]: any },
) => {
  for (const key in should) {
    deepEqual(should[key], is[key]);
  }
};

test.skip("testThrowsAddAndUpdateAndDeleteEvents", (t) => {
  const { users, map0 } = init(gen, { users: 2 });
  /**
   * @type {Object<string,any>}
   */
  let event: { [s: string]: any } = {};
  map0.observe((e) => {
    event = e; // just put it on event, should be thrown synchronously anyway
  });
  map0.set("stuff", 4);
  compareEvent(event, {
    target: map0,
    keysChanged: new Set(["stuff"]),
  });
  // update, oldValue is in contents
  map0.set("stuff", new Y.Array());
  compareEvent(event, {
    target: map0,
    keysChanged: new Set(["stuff"]),
  });
  // update, oldValue is in opContents
  map0.set("stuff", 5);
  // delete
  map0.delete("stuff");
  compareEvent(event, {
    keysChanged: new Set(["stuff"]),
    target: map0,
  });
  compare(users);
});

test.skip("testThrowsDeleteEventsOnClear", (t) => {
  const { users, map0 } = init(gen, { users: 2 });
  /**
   * @type {Object<string,any>}
   */
  let event: { [s: string]: any } = {};
  map0.observe((e) => {
    event = e; // just put it on event, should be thrown synchronously anyway
  });
  // set values
  map0.set("stuff", 4);
  map0.set("otherstuff", new Y.Array());
  // clear
  map0.clear();
  compareEvent(event, {
    keysChanged: new Set(["stuff", "otherstuff"]),
    target: map0,
  });
  compare(users);
});

test.skip("testChangeEvent", (t) => {
  const { map0, users } = init(gen, { users: 2 });
  /**
   * @type {any}
   */
  let changes: any = null;
  /**
   * @type {any}
   */
  let keyChange: any = null;
  map0.observe((e) => {
    changes = e.changes;
  });
  map0.set("a", 1);
  keyChange = changes.keys.get("a");
  t.assert(
    changes !== null &&
      keyChange.action === "add" &&
      keyChange.oldValue === undefined,
  );
  map0.set("a", 2);
  keyChange = changes.keys.get("a");
  t.assert(
    changes !== null &&
      keyChange.action === "update" &&
      keyChange.oldValue === 1,
  );
  users[0].transact(() => {
    map0.set("a", 3);
    map0.set("a", 4);
  });
  keyChange = changes.keys.get("a");
  t.assert(
    changes !== null &&
      keyChange.action === "update" &&
      keyChange.oldValue === 2,
  );
  users[0].transact(() => {
    map0.set("b", 1);
    map0.set("b", 2);
  });
  keyChange = changes.keys.get("b");
  t.assert(
    changes !== null &&
      keyChange.action === "add" &&
      keyChange.oldValue === undefined,
  );
  users[0].transact(() => {
    map0.set("c", 1);
    map0.delete("c");
  });
  t.assert(changes !== null && changes.keys.size === 0);
  users[0].transact(() => {
    map0.set("d", 1);
    map0.set("d", 2);
  });
  keyChange = changes.keys.get("d");
  t.assert(
    changes !== null &&
      keyChange.action === "add" &&
      keyChange.oldValue === undefined,
  );
  compare(users);
});

test.skip("testYmapEventExceptionsShouldCompleteTransaction", (t) => {
  const doc = new Y.Doc();
  const map = doc.getOrCreateMap("map");

  let updateCalled = false;
  let throwingObserverCalled = false;
  let throwingDeepObserverCalled = false;
  doc.onUpdate(() => {
    updateCalled = true;
  });

  const throwingObserver = () => {
    throwingObserverCalled = true;
    throw new Error("Failure");
  };

  const throwingDeepObserver = () => {
    throwingDeepObserverCalled = true;
    throw new Error("Failure");
  };

  map.observe(throwingObserver);
  map.observeDeep(throwingDeepObserver);

  t.throws(() => {
    map.set("y", "2");
  });

  t.assert(updateCalled);
  t.assert(throwingObserverCalled);
  t.assert(throwingDeepObserverCalled);

  // check if it works again
  updateCalled = false;
  throwingObserverCalled = false;
  throwingDeepObserverCalled = false;
  t.throws(() => {
    map.set("z", "3");
  });

  t.assert(updateCalled);
  t.assert(throwingObserverCalled);
  t.assert(throwingDeepObserverCalled);

  t.assert(map.get("z") === "3");
});

test.skip("testYmapEventHasCorrectValueWhenSettingAPrimitive", (t) => {
  const { users, map0 } = init(gen, { users: 3 });

  /**
   * @type {Object<string,any>}
   */
  let event: { [s: string]: any } = {};
  map0.observe((e) => {
    event = e;
  });
  map0.set("stuff", 2);
  t.deepEqual(event.value, event.target.get(event.name));
  compare(users);
});

test.skip("testYmapEventHasCorrectValueWhenSettingAPrimitiveFromOtherUser", (t) => {
  const { users, map0, map1, testConnector } = init(gen, { users: 3 });

  let event: Record<string, any> = {};
  map0.observe((e) => {
    event = e;
  });
  map1.set("stuff", 2);
  testConnector.flushAllMessages();
  t.deepEqual(event.value, event.target.get(event.name));
  compare(users);
});

const mapTransactions: Array<(arg0: Y.Doc, arg1: prng.PRNG) => void> = [
  function set(user, gen) {
    const key = prng.oneOf(gen, ["one", "two"]);
    const value = prng.utf16String(gen);
    user.getOrCreateMap("map").set(key, value);
  },
  function setType(user, gen) {
    const key = prng.oneOf(gen, ["one", "two"]);
    const type = prng.oneOf(gen, [new Y.Array(), new Y.Map()]);
    user.getOrCreateMap("map").set(key, type);
    if (type instanceof Y.Array) {
      type.insert(0, [1, 2, 3, 4]);
    } else {
      type.set("deepkey", "deepvalue");
    }
  },
  function _delete(user, gen) {
    const key = prng.oneOf(gen, ["one", "two"]);
    user.getOrCreateMap("map").delete(key);
  },
];

test.skip("testRepeatGeneratingYmapTests10", (t) => {
  applyRandomTests(gen, mapTransactions, 3);
});

test.skip("testRepeatGeneratingYmapTests40", (t) => {
  applyRandomTests(gen, mapTransactions, 40);
});

test.skip("testRepeatGeneratingYmapTests42", (t) => {
  applyRandomTests(gen, mapTransactions, 42);
});

test.skip("testRepeatGeneratingYmapTests43", (t) => {
  applyRandomTests(gen, mapTransactions, 43);
});

test.skip("testRepeatGeneratingYmapTests44", (t) => {
  applyRandomTests(gen, mapTransactions, 44);
});

test.skip("testRepeatGeneratingYmapTests45", (t) => {
  applyRandomTests(gen, mapTransactions, 45);
});

test.skip("testRepeatGeneratingYmapTests46", (t) => {
  applyRandomTests(gen, mapTransactions, 46);
});

test.skip("testRepeatGeneratingYmapTests300", (t) => {
  applyRandomTests(gen, mapTransactions, 300);
});

test.skip("testRepeatGeneratingYmapTests400", (t) => {
  applyRandomTests(gen, mapTransactions, 400);
});

test.skip("testRepeatGeneratingYmapTests500", (t) => {
  applyRandomTests(gen, mapTransactions, 500);
});

test.skip("testRepeatGeneratingYmapTests600", (t) => {
  applyRandomTests(gen, mapTransactions, 600);
});

test.skip("testRepeatGeneratingYmapTests1000", (t) => {
  applyRandomTests(gen, mapTransactions, 1000);
});

test.skip("testRepeatGeneratingYmapTests1800", (t) => {
  applyRandomTests(gen, mapTransactions, 1800);
});

test.skip("testRepeatGeneratingYmapTests5000", (t) => {
  if (!production) return;
  applyRandomTests(gen, mapTransactions, 5000);
});

test.skip("testRepeatGeneratingYmapTests10000", (t) => {
  if (!production) return;
  applyRandomTests(gen, mapTransactions, 10000);
});

test.skip("testRepeatGeneratingYmapTests100000", (t) => {
  if (!production) return;
  applyRandomTests(gen, mapTransactions, 100000);
});
