import test from "ava";

import { init, compare, applyRandomTests } from "./testHelper";

import * as Y from "../../yocto";
import * as prng from "lib0/prng";
import * as math from "lib0/math";
import { randomInt } from "node:crypto";
import assert, { deepEqual } from "node:assert";

const production = false;

let gen: prng.PRNG;
test.beforeEach(() => {
  gen = prng.create(randomInt(0, 0xffffffff));
});

test("testBasicUpdate", (t) => {
  const doc1 = new Y.Doc();
  const doc2 = new Y.Doc();
  doc1.getOrCreateArray("array").insert(0, ["hi"]);
  const update = Y.encodeStateAsUpdate(doc1);
  Y.applyUpdate(doc2, update);
  t.deepEqual(doc2.getOrCreateArray("array").toArray(), ["hi"]);
});

test("testSlice", (t) => {
  const doc1 = new Y.Doc();
  const arr = doc1.getOrCreateArray("array");
  arr.insert(0, [1, 2, 3]);
  t.deepEqual(arr.slice(0), [1, 2, 3]);
  t.deepEqual(arr.slice(1), [2, 3]);
  t.deepEqual(arr.slice(0, -1), [1, 2]);
  arr.insert(0, [0]);
  t.deepEqual(arr.slice(0), [0, 1, 2, 3]);
  t.deepEqual(arr.slice(0, 2), [0, 1]);
});

test("testArrayFrom", (t) => {
  const doc1 = new Y.Doc();
  const db1 = doc1.getOrCreateMap("root");
  const nestedArray1 = Y.Array.from([0, 1, 2]);
  db1.set("array", nestedArray1);
  t.deepEqual(nestedArray1.toArray(), [0, 1, 2]);
});

/**
 * Debugging yjs#297 - a critical bug connected to the search-marker approach
 */
test("testLengthIssue", (t) => {
  const doc1 = new Y.Doc();
  const arr = doc1.getOrCreateArray("array");
  arr.push([0, 1, 2, 3]);
  arr.delete(0);
  arr.insert(0, [0]);
  t.is(arr.length, arr.toArray().length);
  doc1.transact(() => {
    arr.delete(1);
    t.is(arr.length, arr.toArray().length);
    arr.insert(1, [1]);
    t.is(arr.length, arr.toArray().length);
    arr.delete(2);
    t.is(arr.length, arr.toArray().length);
    arr.insert(2, [2]);
    t.is(arr.length, arr.toArray().length);
  });
  t.is(arr.length, arr.toArray().length);
  arr.delete(1);
  t.is(arr.length, arr.toArray().length);
  arr.insert(1, [1]);
  t.is(arr.length, arr.toArray().length);
});

/**
 * Debugging yjs#314
 */
test("testLengthIssue2", (t) => {
  const doc = new Y.Doc();
  const next = doc.createArray();
  doc.transact(() => {
    next.insert(0, ["group2"]);
  });
  doc.transact(() => {
    next.insert(1, ["rectangle3"]);
  });
  doc.transact(() => {
    next.delete(0);
    next.insert(0, ["rectangle3"]);
  });
  next.delete(1);
  doc.transact(() => {
    next.insert(1, ["ellipse4"]);
  });
  doc.transact(() => {
    next.insert(2, ["ellipse3"]);
  });
  doc.transact(() => {
    next.insert(3, ["ellipse2"]);
  });
  doc.transact(() => {
    doc.transact(() => {
      t.throws(() => {
        next.insert(5, ["rectangle2"]);
      });
      next.insert(4, ["rectangle2"]);
    });
    doc.transact(() => {
      // this should not throw an error message
      next.delete(4);
    });
  });
  console.log(next.toArray());
});

test.skip("testDeleteInsert", (t) => {
  const { users, array0 } = init(gen, { users: 2 });

  array0.delete(0, 0);
  t.notThrows(() => {
    array0.delete(1, 1);
  }, "Does not throw when deleting zero elements with position 0");
  array0.insert(0, ["A"]);
  t.notThrows(() => {
    array0.delete(1, 0);
  }, "Does not throw when deleting zero elements with valid position 1");
  compare(users);
});

// TODO: impl sync protocol encode in rust
test.skip("testInsertThreeElementsTryRegetProperty", (t) => {
  const { testConnector, users, array0, array1 } = init(gen, { users: 2 });

  array0.insert(0, [1, true, false]);
  t.deepEqual(array0.toJSON(), [1, true, false], ".toJSON() works");
  testConnector.flushAllMessages();
  t.deepEqual(array1.toJSON(), [1, true, false], ".toJSON() works after sync");
  compare(users);
});

test.skip("testConcurrentInsertWithThreeConflicts", (t) => {
  const { users, array0, array1, array2 } = init(gen, { users: 3 });

  array0.insert(0, [0]);
  array1.insert(0, [1]);
  array2.insert(0, [2]);
  compare(users);
});

test.skip("testConcurrentInsertDeleteWithThreeConflicts", (t) => {
  const { testConnector, users, array0, array1, array2 } = init(gen, {
    users: 3,
  });

  array0.insert(0, ["x", "y", "z"]);
  testConnector.flushAllMessages();
  array0.insert(1, [0]);
  array1.delete(0);
  array1.delete(1, 1);
  array2.insert(1, [2]);
  compare(users);
});

test.skip("testInsertionsInLateSync", (t) => {
  const { testConnector, users, array0, array1, array2 } = init(gen, {
    users: 3,
  });

  array0.insert(0, ["x", "y"]);
  testConnector.flushAllMessages();
  users[1].disconnect();
  users[2].disconnect();
  array0.insert(1, ["user0"]);
  array1.insert(1, ["user1"]);
  array2.insert(1, ["user2"]);
  users[1].connect();
  users[2].connect();
  testConnector.flushAllMessages();
  compare(users);
});

test.skip("testDisconnectReallyPreventsSendingMessages", (t) => {
  const { testConnector, users, array0, array1 } = init(gen, { users: 3 });

  array0.insert(0, ["x", "y"]);
  testConnector.flushAllMessages();
  users[1].disconnect();
  users[2].disconnect();
  array0.insert(1, ["user0"]);
  array1.insert(1, ["user1"]);
  t.deepEqual(array0.toJSON(), ["x", "user0", "y"]);
  t.deepEqual(array1.toJSON(), ["x", "user1", "y"]);
  users[1].connect();
  users[2].connect();
  compare(users);
});

test.skip("testDeletionsInLateSync", (t) => {
  const { testConnector, users, array0, array1 } = init(gen, { users: 2 });

  array0.insert(0, ["x", "y"]);
  testConnector.flushAllMessages();
  users[1].disconnect();
  array1.delete(1, 1);
  array0.delete(0, 2);
  users[1].connect();
  compare(users);
});

test.skip("testInsertThenMergeDeleteOnSync", (t) => {
  const { testConnector, users, array0, array1 } = init(gen, { users: 2 });

  array0.insert(0, ["x", "y", "z"]);
  testConnector.flushAllMessages();
  users[0].disconnect();
  array1.delete(0, 3);
  users[0].connect();
  compare(users);
});

test.skip("testInsertAndDeleteEvents", (t) => {
  const { array0, users } = init(gen, { users: 2 });

  let event: Record<string, any> | null = null;
  array0.observe((e) => {
    event = e;
  });
  array0.insert(0, [0, 1, 2]);
  assert(event !== null);
  event = null;
  array0.delete(0);
  assert(event !== null);
  event = null;
  array0.delete(0, 2);
  assert(event !== null);
  event = null;
  compare(users);
});

test.skip("testNestedObserverEvents", (t) => {
  const { array0, users } = init(gen, { users: 2 });

  const vals: number[] = [];
  array0.observe((e) => {
    if (array0.length === 1) {
      // inserting, will call this observer again
      // we expect that this observer is called after this event handler finishedn
      array0.insert(1, [1]);
      vals.push(0);
    } else {
      // this should be called the second time an element is inserted (above case)
      vals.push(1);
    }
  });
  array0.insert(0, [0]);
  t.deepEqual(vals, [0, 1]);
  t.deepEqual(array0.toArray(), [0, 1]);
  compare(users);
});

test.skip("testInsertAndDeleteEventsForTypes", (t) => {
  const { array0, users } = init(gen, { users: 2 });

  let event: Record<string, any> | null = null;
  array0.observe((e) => {
    event = e;
  });
  array0.insert(0, [new Y.Array()]);
  assert(event !== null);
  event = null;
  array0.delete(0);
  assert(event !== null);
  event = null;
  compare(users);
});

/**
 * This issue has been reported in https://discuss.yjs.dev/t/order-in-which-events-yielded-by-observedeep-should-be-applied/261/2
 *
 * Deep observers generate multiple events. When an array added at item at, say, position 0,
 * and item 1 changed then the array-add event should fire first so that the change event
 * path is correct. A array binding might lead to an inconsistent state otherwise.
 */
test.skip("testObserveDeepEventOrder", (t) => {
  const { array0, users } = init(gen, { users: 2 });

  let events: any[] = [];
  array0.observeDeep((e) => {
    events = e;
  });
  array0.insert(0, [new Y.Map()]);
  users[0].transact(() => {
    array0.get<Y.Map>(0).set("a", "a");
    array0.insert(0, [0]);
  });
  for (let i = 1; i < events.length; i++) {
    assert(
      events[i - 1].path.length <= events[i].path.length,
      "path size increases, fire top-level events first",
    );
  }
});

/**
 * Correct index when computing event.path in observeDeep - https://github.com/yjs/yjs/issues/457
 */
test.skip("testObservedeepIndexes", (t) => {
  const doc = new Y.Doc();
  const map = doc.createMap();
  // Create a field with the array as value
  map.set("my-array", new Y.Array());
  // Fill the array with some strings and our Map
  map.get<Y.Array>("my-array").push(["a", "b", "c", new Y.Map()]);
  let eventPath: any[] = [];
  map.observeDeep((events) => {
    eventPath = events[0].path;
  });
  // set a value on the map inside of our array
  map.get<Y.Array>("my-array").get<Y.Map>(3).set("hello", "world");
  console.log(eventPath);
  t.deepEqual(eventPath, ["my-array", 3]);
});

test.skip("testChangeEvent", (t) => {
  const { array0, users } = init(gen, { users: 2 });

  let changes: any = null;
  array0.observe((e) => {
    changes = e.changes;
  });
  const newArr = new Y.Array();
  array0.insert(0, [newArr, 4, "dtrn"]);
  assert(
    changes !== null && changes.added.size === 2 && changes.deleted.size === 0,
  );
  t.deepEqual(changes.delta, [{ insert: [newArr, 4, "dtrn"] }]);
  changes = null;
  array0.delete(0, 2);
  assert(
    changes !== null && changes.added.size === 0 && changes.deleted.size === 2,
  );
  t.deepEqual(changes.delta, [{ delete: 2 }]);
  changes = null;
  array0.insert(1, [0.1]);
  assert(
    changes !== null && changes.added.size === 1 && changes.deleted.size === 0,
  );
  t.deepEqual(changes.delta, [{ retain: 1 }, { insert: [0.1] }]);
  compare(users);
});

test.skip("testInsertAndDeleteEventsForTypes2", (t) => {
  const { array0, users } = init(gen, { users: 2 });

  const events: Record<string, any>[] = [];
  array0.observe((e) => {
    events.push(e);
  });
  array0.insert(0, ["hi", new Y.Map()]);
  t.is(
    events.length,
    1,
    "Event is triggered exactly once for insertion of two elements",
  );
  array0.delete(1);
  t.is(events.length, 2, "Event is triggered exactly once for deletion");
  compare(users);
});

/**
 * This issue has been reported here https://github.com/yjs/yjs/issues/155
 */
test.skip("testNewChildDoesNotEmitEventInTransaction", (t) => {
  const { array0, users } = init(gen, { users: 2 });

  let fired = false;
  users[0].transact(() => {
    const newMap = new Y.Map();
    newMap.observe(() => {
      fired = true;
    });
    array0.insert(0, [newMap]);
    newMap.set("tst", 42);
  });
  assert(!fired, "Event does not trigger");
});

test.skip("testGarbageCollector", (t) => {
  const { testConnector, users, array0 } = init(gen, { users: 3 });

  array0.insert(0, ["x", "y", "z"]);
  testConnector.flushAllMessages();
  users[0].disconnect();
  array0.delete(0, 3);
  users[0].connect();
  testConnector.flushAllMessages();
  compare(users);
});

test.skip("testEventTargetIsSetCorrectlyOnLocal", (t) => {
  const { array0, users } = init(gen, { users: 3 });

  let event: any;
  array0.observe((e) => {
    event = e;
  });
  array0.insert(0, ["stuff"]);
  assert(event.target === array0, '"target" property is set correctly');
  compare(users);
});

test.skip("testEventTargetIsSetCorrectlyOnRemote", (t) => {
  const { testConnector, array0, array1, users } = init(gen, { users: 3 });

  let event: any;
  array0.observe((e) => {
    event = e;
  });
  array1.insert(0, ["stuff"]);
  testConnector.flushAllMessages();
  assert(event.target === array0, '"target" property is set correctly');
  compare(users);
});

test("testIteratingArrayContainingTypes", (t) => {
  const y = new Y.Doc();
  const arr = y.getOrCreateArray("arr");
  const numItems = 10;
  for (let i = 0; i < numItems; i++) {
    const map = y.createMap();
    map.set("value", i);
    arr.push([map]);
  }
  t.is(arr.length, numItems, "array length mot correct");
  let cnt = 0;
  for (const item of arr.iter()) {
    t.is(item.get("value"), cnt++, "value is correct");
  }
  // y.destroy();
});

let _uniqueNumber = 0;
const getUniqueNumber = () => _uniqueNumber++;

const arrayTransactions: Array<
  (arg0: Y.Doc, arg1: prng.PRNG, arg2: any) => void
> = [
  function insert(user: Y.Doc, gen: prng.PRNG) {
    const yarray = user.getOrCreateArray("array");
    const uniqueNumber = getUniqueNumber();
    const content: number[] = [];
    const len = prng.int32(gen, 1, 4);
    for (let i = 0; i < len; i++) {
      content.push(uniqueNumber);
    }
    const pos = prng.int32(gen, 0, yarray.length);
    const oldContent = yarray.toArray();
    yarray.insert(pos, content);
    oldContent.splice(pos, 0, ...content);
    deepEqual(yarray.toArray(), oldContent); // we want to make sure that fastSearch markers insert at the correct position
  },
  function insertTypeArray(user: Y.Doc, gen: prng.PRNG) {
    const yarray = user.getOrCreateArray("array");
    const pos = prng.int32(gen, 0, yarray.length);
    yarray.insert(pos, [user.createArray()]);
    const array2 = yarray.get<Y.Array>(pos);
    array2.insert(0, [1, 2, 3, 4]);
  },
  function insertTypeMap(user: Y.Doc, gen: prng.PRNG) {
    const yarray = user.getOrCreateArray("array");
    const pos = prng.int32(gen, 0, yarray.length);
    yarray.insert(pos, [user.createMap()]);
    const map = yarray.get<Y.Map>(pos);
    map.set("someprop", 42);
    map.set("someprop", 43);
    map.set("someprop", 44);
  },
  function insertTypeNull(user: Y.Doc, gen: prng.PRNG) {
    const yarray = user.getOrCreateArray("array");
    const pos = prng.int32(gen, 0, yarray.length);
    yarray.insert(pos, [null]);
  },
  function _delete(user: Y.Doc, gen: prng.PRNG) {
    const yarray = user.getOrCreateArray("array");
    const length = yarray.length;
    if (length > 0) {
      let somePos = prng.int32(gen, 0, length - 1);
      let delLength = prng.int32(gen, 1, math.min(2, length - somePos));
      if (prng.bool(gen)) {
        const type = yarray.get(somePos);
        if (type instanceof Y.Array && type.length > 0) {
          somePos = prng.int32(gen, 0, type.length - 1);
          delLength = prng.int32(gen, 0, math.min(2, type.length - somePos));
          type.delete(somePos, delLength);
        }
      } else {
        const oldContent = yarray.toArray();
        yarray.delete(somePos, delLength);
        oldContent.splice(somePos, delLength);
        deepEqual(yarray.toArray(), oldContent);
      }
    }
  },
];

test.skip("testRepeatGeneratingYarrayTests6", (t) => {
  applyRandomTests(gen, arrayTransactions, 6);
});

test.skip("testRepeatGeneratingYarrayTests40", (t) => {
  applyRandomTests(gen, arrayTransactions, 40);
});

test.skip("testRepeatGeneratingYarrayTests42", (t) => {
  applyRandomTests(gen, arrayTransactions, 42);
});

test.skip("testRepeatGeneratingYarrayTests43", (t) => {
  applyRandomTests(gen, arrayTransactions, 43);
});

test.skip("testRepeatGeneratingYarrayTests44", (t) => {
  applyRandomTests(gen, arrayTransactions, 44);
});

test.skip("testRepeatGeneratingYarrayTests45", (t) => {
  applyRandomTests(gen, arrayTransactions, 45);
});

test.skip("testRepeatGeneratingYarrayTests46", (t) => {
  applyRandomTests(gen, arrayTransactions, 46);
});

test.skip("testRepeatGeneratingYarrayTests300", (t) => {
  applyRandomTests(gen, arrayTransactions, 300);
});

test.skip("testRepeatGeneratingYarrayTests400", (t) => {
  applyRandomTests(gen, arrayTransactions, 400);
});

test.skip("testRepeatGeneratingYarrayTests500", (t) => {
  applyRandomTests(gen, arrayTransactions, 500);
});

test.skip("testRepeatGeneratingYarrayTests600", (t) => {
  applyRandomTests(gen, arrayTransactions, 600);
});

test.skip("testRepeatGeneratingYarrayTests1000", (t) => {
  applyRandomTests(gen, arrayTransactions, 1000);
});

test.skip("testRepeatGeneratingYarrayTests1800", (t) => {
  applyRandomTests(gen, arrayTransactions, 1800);
});

test.skip("testRepeatGeneratingYarrayTests3000", (t) => {
  if (!production) return;
  applyRandomTests(gen, arrayTransactions, 3000);
});

test.skip("testRepeatGeneratingYarrayTests5000", (t) => {
  if (!production) return;
  applyRandomTests(gen, arrayTransactions, 5000);
});

test.skip("testRepeatGeneratingYarrayTests30000", (t) => {
  if (!production) return;
  applyRandomTests(gen, arrayTransactions, 30000);
});
