import { init, compare, applyRandomTests } from "./testHelper.js"; // eslint-disable-line

import * as Y from "../../index.js";
import * as t from "lib0/testing";
import * as prng from "lib0/prng";
import * as math from "lib0/math";

export const testBasicUpdate = (tc: t.TestCase) => {
  const doc1 = new Y.Doc();
  const doc2 = new Y.Doc();
  doc1.getOrCreateArray("array").insert(0, ["hi"]);
  const update = Y.encodeStateAsUpdate(doc1);
  Y.applyUpdate(doc2, update);
  t.compare(doc2.getOrCreateArray("array").toArray(), ["hi"]);
};

export const testSlice = (tc: t.TestCase) => {
  const doc1 = new Y.Doc();
  const arr = doc1.getOrCreateArray("array");
  arr.insert(0, [1, 2, 3]);
  t.compareArrays(arr.slice(0), [1, 2, 3]);
  t.compareArrays(arr.slice(1), [2, 3]);
  t.compareArrays(arr.slice(0, -1), [1, 2]);
  arr.insert(0, [0]);
  t.compareArrays(arr.slice(0), [0, 1, 2, 3]);
  t.compareArrays(arr.slice(0, 2), [0, 1]);
};

/**
 * @param {t.TestCase} tc
 */
export const testArrayFrom = (tc: t.TestCase) => {
  const doc1 = new Y.Doc();
  const db1 = doc1.getOrCreateMap("root");
  const nestedArray1 = Y.Array.from([0, 1, 2]);
  db1.set("array", nestedArray1);
  t.compare(nestedArray1.toArray(), [0, 1, 2]);
};

/**
 * Debugging yjs#297 - a critical bug connected to the search-marker approach
 */
export const testLengthIssue = (tc: t.TestCase) => {
  const doc1 = new Y.Doc();
  const arr = doc1.getOrCreateArray("array");
  arr.push([0, 1, 2, 3]);
  arr.delete(0);
  arr.insert(0, [0]);
  t.assert(arr.length === arr.toArray().length);
  doc1.transact(() => {
    arr.delete(1);
    t.assert(arr.length === arr.toArray().length);
    arr.insert(1, [1]);
    t.assert(arr.length === arr.toArray().length);
    arr.delete(2);
    t.assert(arr.length === arr.toArray().length);
    arr.insert(2, [2]);
    t.assert(arr.length === arr.toArray().length);
  });
  t.assert(arr.length === arr.toArray().length);
  arr.delete(1);
  t.assert(arr.length === arr.toArray().length);
  arr.insert(1, [1]);
  t.assert(arr.length === arr.toArray().length);
};

/**
 * Debugging yjs#314
 */
export const testLengthIssue2 = (tc: t.TestCase) => {
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
      t.fails(() => {
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
};

export const testDeleteInsert = (tc: t.TestCase) => {
  const { users, array0 } = init(tc, { users: 2 });
  t.assert(array0);
  array0.delete(0, 0);
  t.describe("Does not throw when deleting zero elements with position 0");
  t.fails(() => {
    array0.delete(1, 1);
  });
  array0.insert(0, ["A"]);
  array0.delete(1, 0);
  t.describe(
    "Does not throw when deleting zero elements with valid position 1",
  );
  compare(users);
};

export const testInsertThreeElementsTryRegetProperty = (tc: t.TestCase) => {
  const { testConnector, users, array0, array1 } = init(tc, { users: 2 });
  t.assert(array0);
  t.assert(array1);
  array0.insert(0, [1, true, false]);
  t.compare(array0.toJSON(), [1, true, false], ".toJSON() works");
  testConnector.flushAllMessages();
  t.compare(array1.toJSON(), [1, true, false], ".toJSON() works after sync");
  compare(users);
};

export const testConcurrentInsertWithThreeConflicts = (tc: t.TestCase) => {
  const { users, array0, array1, array2 } = init(tc, { users: 3 });
  t.assert(array0);
  t.assert(array1);
  t.assert(array2);
  array0.insert(0, [0]);
  array1.insert(0, [1]);
  array2.insert(0, [2]);
  compare(users);
};

export const testConcurrentInsertDeleteWithThreeConflicts = (
  tc: t.TestCase,
) => {
  const { testConnector, users, array0, array1, array2 } = init(tc, {
    users: 3,
  });
  t.assert(array0);
  t.assert(array1);
  t.assert(array2);
  array0.insert(0, ["x", "y", "z"]);
  testConnector.flushAllMessages();
  array0.insert(1, [0]);
  array1.delete(0);
  array1.delete(1, 1);
  array2.insert(1, [2]);
  compare(users);
};

export const testInsertionsInLateSync = (tc: t.TestCase) => {
  const { testConnector, users, array0, array1, array2 } = init(tc, {
    users: 3,
  });
  t.assert(array0);
  t.assert(array1);
  t.assert(array2);
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
};

export const testDisconnectReallyPreventsSendingMessages = (tc: t.TestCase) => {
  const { testConnector, users, array0, array1 } = init(tc, { users: 3 });
  t.assert(array0);
  t.assert(array1);
  array0.insert(0, ["x", "y"]);
  testConnector.flushAllMessages();
  users[1].disconnect();
  users[2].disconnect();
  array0.insert(1, ["user0"]);
  array1.insert(1, ["user1"]);
  t.compare(array0.toJSON(), ["x", "user0", "y"]);
  t.compare(array1.toJSON(), ["x", "user1", "y"]);
  users[1].connect();
  users[2].connect();
  compare(users);
};

export const testDeletionsInLateSync = (tc: t.TestCase) => {
  const { testConnector, users, array0, array1 } = init(tc, { users: 2 });
  t.assert(array0);
  t.assert(array1);
  array0.insert(0, ["x", "y"]);
  testConnector.flushAllMessages();
  users[1].disconnect();
  array1.delete(1, 1);
  array0.delete(0, 2);
  users[1].connect();
  compare(users);
};

export const testInsertThenMergeDeleteOnSync = (tc: t.TestCase) => {
  const { testConnector, users, array0, array1 } = init(tc, { users: 2 });
  t.assert(array0);
  t.assert(array1);
  array0.insert(0, ["x", "y", "z"]);
  testConnector.flushAllMessages();
  users[0].disconnect();
  array1.delete(0, 3);
  users[0].connect();
  compare(users);
};

export const testInsertAndDeleteEvents = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 2 });
  t.assert(array0);
  let event: Record<string, any> | null = null;
  array0.observe((e) => {
    event = e;
  });
  array0.insert(0, [0, 1, 2]);
  t.assert(event !== null);
  event = null;
  array0.delete(0);
  t.assert(event !== null);
  event = null;
  array0.delete(0, 2);
  t.assert(event !== null);
  event = null;
  compare(users);
};

export const testNestedObserverEvents = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 2 });
  t.assert(array0);
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
  t.compareArrays(vals, [0, 1]);
  t.compareArrays(array0.toArray(), [0, 1]);
  compare(users);
};

export const testInsertAndDeleteEventsForTypes = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 2 });
  t.assert(array0);
  let event: Record<string, any> | null = null;
  array0.observe((e) => {
    event = e;
  });
  array0.insert(0, [new Y.Array()]);
  t.assert(event !== null);
  event = null;
  array0.delete(0);
  t.assert(event !== null);
  event = null;
  compare(users);
};

/**
 * This issue has been reported in https://discuss.yjs.dev/t/order-in-which-events-yielded-by-observedeep-should-be-applied/261/2
 *
 * Deep observers generate multiple events. When an array added at item at, say, position 0,
 * and item 1 changed then the array-add event should fire first so that the change event
 * path is correct. A array binding might lead to an inconsistent state otherwise.
 */
export const testObserveDeepEventOrder = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 2 });
  t.assert(array0);
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
    t.assert(
      events[i - 1].path.length <= events[i].path.length,
      "path size increases, fire top-level events first",
    );
  }
};

/**
 * Correct index when computing event.path in observeDeep - https://github.com/yjs/yjs/issues/457
 */
export const testObservedeepIndexes = (_tc: t.TestCase) => {
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
  t.compare(eventPath, ["my-array", 3]);
};

export const testChangeEvent = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 2 });
  t.assert(array0);
  let changes: any = null;
  array0.observe((e) => {
    changes = e.changes;
  });
  const newArr = new Y.Array();
  array0.insert(0, [newArr, 4, "dtrn"]);
  t.assert(
    changes !== null && changes.added.size === 2 && changes.deleted.size === 0,
  );
  t.compare(changes.delta, [{ insert: [newArr, 4, "dtrn"] }]);
  changes = null;
  array0.delete(0, 2);
  t.assert(
    changes !== null && changes.added.size === 0 && changes.deleted.size === 2,
  );
  t.compare(changes.delta, [{ delete: 2 }]);
  changes = null;
  array0.insert(1, [0.1]);
  t.assert(
    changes !== null && changes.added.size === 1 && changes.deleted.size === 0,
  );
  t.compare(changes.delta, [{ retain: 1 }, { insert: [0.1] }]);
  compare(users);
};

export const testInsertAndDeleteEventsForTypes2 = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 2 });
  t.assert(array0);
  const events: Record<string, any>[] = [];
  array0.observe((e) => {
    events.push(e);
  });
  array0.insert(0, ["hi", new Y.Map()]);
  t.assert(
    events.length === 1,
    "Event is triggered exactly once for insertion of two elements",
  );
  array0.delete(1);
  t.assert(events.length === 2, "Event is triggered exactly once for deletion");
  compare(users);
};

/**
 * This issue has been reported here https://github.com/yjs/yjs/issues/155
 * @param {t.TestCase} tc
 */
export const testNewChildDoesNotEmitEventInTransaction = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 2 });
  t.assert(array0);
  let fired = false;
  users[0].transact(() => {
    const newMap = new Y.Map();
    newMap.observe(() => {
      fired = true;
    });
    array0.insert(0, [newMap]);
    newMap.set("tst", 42);
  });
  t.assert(!fired, "Event does not trigger");
};

export const testGarbageCollector = (tc: t.TestCase) => {
  const { testConnector, users, array0 } = init(tc, { users: 3 });
  t.assert(array0);
  array0.insert(0, ["x", "y", "z"]);
  testConnector.flushAllMessages();
  users[0].disconnect();
  array0.delete(0, 3);
  users[0].connect();
  testConnector.flushAllMessages();
  compare(users);
};

/**
 * @param {t.TestCase} tc
 */
export const testEventTargetIsSetCorrectlyOnLocal = (tc: t.TestCase) => {
  const { array0, users } = init(tc, { users: 3 });
  t.assert(array0);
  let event: any;
  array0.observe((e) => {
    event = e;
  });
  array0.insert(0, ["stuff"]);
  t.assert(event.target === array0, '"target" property is set correctly');
  compare(users);
};

export const testEventTargetIsSetCorrectlyOnRemote = (tc: t.TestCase) => {
  const { testConnector, array0, array1, users } = init(tc, { users: 3 });
  t.assert(array0);
  t.assert(array1);
  let event: any;
  array0.observe((e) => {
    event = e;
  });
  array1.insert(0, ["stuff"]);
  testConnector.flushAllMessages();
  t.assert(event.target === array0, '"target" property is set correctly');
  compare(users);
};

export const testIteratingArrayContainingTypes = (tc: t.TestCase) => {
  const y = new Y.Doc();
  const arr = y.getOrCreateArray("arr");
  const numItems = 10;
  for (let i = 0; i < numItems; i++) {
    const map = new Y.Map();
    map.set("value", i);
    arr.push([map]);
  }
  let cnt = 0;
  for (const item of arr.iter()) {
    t.assert(item.get("value") === cnt++, "value is correct");
  }
  y.destroy();
};

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
    t.compareArrays(yarray.toArray(), oldContent); // we want to make sure that fastSearch markers insert at the correct position
  },
  function insertTypeArray(user: Y.Doc, gen: prng.PRNG) {
    const yarray = user.getOrCreateArray("array");
    const pos = prng.int32(gen, 0, yarray.length);
    yarray.insert(pos, [new Y.Array()]);
    const array2 = yarray.get<Y.Array>(pos);
    array2.insert(0, [1, 2, 3, 4]);
  },
  function insertTypeMap(user: Y.Doc, gen: prng.PRNG) {
    const yarray = user.getOrCreateArray("array");
    const pos = prng.int32(gen, 0, yarray.length);
    yarray.insert(pos, [new Y.Map()]);
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
        t.compareArrays(yarray.toArray(), oldContent);
      }
    }
  },
];

/**
 * @param {t.TestCase} tc
 */
export const testRepeatGeneratingYarrayTests6 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 6);
};

export const testRepeatGeneratingYarrayTests40 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 40);
};

export const testRepeatGeneratingYarrayTests42 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 42);
};

export const testRepeatGeneratingYarrayTests43 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 43);
};

export const testRepeatGeneratingYarrayTests44 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 44);
};

export const testRepeatGeneratingYarrayTests45 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 45);
};

export const testRepeatGeneratingYarrayTests46 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 46);
};

export const testRepeatGeneratingYarrayTests300 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 300);
};

export const testRepeatGeneratingYarrayTests400 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 400);
};

export const testRepeatGeneratingYarrayTests500 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 500);
};

export const testRepeatGeneratingYarrayTests600 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 600);
};

export const testRepeatGeneratingYarrayTests1000 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 1000);
};

export const testRepeatGeneratingYarrayTests1800 = (tc: t.TestCase) => {
  applyRandomTests(tc, arrayTransactions, 1800);
};

export const testRepeatGeneratingYarrayTests3000 = (tc: t.TestCase) => {
  t.skip(!t.production);
  applyRandomTests(tc, arrayTransactions, 3000);
};

export const testRepeatGeneratingYarrayTests5000 = (tc: t.TestCase) => {
  t.skip(!t.production);
  applyRandomTests(tc, arrayTransactions, 5000);
};

export const testRepeatGeneratingYarrayTests30000 = (tc: t.TestCase) => {
  t.skip(!t.production);
  applyRandomTests(tc, arrayTransactions, 30000);
};
