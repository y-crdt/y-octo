import assert, { equal, deepEqual } from "node:assert";
import { test } from "node:test";

import * as YOcto from "../yocto";

test("array test", { concurrency: false }, async (t) => {
  let client_id: number;
  let doc: YOcto.Doc;
  t.beforeEach(async () => {
    client_id = (Math.random() * 100000) | 0;
    doc = new YOcto.Doc(client_id);
  });

  t.afterEach(async () => {
    client_id = -1;
    // @ts-ignore - doc must not null in next range
    doc = null;
  });

  await t.test("array should be created", () => {
    let arr = doc.getOrCreateArray("arr");
    deepEqual(doc.keys, ["arr"]);
    equal(arr.length, 0);
  });

  await t.test("array editing", () => {
    let arr = doc.getOrCreateArray("arr");
    arr.insert(0, true);
    arr.insert(1, false);
    arr.insert(2, 1);
    arr.insert(3, "hello world");
    equal(arr.length, 4);
    equal(arr.get(0), true);
    equal(arr.get(1), false);
    equal(arr.get(2), 1);
    equal(arr.get(3), "hello world");
    equal(arr.length, 4);
    arr.delete(1, 1);
    equal(arr.length, 3);
    equal(arr.get(2), "hello world");
    deepEqual(arr.slice(1, 3), [1, "hello world"]);
    deepEqual(
      arr.map((v) => v),
      [true, 1, "hello world"],
    );
  });

  await t.test("sub array should can edit", () => {
    let map = doc.getOrCreateMap("map");
    let sub = doc.createArray();
    map.set("sub", sub);

    sub.insert(0, true);
    sub.insert(1, false);
    sub.insert(2, 1);
    sub.insert(3, "hello world");
    equal(sub.length, 4);

    let sub2 = map.get<YOcto.Array>("sub");
    assert(sub2);
    equal(sub2.get(0), true);
    equal(sub2.get(1), false);
    equal(sub2.get(2), 1);
    equal(sub2.get(3), "hello world");
    equal(sub2.length, 4);
    deepEqual(sub2.slice(1, 3), [false, 1]);
    deepEqual(
      sub2.map((v) => v),
      [true, false, 1, "hello world"],
    );
  });

  await t.test("array should support iterator", () => {
    let arr = doc.getOrCreateArray("arr");
    arr.insert(0, true);
    arr.insert(1, false);
    arr.insert(2, 1);
    arr.insert(3, "hello world");
    let i = 0;
    for (let v of arr.iter()) {
      switch (i) {
        case 0:
          equal(v, true);
          break;
        case 1:
          equal(v, false);
          break;
        case 2:
          equal(v, 1);
          break;
        case 3:
          equal(v, "hello world");
          break;
      }
      i++;
    }
  });
});
