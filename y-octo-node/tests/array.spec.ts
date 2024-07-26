import test from "ava";

import * as YOcto from "../yocto";

let client_id: number;
let doc: YOcto.Doc;
test.beforeEach(async () => {
  client_id = (Math.random() * 100000) | 0;
  doc = new YOcto.Doc(client_id);
});

test.afterEach(async () => {
  client_id = -1;
  // @ts-ignore - doc must not null in next range
  doc = null;
});

test("array should be created", (t) => {
  let arr = doc.getOrCreateArray("arr");
  t.deepEqual(doc.keys, ["arr"]);
  t.is(arr.length, 0);
});

test("array editing", (t) => {
  let arr = doc.getOrCreateArray("arr");
  arr.insert(0, true);
  arr.insert(1, false);
  arr.insert(2, 1);
  arr.insert(3, "hello world");
  t.is(arr.length, 4);
  t.is(arr.get(0), true);
  t.is(arr.get(1), false);
  t.is(arr.get(2), 1);
  t.is(arr.get(3), "hello world");
  t.is(arr.length, 4);
  arr.delete(1, 1);
  t.is(arr.length, 3);
  t.is(arr.get(2), "hello world");
  t.deepEqual(arr.slice(1, 3), [1, "hello world"]);
  t.deepEqual(
    arr.map((v) => v),
    [true, 1, "hello world"],
  );
});

test("sub array should can edit", (t) => {
  let map = doc.getOrCreateMap("map");
  let sub = doc.createArray();
  map.set("sub", sub);

  sub.insert(0, true);
  sub.insert(1, false);
  sub.insert(2, 1);
  sub.insert(3, "hello world");
  t.is(sub.length, 4);

  let sub2 = map.get<YOcto.Array>("sub");
  t.assert(sub2);
  t.is(sub2.get(0), true);
  t.is(sub2.get(1), false);
  t.is(sub2.get(2), 1);
  t.is(sub2.get(3), "hello world");
  t.is(sub2.length, 4);
  t.deepEqual(sub2.slice(1, 3), [false, 1]);
  t.deepEqual(
    sub2.map((v) => v),
    [true, false, 1, "hello world"],
  );
});

test("array should support iterator", (t) => {
  let arr = doc.getOrCreateArray("arr");
  arr.insert(0, true);
  arr.insert(1, false);
  arr.insert(2, 1);
  arr.insert(3, "hello world");
  let i = 0;
  for (let v of arr.iter()) {
    switch (i) {
      case 0:
        t.is(v, true);
        break;
      case 1:
        t.is(v, false);
        break;
      case 2:
        t.is(v, 1);
        break;
      case 3:
        t.is(v, "hello world");
        break;
    }
    i++;
  }
});
