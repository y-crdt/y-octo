import test from "ava";

import * as YOcto from "@y-octo/node";
import * as Y from "yjs";

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

test("doc id should be set", (t) => {
  t.is(doc.clientId, client_id);
});

test("y-octo doc update should be apply", (t) => {
  let array = doc.getOrCreateArray("array");
  let map = doc.getOrCreateMap("map");
  let text = doc.getOrCreateText("text");

  array.insert(0, true);
  array.insert(1, false);
  array.insert(2, 1);
  array.insert(3, "hello world");
  map.set("a", true);
  map.set("b", false);
  map.set("c", 1);
  map.set("d", "hello world");
  text.insert(0, "a");
  text.insert(1, "b");
  text.insert(2, "c");

  let doc2 = new YOcto.Doc(client_id);
  doc2.applyUpdate(doc.encodeStateAsUpdateV1());

  let array2 = doc2.getOrCreateArray("array");
  let map2 = doc2.getOrCreateMap("map");
  let text2 = doc2.getOrCreateText("text");

  // after apply update that include same client id's change
  // the client id should be changed
  t.not(doc2.clientId, client_id);
  t.is(array2.length, 4);
  t.is(array2.get(0), true);
  t.is(array2.get(1), false);
  t.is(array2.get(2), 1);
  t.is(array2.get(3), "hello world");
  t.is(map2.length, 4);
  t.is(map2.get("a"), true);
  t.is(map2.get("b"), false);
  t.is(map2.get("c"), 1);
  t.is(map2.get("d"), "hello world");
  t.is(text2.toString(), "abc");
});

test("yjs doc update should be apply", (t) => {
  let doc2 = new Y.Doc();
  let array2 = doc2.getArray("array");
  let map2 = doc2.getMap("map");
  let text2 = doc2.getText("text");

  array2.insert(0, [true]);
  array2.insert(1, [false]);
  array2.insert(2, [1]);
  array2.insert(3, ["hello world"]);
  map2.set("a", true);
  map2.set("b", false);
  map2.set("c", 1);
  map2.set("d", "hello world");
  text2.insert(0, "a");
  text2.insert(1, "b");
  text2.insert(2, "c");

  doc.applyUpdate(Buffer.from(Y.encodeStateAsUpdate(doc2)));

  let array = doc.getOrCreateArray("array");
  let map = doc.getOrCreateMap("map");
  let text = doc.getOrCreateText("text");

  t.is(array.length, 4);
  t.is(array.get(0), true);
  t.is(array.get(1), false);
  t.is(array.get(2), 1);
  t.is(array.get(3), "hello world");
  t.is(map.length, 4);
  t.is(map.get("a"), true);
  t.is(map.get("b"), false);
  t.is(map.get("c"), 1);
  t.is(map.get("d"), "hello world");
  t.is(text.toString(), "abc");
});
