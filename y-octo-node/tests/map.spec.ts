import test from "ava";

import * as Y from "yjs";
import * as YOcto from "@y-octo/node";

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

test("map should be created", (t) => {
  let map = doc.getOrCreateMap("map");
  t.deepEqual(doc.keys, ["map"]);
  t.is(map.length, 0);
});

test("map editing", (t) => {
  let map = doc.getOrCreateMap("map");
  map.set("a", true);
  map.set("b", false);
  map.set("c", 1);
  map.set("d", "hello world");
  t.is(map.length, 4);
  t.is(map.get("a"), true);
  t.is(map.get("b"), false);
  t.is(map.get("c"), 1);
  t.is(map.get("d"), "hello world");
  t.is(map.length, 4);
  map.delete("b");
  t.is(map.length, 3);
  t.is(map.get("d"), "hello world");
});

test("map should can be nested", (t) => {
  let map = doc.getOrCreateMap("map");
  let sub = doc.createMap();
  map.set("sub", sub);

  sub.set("a", true);
  sub.set("b", false);
  sub.set("c", 1);
  sub.set("d", "hello world");
  t.is(sub.length, 4);

  let sub2 = map.get<YOcto.Map>("sub");
  t.assert(sub2);
  t.is(sub2.get("a"), true);
  t.is(sub2.get("b"), false);
  t.is(sub2.get("c"), 1);
  t.is(sub2.get("d"), "hello world");
  t.is(sub2.length, 4);
});

test("y-octo to yjs compatibility test with nested type", (t) => {
  let map = doc.getOrCreateMap("map");
  let sub_array = doc.createArray();
  let sub_map = doc.createMap();
  let sub_text = doc.createText();

  map.set("array", sub_array);
  map.set("map", sub_map);
  map.set("text", sub_text);

  sub_array.insert(0, true);
  sub_array.insert(1, false);
  sub_array.insert(2, 1);
  sub_array.insert(3, "hello world");
  sub_map.set("a", true);
  sub_map.set("b", false);
  sub_map.set("c", 1);
  sub_map.set("d", "hello world");
  sub_text.insert(0, "a");
  sub_text.insert(1, "b");
  sub_text.insert(2, "c");

  let doc2 = new Y.Doc();
  Y.applyUpdate(doc2, doc.encodeStateAsUpdateV1());

  let map2 = doc2.getMap<any>("map");
  let sub_array2 = map2.get("array") as Y.Array<any>;
  let sub_map2 = map2.get("map") as Y.Map<any>;
  let sub_text2 = map2.get("text") as Y.Text;

  t.assert(sub_array2);
  t.is(sub_array2.length, 4);
  t.is(sub_array2.get(0), true);
  t.is(sub_array2.get(1), false);
  t.is(sub_array2.get(2), 1);
  t.is(sub_array2.get(3), "hello world");
  t.assert(sub_map2);
  t.is(sub_map2.get("a"), true);
  t.is(sub_map2.get("b"), false);
  t.is(sub_map2.get("c"), 1);
  t.is(sub_map2.get("d"), "hello world");
  t.assert(sub_text2);
  t.is(sub_text2.toString(), "abc");
});

test("yjs to y-octo compatibility test with nested type", (t) => {
  let doc2 = new Y.Doc();
  let map2 = doc2.getMap<any>("map");
  let sub_array2 = new Y.Array<any>();
  let sub_map2 = new Y.Map<any>();
  let sub_text2 = new Y.Text();
  map2.set("array", sub_array2);
  map2.set("map", sub_map2);
  map2.set("text", sub_text2);

  sub_array2.insert(0, [true]);
  sub_array2.insert(1, [false]);
  sub_array2.insert(2, [1]);
  sub_array2.insert(3, ["hello world"]);
  sub_map2.set("a", true);
  sub_map2.set("b", false);
  sub_map2.set("c", 1);
  sub_map2.set("d", "hello world");
  sub_text2.insert(0, "a");
  sub_text2.insert(1, "b");
  sub_text2.insert(2, "c");

  doc.applyUpdate(Buffer.from(Y.encodeStateAsUpdate(doc2)));

  let map = doc.getOrCreateMap("map");
  let sub_array = map.get<YOcto.Array>("array");
  let sub_map = map.get<YOcto.Map>("map");
  let sub_text = map.get<YOcto.Text>("text");

  t.assert(sub_array);
  t.is(sub_array.length, 4);
  t.is(sub_array.get(0), true);
  t.is(sub_array.get(1), false);
  t.is(sub_array.get(2), 1);
  t.is(sub_array.get(3), "hello world");
  t.assert(sub_map);
  t.is(sub_map.get("a"), true);
  t.is(sub_map.get("b"), false);
  t.is(sub_map.get("c"), 1);
  t.is(sub_map.get("d"), "hello world");
  t.assert(sub_text);
  t.is(sub_text.toString(), "abc");
});
