import test from "ava";

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

test("text should be created", (t) => {
  let text = doc.getOrCreateText("text");
  t.deepEqual(doc.keys, ["text"]);
  t.is(text.len, 0);
});

test("text editing", (t) => {
  let text = doc.getOrCreateText("text");
  text.insert(0, "a");
  text.insert(1, "b");
  text.insert(2, "c");
  t.is(text.toString(), "abc");
  text.delete(0, 1);
  t.is(text.toString(), "bc");
  text.delete(1, 1);
  t.is(text.toString(), "b");
  text.delete(0, 1);
  t.is(text.toString(), "");
});

test("sub text should can edit", (t) => {
  let map = doc.getOrCreateMap("map");
  let sub = doc.createText();
  map.set("sub", sub);

  sub.insert(0, "a");
  sub.insert(1, "b");
  sub.insert(2, "c");
  t.is(sub.toString(), "abc");

  let sub2 = map.get<Text>("sub");
  t.assert(sub2);
  t.is(sub2.toString(), "abc");
});
