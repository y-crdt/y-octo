import assert, { equal, deepEqual } from "node:assert";
import { test } from "node:test";

import { Doc, YMap } from "../index";

test("map test", { concurrency: false }, async (t) => {
  let client_id: number;
  let doc: Doc;
  t.beforeEach(async () => {
    client_id = (Math.random() * 100000) | 0;
    doc = new Doc(client_id);
  });

  t.afterEach(async () => {
    client_id = -1;
    // @ts-ignore - doc must not null in next range
    doc = null;
  });

  await t.test("map should be created", () => {
    let map = doc.getOrCreateMap("map");
    deepEqual(doc.keys, ["map"]);
    equal(map.length, 0);
  });

  await t.test("map editing", () => {
    let map = doc.getOrCreateMap("map");
    map.set("a", true);
    map.set("b", false);
    map.set("c", 1);
    map.set("d", "hello world");
    equal(map.length, 4);
    equal(map.get("a"), true);
    equal(map.get("b"), false);
    equal(map.get("c"), 1);
    equal(map.get("d"), "hello world");
    equal(map.length, 4);
    map.remove("b");
    equal(map.length, 3);
    equal(map.get("d"), "hello world");
  });

  await t.test("sub map should can edit", () => {
    let map = doc.getOrCreateMap("map");
    let sub = doc.createMap();
    map.setMap("sub", sub);

    sub.set("a", true);
    sub.set("b", false);
    sub.set("c", 1);
    sub.set("d", "hello world");
    equal(sub.length, 4);

    let sub2 = map.get<YMap>("sub");
    assert(sub2);
    equal(sub2.get("a"), true);
    equal(sub2.get("b"), false);
    equal(sub2.get("c"), 1);
    equal(sub2.get("d"), "hello world");
    equal(sub2.length, 4);
  });
});
