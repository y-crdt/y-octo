import { equal, deepEqual } from "node:assert";
import { test } from "node:test";

import { Doc } from "../index";

test("y-octo doc", { concurrency: false }, async (t) => {
  let client_id: number;
  let doc: Doc | null;
  t.beforeEach(async () => {
    client_id = (Math.random() * 100000) | 0;
    doc = new Doc(client_id);
  });

  t.afterEach(async () => {
    client_id = -1;
    doc = null;
  });

  await t.test("doc id should be set", () => {
    equal(doc?.clientId, client_id);
  });

  await t.test("text should be created", () => {
    let text = doc?.getOrCreateText("text");
    deepEqual(doc?.keys, ["text"]);
    equal(text?.len, 0);
  });

  await t.test("text editing", () => {
    let text = doc?.getOrCreateText("text");
    text?.insert(0, "a");
    text?.insert(1, "b");
    text?.insert(2, "c");
    equal(text?.toString(), "abc");
    text?.remove(0, 1);
    equal(text?.toString(), "bc");
    text?.remove(1, 1);
    equal(text?.toString(), "b");
    text?.remove(0, 1);
    equal(text?.toString(), "");
  });
});
