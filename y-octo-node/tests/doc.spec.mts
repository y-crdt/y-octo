import { equal } from "node:assert";
import { test } from "node:test";

import { Doc } from "../index";

test("y-octo doc", { concurrency: false }, async (t) => {
  let client_id: number;
  let doc: Doc | null;
  t.beforeEach(async () => {
    client_id = (Math.random() * 100000) | 1;
    doc = new Doc(client_id);
  });

  t.afterEach(async () => {
    client_id = -1;
    doc = null;
  });

  await t.test("doc id should be set", () => {
    equal(doc?.clientId, client_id);
  });
});
