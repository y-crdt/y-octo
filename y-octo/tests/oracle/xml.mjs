import fs from "node:fs";
import { fileURLToPath } from "node:url";
import * as Y from "yjs-13-6-33";

function encodeHex(bytes) {
  return Buffer.from(bytes).toString("hex");
}

function decodeHex(hex) {
  return Uint8Array.from(Buffer.from(hex, "hex"));
}

function summarizeTree(root) {
  return [...root.createTreeWalker()].map((node) => {
    if (node instanceof Y.XmlElement) {
      return {
        kind: "XMLElement",
        tag: node.nodeName,
        attrs: Object.keys(node.getAttributes()).sort(),
      };
    }
    if (node instanceof Y.XmlText) {
      return {
        kind: "XMLText",
        text: node.toString(),
      };
    }
    if (node instanceof Y.XmlHook) {
      return {
        kind: "XMLHook",
        hookName: node.hookName,
        entries: Object.entries(node.toJSON()).sort((a, b) =>
          a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0,
        ),
      };
    }
    if (node instanceof Y.XmlFragment) {
      return { kind: "XMLFragment" };
    }
    return { kind: "Unknown" };
  });
}

function buildCase1() {
  const doc1 = new Y.Doc({ guid: "xml-oracle-1", gc: true });
  doc1.clientID = 101;
  const doc2 = new Y.Doc({ guid: "xml-oracle-2", gc: true });
  doc2.clientID = 202;

  const frag1 = doc1.getXmlFragment("xml");
  const rootEl1 = doc1.getXmlElement("rootEl");
  rootEl1.setAttribute("role", "main");

  const div = new Y.XmlElement("Div");
  div.setAttribute("z", "hello <world> & \"quotes\" 'single'");
  div.setAttribute("a", 42);
  div.setAttribute("b", true);
  div.setAttribute("c", { nested: 1 });
  div.setAttribute("d", null);
  div.setAttribute("e", undefined);
  div.setAttribute("f", [1, "x", null, false]);
  div.setAttribute("g", new Uint8Array([7, 8, 9]));
  div.setAttribute("f_exp_neg", 1e-7);
  div.setAttribute("f_fix_neg", 1e-6);
  div.setAttribute("f_fix_pos", 1e20);
  div.setAttribute("f_exp_pos", 1e21);
  div.setAttribute("f_neg_zero", -0);
  // ECMA-262 shortest decimal ties-to-even (0x430c6bf526340002 = 1000000000000000.25)
  div.setAttribute("f_tie_pos", 1000000000000000.25);
  div.setAttribute("f_tie_neg", -1000000000000000.25);
  // UTF-16 code unit ordering: U+10000 (0xD800 0xDC00) < U+E000 (0xE000) in JS,
  // opposite of UTF-8 / Unicode scalar order.
  div.setAttribute("\uE000", "bmp-pua");
  div.setAttribute("\u{10000}", "supplementary");
  div.setAttribute("temp", "will-remove");

  const rich = new Y.XmlText();
  rich.applyDelta([
    {
      insert: "a < b & c \"d\" 'e'",
      attributes: {
        bold: true,
        link: {
          href: "https://example.com?a=1&b=2",
          title: "doc",
          "\uE000": "bmp",
          "\u{10000}": "supp",
        },
        "\uE000": true,
        "\u{10000}": true,
      },
    },
    { insert: " plain " },
    {
      insert: "em",
      attributes: {
        italic: {},
        str_attr: "ab",
        arr_attr: ["x", 12],
        arr11: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
      },
    },
  ]);
  div.insert(0, [rich]);

  const hook = new Y.XmlHook("widget-card");
  hook.set("title", "Card 1");
  hook.set("count", 3);

  const nestedFrag = new Y.XmlFragment();
  const span = new Y.XmlElement("SPAN");
  span.setAttribute("data-id", "s1");
  const spanText = new Y.XmlText();
  spanText.insert(0, "inside-frag");
  span.insert(0, [spanText]);
  nestedFrag.push([span]);

  const toDelete = new Y.XmlElement("temp");
  frag1.insert(0, [div, toDelete, hook, nestedFrag]);

  // Separate fragment with multi-element ContentAny(["p1", 2, false]) so
  // YXmlFragment.prototype.toString() concatenates every element (Yjs
  // YXmlTreeWalker assumes ContentType items, so keep `xml` typed).
  const mixed1 = doc1.getXmlFragment("mixed");
  const mixedEl = new Y.XmlElement("b");
  const mixedTxt = new Y.XmlText();
  mixedTxt.insert(0, "ok");
  mixedEl.insert(0, [mixedTxt]);
  mixed1.insert(0, ["p1", 2, false, mixedEl]);

  // Sync doc1 -> doc2, perform concurrent edits & deletions, then sync both ways.
  Y.applyUpdate(doc2, Y.encodeStateAsUpdate(doc1));
  const frag2 = doc2.getXmlFragment("xml");
  const div2 = frag2.get(0);
  div2.setAttribute("remote", "from-202");
  div2.removeAttribute("temp");
  const p2 = new Y.XmlElement("p");
  const p2Text = new Y.XmlText();
  p2Text.insert(0, "peer-added", { code: true });
  p2.insert(0, [p2Text]);
  div2.push([p2]);

  // Concurrently on doc1: delete `toDelete` child and edit rich text.
  frag1.delete(1, 1);
  rich.insert(rich.length, "!");

  Y.applyUpdate(doc1, Y.encodeStateAsUpdate(doc2, Y.encodeStateVector(doc1)));
  Y.applyUpdate(doc2, Y.encodeStateAsUpdate(doc1, Y.encodeStateVector(doc2)));

  if (frag1.toString() !== frag2.toString()) {
    throw new Error("Yjs replicas diverged");
  }

  return {
    yjs_version: "13.6.33",
    update_hex: encodeHex(Y.encodeStateAsUpdate(doc1)),
    frag_to_string: frag1.toString(),
    mixed_to_string: mixed1.toString(),
    root_el_to_string: rootEl1.toString(),
    root_el_node_name: rootEl1.nodeName,
    div_attrs_keys: Object.keys(div.getAttributes()).sort(),
    tree_walker: summarizeTree(frag1),
    state_vector: [...Y.decodeStateVector(Y.encodeStateVector(doc1))].sort(
      (a, b) => a[0] - b[0],
    ),
  };
}

function buildExpectedCase2() {
  const doc = new Y.Doc({ guid: "case2-expected", gc: true });
  doc.clientID = 808;
  const frag = doc.getXmlFragment("xml");
  const rootEl = doc.getXmlElement("rootEl");
  rootEl.setAttribute("id", "root-1");

  const section = new Y.XmlElement("Section");
  section.setAttribute("class", "published");
  section.setAttribute("count", 1);
  section.setAttribute("flag", null);
  section.setAttribute("f_exp_neg", 1e-7);
  section.setAttribute("f_fix_neg", 1e-6);
  section.setAttribute("f_fix_pos", 1e20);
  section.setAttribute("f_exp_pos", 1e21);
  section.setAttribute("f_tie_pos", 1000000000000000.25);
  section.setAttribute("f_tie_neg", -1000000000000000.25);
  section.setAttribute("f_neg_zero", -0);
  section.setAttribute("\uE000", "bmp-pua");
  section.setAttribute("\u{10000}", "supplementary");

  const text = new Y.XmlText();
  text.applyDelta([
    {
      insert: 'Hello <world> & "friends"!',
      attributes: {
        bold: true,
        link: { href: "https://a.test?x=1&y=2", title: "A & B" },
      },
    },
    { insert: " " },
    { insert: "tail", attributes: { italic: true } },
    {
      insert: "X",
      attributes: {
        link: "ab",
        arr: ["x", 12],
        arr11: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        bin: new Uint8Array([7, 8]),
      },
    },
  ]);
  section.insert(0, [text]);

  const hook = new Y.XmlHook("custom-embed");
  hook.set("k", "v");
  hook.set("n", 9);

  frag.push([section, hook]);
  return { frag, rootEl };
}

function verifyUpdate(payload) {
  const doc = new Y.Doc({ guid: "xml-verify", gc: true });
  doc.clientID = 999;
  Y.applyUpdate(doc, decodeHex(payload.update_hex));
  const frag = doc.getXmlFragment("xml");
  const rootEl = doc.getXmlElement("rootEl");

  // Independently construct Case 2 in Yjs to catch any wire distortion from Rust.
  const expected = buildExpectedCase2();
  const decodedSection = frag.get(0);
  const expectedNumbers = {
    count: 1,
    f_exp_neg: 1e-7,
    f_fix_neg: 1e-6,
    f_fix_pos: 1e20,
    f_exp_pos: 1e21,
    f_tie_pos: 1000000000000000.25,
    f_tie_neg: -1000000000000000.25,
    f_neg_zero: -0,
  };
  for (const [k, expVal] of Object.entries(expectedNumbers)) {
    const actualVal = decodedSection.getAttribute(k);
    if (typeof actualVal !== "number") {
      throw new Error(
        `attribute ${k}: expected typeof number, got ${typeof actualVal} (${String(actualVal)})`,
      );
    }
    if (!Object.is(actualVal, expVal)) {
      throw new Error(
        `attribute ${k}: expected ${Object.is(expVal, -0) ? "-0" : expVal}, got ${Object.is(actualVal, -0) ? "-0" : actualVal}`,
      );
    }
  }
  if (frag.toString() !== expected.frag.toString()) {
    throw new Error(
      `decoded frag.toString() diverged from independently constructed Yjs doc:\n  decoded:  ${frag.toString()}\n  expected: ${expected.frag.toString()}`,
    );
  }
  if (rootEl.toString() !== expected.rootEl.toString()) {
    throw new Error(
      `decoded rootEl.toString() diverged from independently constructed Yjs doc:\n  decoded:  ${rootEl.toString()}\n  expected: ${expected.rootEl.toString()}`,
    );
  }

  return {
    frag_to_string: frag.toString(),
    root_el_to_string: rootEl.toString(),
    root_el_node_name: rootEl.nodeName,
    tree_walker: summarizeTree(frag),
    state_vector: [...Y.decodeStateVector(Y.encodeStateVector(doc))].sort(
      (a, b) => a[0] - b[0],
    ),
  };
}

const args = process.argv.slice(2);
if (args.includes("--generate")) {
  const out = buildCase1();
  const target = fileURLToPath(new URL("./xml.json", import.meta.url));
  fs.writeFileSync(target, JSON.stringify(out, null, 2) + "\n");
} else if (args.includes("--case1")) {
  process.stdout.write(JSON.stringify(buildCase1()) + "\n");
} else if (args.includes("--verify")) {
  const input = fs.readFileSync(0, "utf8");
  const payload = JSON.parse(input);
  process.stdout.write(JSON.stringify(verifyUpdate(payload)) + "\n");
} else {
  throw new Error("Expected --generate, --case1, or --verify");
}
