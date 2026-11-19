// Canonical test-state digest: explicit tags/lengths, IEEE-754 numbers, UTF-8
// strings and byte-sorted object keys. Independent of JSON float formatting.
import { createHash } from "node:crypto";
export function digest(value) {
  const hash = createHash("sha256");
  const byte = (n) => hash.update(Uint8Array.of(n));
  const length = (n) => {
    const b = Buffer.alloc(4);
    b.writeUInt32BE(n);
    hash.update(b);
  };
  function visit(v) {
    if (v === null) return byte(0);
    if (v === false) return byte(1);
    if (v === true) return byte(2);
    if (typeof v === "number") {
      byte(3);
      const b = Buffer.alloc(8);
      b.writeDoubleBE(v);
      hash.update(b);
      return;
    }
    if (typeof v === "string") {
      byte(4);
      const b = Buffer.from(v);
      length(b.length);
      hash.update(b);
      return;
    }
    if (Array.isArray(v)) {
      byte(5);
      length(v.length);
      v.forEach(visit);
      return;
    }
    const keys = Object.keys(v).sort((a, b) =>
      Buffer.compare(Buffer.from(a), Buffer.from(b)),
    );
    byte(6);
    length(keys.length);
    for (const k of keys) {
      visit(k);
      visit(v[k]);
    }
  }
  visit(value);
  return hash.digest("hex");
}
