// Scheme C ES module wrapper for `y-octo-wasm` (zero host imports):
// 4-byte aligned little-endian binary tape + reusable scratch buffers
// + high-frequency direct scalar C-ABI hot paths.

const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8", { ignoreBOM: true });

const YTYPE_KIND_MAP = {
  Array: 0,
  Map: 1,
  Text: 2,
  XMLElement: 3,
  XmlElement: 3,
  XMLFragment: 4,
  XmlFragment: 4,
  XMLHook: 5,
  XmlHook: 5,
  XMLText: 6,
  XmlText: 6,
  Unknown: 7,
};

const YTYPE_KIND_REV = [
  "Array",
  "Map",
  "Text",
  "XMLElement",
  "XMLFragment",
  "XMLHook",
  "XMLText",
  "Unknown",
];

const UNDO_MODE_MAP = {
  global: 0,
  disabled: 1,
  custom: 2,
};

const ASCII_WRITE_FAST_MAX = 16;
const ASCII_READ_FAST_MAX = 12;

/**
 * Instantiates a `y-octo-wasm` binary with zero host imports.
 * @param {BufferSource} wasmBytes
 */
export async function loadYOctoWasm(wasmBytes) {
  const mod = new WebAssembly.Module(wasmBytes);
  const imports = WebAssembly.Module.imports(mod);
  if (imports.length !== 0) {
    throw new Error(
      `y-octo-wasm expected zero host imports, got: ${JSON.stringify(imports)}`,
    );
  }
  const instance = await WebAssembly.instantiate(mod, {});
  const exp = instance.exports;
  if (exp.wasm_abi_version?.() !== 1) {
    throw new Error(
      `y-octo-wasm ABI version mismatch: expected 1, got ${exp.wasm_abi_version?.()}`,
    );
  }

  let memBuf = exp.memory.buffer;
  let u8 = new Uint8Array(memBuf);
  let dv = new DataView(memBuf);
  let inPtr = 0;
  let inCap = 0;
  let wPos = 0;
  let rPos = 0;
  let encodeDepth = 0;
  let pendingTrim = false;

  function refreshMem() {
    if (memBuf !== exp.memory.buffer) {
      memBuf = exp.memory.buffer;
      u8 = new Uint8Array(memBuf);
      dv = new DataView(memBuf);
    }
  }

  function runTrimScratch() {
    pendingTrim = false;
    exp.runtime_trim_scratch();
    inPtr = 0;
    inCap = 0;
    wPos = 0;
    rPos = 0;
    refreshMem();
  }

  function wReset(minCap = 1024) {
    const req = Math.max(minCap, 64);
    inPtr = exp.in_buf_ensure(req);
    inCap = req;
    refreshMem();
    wPos = inPtr;
  }

  function withInputFrame(minCap, fn) {
    let savedBytes = null;
    let savedCap = 0;
    if (encodeDepth > 0) {
      refreshMem();
      savedBytes = u8.slice(inPtr, wPos);
      savedCap = inCap;
    }
    encodeDepth++;
    try {
      wReset(minCap);
      return fn();
    } finally {
      encodeDepth--;
      if (encodeDepth > 0 && savedBytes !== null) {
        const need = Math.max(savedCap, savedBytes.length, 64);
        inPtr = exp.in_buf_ensure(need);
        inCap = need;
        refreshMem();
        u8.set(savedBytes, inPtr);
        wPos = inPtr + savedBytes.length;
      } else if (encodeDepth === 0 && pendingTrim) {
        runTrimScratch();
      }
    }
  }

  function wEnsure(extra) {
    const used = wPos - inPtr;
    if (used + extra > inCap) {
      const nextCap = Math.max((used + extra) * 2, inCap * 2, 1024);
      inPtr = exp.in_buf_ensure(nextCap);
      inCap = nextCap;
      refreshMem();
      wPos = inPtr + used;
    } else {
      refreshMem();
    }
  }

  function wU32(v) {
    wEnsure(4);
    dv.setUint32(wPos, v, true);
    wPos += 4;
  }

  function wI32(v) {
    wEnsure(4);
    dv.setInt32(wPos, v, true);
    wPos += 4;
  }

  function wU64(v) {
    wEnsure(8);
    const lo = v >>> 0;
    const hi = Math.floor(v / 4294967296) >>> 0;
    dv.setUint32(wPos, lo, true);
    dv.setUint32(wPos + 4, hi, true);
    wPos += 8;
  }

  function wI64(v) {
    wEnsure(8);
    dv.setBigInt64(wPos, BigInt(v), true);
    wPos += 8;
  }

  function wF64(v) {
    wEnsure(8);
    dv.setFloat64(wPos, v, true);
    wPos += 8;
  }

  function writeUtf8Raw(str, off) {
    const slen = str.length;
    if (slen <= ASCII_WRITE_FAST_MAX) {
      for (let i = 0; i < slen; i++) {
        const c = str.charCodeAt(i);
        if (c >= 0x80) {
          return encoder.encodeInto(str, u8.subarray(off)).written;
        }
        u8[off + i] = c;
      }
      return slen;
    }
    return encoder.encodeInto(str, u8.subarray(off)).written;
  }

  function wStr(str) {
    const maxBytes = str.length * 3 + 8;
    wEnsure(maxBytes);
    const lenOff = wPos;
    wPos += 4;
    const written = writeUtf8Raw(str, wPos);
    dv.setUint32(lenOff, written, true);
    wPos += (written + 3) & ~3;
  }

  function wBytes(bytes) {
    const src = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
    const len = src.length;
    const padded = (len + 3) & ~3;
    wEnsure(4 + padded);
    dv.setUint32(wPos, len, true);
    wPos += 4;
    u8.set(src, wPos);
    wPos += padded;
  }

  function wAny(val) {
    if (val === undefined) {
      wU32(0);
    } else if (val === null) {
      wU32(1);
    } else if (val === false) {
      wU32(2);
    } else if (val === true) {
      wU32(3);
    } else if (typeof val === "number") {
      if (
        Number.isInteger(val) &&
        !Object.is(val, -0) &&
        val >= -2147483648 &&
        val <= 2147483647
      ) {
        wU32(4);
        wI32(val);
      } else {
        wU32(6);
        wF64(val);
      }
    } else if (typeof val === "bigint") {
      wU32(7);
      wI64(val);
    } else if (typeof val === "string") {
      wU32(8);
      wStr(val);
    } else if (val instanceof Uint8Array) {
      wU32(9);
      wBytes(val);
    } else if (Array.isArray(val)) {
      wU32(10);
      wU32(val.length);
      for (let i = 0; i < val.length; i++) wAny(val[i]);
    } else if (typeof val === "object") {
      wU32(11);
      const keys = Object.keys(val);
      wU32(keys.length);
      for (let i = 0; i < keys.length; i++) {
        wStr(keys[i]);
        wAny(val[keys[i]]);
      }
    } else {
      wU32(0);
    }
  }

  function wTxOrigin(origin) {
    if (origin === "Tracked" || origin === undefined) {
      wU32(0);
    } else if (origin === "Untracked") {
      wU32(1);
    } else if (
      typeof origin === "object" &&
      origin !== null &&
      typeof origin.Named === "string"
    ) {
      wU32(2);
      wStr(origin.Named);
    } else {
      throw new Error(`Invalid SessionTxOrigin: ${JSON.stringify(origin)}`);
    }
  }

  function wIdentity(id) {
    if (Object.hasOwn(id, "Root")) {
      wU32(0);
      wStr(id.Root);
    } else {
      wU32(1);
      wU64(id.Item.client);
      wU64(id.Item.clock);
    }
  }

  function wPath(path) {
    wStr(path.root);
    wU32(path.segments.length);
    for (let i = 0; i < path.segments.length; i++) {
      const seg = path.segments[i];
      if (Object.hasOwn(seg, "Key")) {
        wU32(0);
        wStr(seg.Key);
      } else {
        wU32(1);
        wU64(seg.Index);
      }
    }
  }

  function wTarget(target) {
    if (Object.hasOwn(target, "Identity")) {
      wU32(0);
      wIdentity(target.Identity);
    } else {
      wU32(1);
      wPath(target.Path);
    }
  }

  function wFormat(fmt) {
    if (!fmt) {
      wU32(0);
      return;
    }
    const keys = Object.keys(fmt);
    wU32(keys.length);
    for (let i = 0; i < keys.length; i++) {
      wStr(keys[i]);
      wAny(fmt[keys[i]]);
    }
  }

  function wDelta(delta) {
    wU32(delta.length);
    for (let i = 0; i < delta.length; i++) {
      const op = delta[i];
      if (Object.hasOwn(op, "insert")) {
        const ins = op.insert;
        const fmt = op.format;
        if (typeof ins === "string") {
          wU32(0);
          wStr(ins);
          wFormat(fmt);
        } else if (Array.isArray(ins)) {
          wU32(1);
          wU32(ins.length);
          for (let j = 0; j < ins.length; j++) wAny(ins[j]);
          wFormat(fmt);
        } else {
          wU32(1);
          wU32(1);
          wAny(ins);
          wFormat(fmt);
        }
      } else if (Object.hasOwn(op, "retain")) {
        wU32(2);
        wU64(op.retain);
        wFormat(op.format);
      } else {
        wU32(3);
        wU64(op.delete);
      }
    }
  }

  function wSessionValue(v) {
    if (Object.hasOwn(v, "Any")) {
      wU32(0);
      wAny(v.Any);
    } else if (Object.hasOwn(v, "Map")) {
      wU32(1);
      const entries = v.Map;
      wU32(entries.length);
      for (let i = 0; i < entries.length; i++) {
        wStr(entries[i][0]);
        wSessionValue(entries[i][1]);
      }
    } else if (Object.hasOwn(v, "Array")) {
      wU32(2);
      const arr = v.Array;
      wU32(arr.length);
      for (let i = 0; i < arr.length; i++) wSessionValue(arr[i]);
    } else if (Object.hasOwn(v, "Text")) {
      wU32(3);
      wDelta(v.Text);
    } else if (Object.hasOwn(v, "Doc")) {
      const doc = v.Doc;
      wU32(4);
      wStr(doc.guid);
      wU32(doc.gc ? 1 : 0);
    } else if (Object.hasOwn(v, "XmlElement")) {
      const el = v.XmlElement;
      wU32(5);
      wStr(el.tag);
      const attrs = el.attrs ?? [];
      wU32(attrs.length);
      for (let i = 0; i < attrs.length; i++) {
        wStr(attrs[i][0]);
        wAny(attrs[i][1]);
      }
      const children = el.children ?? [];
      wU32(children.length);
      for (let i = 0; i < children.length; i++) wSessionValue(children[i]);
    } else if (Object.hasOwn(v, "XmlFragment")) {
      wU32(6);
      const children = v.XmlFragment;
      wU32(children.length);
      for (let i = 0; i < children.length; i++) wSessionValue(children[i]);
    } else if (Object.hasOwn(v, "XmlText")) {
      wU32(7);
      wDelta(v.XmlText);
    } else if (Object.hasOwn(v, "XmlHook")) {
      const hook = v.XmlHook;
      wU32(8);
      wStr(hook.name);
      const entries = hook.entries ?? [];
      wU32(entries.length);
      for (let i = 0; i < entries.length; i++) {
        wStr(entries[i][0]);
        wSessionValue(entries[i][1]);
      }
    } else {
      throw new Error(`Invalid SessionValue: ${JSON.stringify(v)}`);
    }
  }

  function rStart() {
    refreshMem();
    rPos = exp.out_buf_ptr();
    return exp.out_buf_len();
  }

  function readRawOutBytes() {
    const len = rStart();
    return u8.slice(rPos, rPos + len);
  }

  function rU32() {
    const v = dv.getUint32(rPos, true);
    rPos += 4;
    return v;
  }

  function rI32() {
    const v = dv.getInt32(rPos, true);
    rPos += 4;
    return v;
  }

  function rU64() {
    const lo = dv.getUint32(rPos, true);
    const hi = dv.getUint32(rPos + 4, true);
    rPos += 8;
    return hi * 4294967296 + lo;
  }

  function rI64() {
    const v = Number(dv.getBigInt64(rPos, true));
    rPos += 8;
    return v;
  }

  function rF64() {
    const v = dv.getFloat64(rPos, true);
    rPos += 8;
    return v;
  }

  function rStr() {
    const len = dv.getUint32(rPos, true);
    rPos += 4;
    const start = rPos;
    rPos += (len + 3) & ~3;
    if (len === 0) return "";
    if (len <= ASCII_READ_FAST_MAX) {
      let allAscii = true;
      let s = "";
      for (let i = 0; i < len; i++) {
        const b = u8[start + i];
        if (b >= 0x80) {
          allAscii = false;
          break;
        }
        s += String.fromCharCode(b);
      }
      if (allAscii) return s;
    }
    return decoder.decode(u8.subarray(start, start + len));
  }

  function rBytes() {
    const len = dv.getUint32(rPos, true);
    rPos += 4;
    const out = u8.slice(rPos, rPos + len);
    rPos += (len + 3) & ~3;
    return out;
  }

  function rAny() {
    switch (rU32()) {
      case 0:
        return undefined;
      case 1:
        return null;
      case 2:
        return false;
      case 3:
        return true;
      case 4:
        return rI32();
      case 5: {
        const v = dv.getFloat32(rPos, true);
        rPos += 4;
        return v;
      }
      case 6:
        return rF64();
      case 7: {
        const v = dv.getBigInt64(rPos, true);
        rPos += 8;
        return v;
      }
      case 8:
        return rStr();
      case 9:
        return rBytes();
      case 10: {
        const len = rU32();
        const arr = new Array(len);
        for (let i = 0; i < len; i++) arr[i] = rAny();
        return arr;
      }
      case 11: {
        const len = rU32();
        const obj = {};
        for (let i = 0; i < len; i++) {
          const key = rStr();
          const val = rAny();
          Object.defineProperty(obj, key, {
            value: val,
            enumerable: true,
            writable: true,
            configurable: true,
          });
        }
        return obj;
      }
      default:
        throw new Error("bad aligned Any tag");
    }
  }

  function rIdentity() {
    if (rU32() === 0) return { Root: rStr() };
    return { Item: { client: rU64(), clock: rU64() } };
  }

  function rPath() {
    const root = rStr();
    const len = rU32();
    const segments = new Array(len);
    for (let i = 0; i < len; i++) {
      segments[i] = rU32() === 0 ? { Key: rStr() } : { Index: rU64() };
    }
    return { root, segments };
  }

  function rTypeStatus() {
    const alive = rU32() !== 0;
    const kind = rU32() === 0 ? null : YTYPE_KIND_REV[rU32()];
    const path = rU32() === 0 ? null : rPath();
    return { alive, kind, path };
  }

  function rReadValue() {
    switch (rU32()) {
      case 0:
        return { Any: rAny() };
      case 1:
        return { Map: rIdentity() };
      case 2:
        return { Array: rIdentity() };
      case 3:
        return { Text: rIdentity() };
      case 4:
        return { Doc: { guid: rStr(), gc: rU32() !== 0 } };
      case 5:
        return { XmlElement: { tag: rStr(), identity: rIdentity() } };
      case 6:
        return { XmlFragment: rIdentity() };
      case 7:
        return { XmlText: rIdentity() };
      case 8:
        return { XmlHook: { name: rStr(), identity: rIdentity() } };
      default:
        throw new Error("bad aligned ReadValue tag");
    }
  }

  function rFormat() {
    const len = rU32();
    if (len === 0) return undefined;
    const obj = {};
    for (let i = 0; i < len; i++) {
      const key = rStr();
      const val = rAny();
      Object.defineProperty(obj, key, {
        value: val,
        enumerable: true,
        writable: true,
        configurable: true,
      });
    }
    return obj;
  }

  function rDelta() {
    const len = rU32();
    const ops = new Array(len);
    for (let i = 0; i < len; i++) {
      const tag = rU32();
      if (tag === 0) {
        const insert = rStr();
        const format = rFormat();
        ops[i] = format ? { insert, format } : { insert };
      } else if (tag === 1) {
        const elen = rU32();
        const insert = new Array(elen);
        for (let j = 0; j < elen; j++) insert[j] = rAny();
        const format = rFormat();
        ops[i] = format ? { insert, format } : { insert };
      } else if (tag === 2) {
        const retain = rU64();
        const format = rFormat();
        ops[i] = format ? { retain, format } : { retain };
      } else {
        ops[i] = { delete: rU64() };
      }
    }
    return ops;
  }

  function rCommitBody() {
    const revision = rU64();
    const flags = rU32();
    const originTag = (flags >>> 4) & 0xf;
    let origin_kind;
    if (originTag === 0) origin_kind = "LocalTransact";
    else if (originTag === 1) origin_kind = "LocalUntracked";
    else if (originTag === 2) origin_kind = "RemoteSync";
    else if (originTag === 3) origin_kind = { Undo: { stack_id: rU32() } };
    else if (originTag === 4) origin_kind = { Redo: { stack_id: rU32() } };
    else if (originTag === 5) origin_kind = { LocalNamed: rStr() };
    else if (originTag === 6) origin_kind = "FormattingCleanup";
    else throw new Error(`bad originTag ${originTag}`);

    const update = rBytes();
    const chLen = rU32();
    const changed = new Array(chLen);
    for (let i = 0; i < chLen; i++) {
      const identity = rIdentity();
      const path = rU32() === 0 ? null : rPath();
      const kLen = rU32();
      const keys = new Array(kLen);
      for (let j = 0; j < kLen; j++) keys[j] = rStr();
      changed[i] = { identity, path, keys };
    }
    const saLen = rU32();
    const subdocs_added = new Array(saLen);
    for (let i = 0; i < saLen; i++) subdocs_added[i] = rStr();
    const srLen = rU32();
    const subdocs_removed = new Array(srLen);
    for (let i = 0; i < srLen; i++) subdocs_removed[i] = rStr();
    const selection_meta = (flags & 0x100) !== 0 ? rBytes() : null;
    return {
      revision,
      update,
      is_local: (flags & 1) !== 0,
      origin_kind,
      changed,
      subdocs_added,
      subdocs_removed,
      can_undo: (flags & 2) !== 0,
      can_redo: (flags & 4) !== 0,
      selection_meta,
    };
  }

  function rOptCommit() {
    if (rU32() === 0) return null;
    return rCommitBody();
  }

  function rAwarenessEvent() {
    const aLen = rU32();
    const added = new Array(aLen);
    for (let i = 0; i < aLen; i++) added[i] = rU64();
    const uLen = rU32();
    const updated = new Array(uLen);
    for (let i = 0; i < uLen; i++) updated[i] = rU64();
    const rLen = rU32();
    const removed = new Array(rLen);
    for (let i = 0; i < rLen; i++) removed[i] = rU64();
    return { added, updated, removed };
  }

  function readError() {
    refreshMem();
    const ptr = exp.error_ptr();
    const len = exp.error_len();
    return decoder.decode(u8.subarray(ptr, ptr + len));
  }

  function checkOk(code) {
    if (code === 0) {
      throw new Error(readError() || "y-octo-wasm call failed");
    }
    return code;
  }

  function trimScratch() {
    if (encodeDepth > 0) {
      pendingTrim = true;
      return;
    }
    runTrimScratch();
  }

  // Stateless V1 wire operators.
  function validateUpdateV1(update) {
    const src = update instanceof Uint8Array ? update : new Uint8Array(update);
    withInputFrame(src.length, () => {
      u8.set(src, inPtr);
      wPos = inPtr + src.length;
      checkOk(exp.wire_validate_update_v1(src.length));
    });
  }

  function encodeStateVectorFromUpdateV1(update) {
    const src = update instanceof Uint8Array ? update : new Uint8Array(update);
    return withInputFrame(src.length, () => {
      u8.set(src, inPtr);
      wPos = inPtr + src.length;
      checkOk(exp.wire_encode_sv_from_update_v1(src.length));
      return readRawOutBytes();
    });
  }

  function diffUpdateV1(update, sv) {
    const u = update instanceof Uint8Array ? update : new Uint8Array(update);
    const s = sv instanceof Uint8Array ? sv : new Uint8Array(sv);
    return withInputFrame(u.length + s.length, () => {
      u8.set(u, inPtr);
      u8.set(s, inPtr + u.length);
      wPos = inPtr + u.length + s.length;
      checkOk(exp.wire_diff_update_v1(u.length, s.length));
      return readRawOutBytes();
    });
  }

  function mergeUpdatesV1(updates) {
    const list = Array.from(updates, (u) =>
      u instanceof Uint8Array ? u : new Uint8Array(u),
    );
    let total = 0;
    for (const src of list) total += 4 + src.length;
    return withInputFrame(total, () => {
      let offset = inPtr;
      for (const src of list) {
        dv.setUint32(offset, src.length, true);
        offset += 4;
        u8.set(src, offset);
        offset += src.length;
      }
      wPos = offset;
      checkOk(exp.wire_merge_updates_v1(total));
      return readRawOutBytes();
    });
  }

  function revertUpdateV1(currentSnapshot, targetSnapshot) {
    const cur =
      currentSnapshot instanceof Uint8Array
        ? currentSnapshot
        : new Uint8Array(currentSnapshot);
    const tgt =
      targetSnapshot instanceof Uint8Array
        ? targetSnapshot
        : new Uint8Array(targetSnapshot);
    return withInputFrame(cur.length + tgt.length, () => {
      u8.set(cur, inPtr);
      u8.set(tgt, inPtr + cur.length);
      wPos = inPtr + cur.length + tgt.length;
      checkOk(exp.wire_revert_update_v1(cur.length, tgt.length));
      return readRawOutBytes();
    });
  }

  class DocSession {
    constructor(
      clientId,
      guid,
      { gc = true, captureTimeoutMs = 500, undo = "global" } = {},
    ) {
      const undoMode = UNDO_MODE_MAP[undo];
      if (undoMode === undefined) {
        throw new Error(`Invalid undo mode: ${undo}`);
      }
      const cid = BigInt(clientId);
      const gcFlag = gc ? 1 : 0;
      const timeout = BigInt(captureTimeoutMs);
      this._handle = withInputFrame(guid.length * 3 + 16, () => {
        const written = writeUtf8Raw(guid, inPtr);
        wPos = inPtr + written;
        const h = exp.session_create(cid, written, gcFlag, undoMode, timeout);
        if (!h) {
          throw new Error(readError() || "session_create failed");
        }
        return h;
      });
    }

    free() {
      if (this._handle) {
        exp.session_free(this._handle);
        this._handle = 0;
      }
    }

    _exec() {
      const len = wPos - inPtr;
      checkOk(exp.session_exec(this._handle, len));
      rStart();
    }

    client() {
      return withInputFrame(64, () => {
        wU32(21);
        this._exec();
        return rU64();
      });
    }

    clientRequired() {
      return withInputFrame(64, () => {
        wU32(22);
        this._exec();
        return rU32() !== 0;
      });
    }

    setClient(clientId) {
      return withInputFrame(64, () => {
        wU32(23);
        wU64(Number(clientId));
        this._exec();
        return rU32() !== 0;
      });
    }

    guid() {
      return withInputFrame(64, () => {
        wU32(24);
        this._exec();
        return rStr();
      });
    }

    txDepth() {
      return exp.session_tx_depth(this._handle);
    }

    beginTx(origin = "Tracked") {
      if (origin === "Tracked" || origin === "Untracked") {
        return checkOk(
          exp.session_begin_tx(this._handle, origin === "Tracked" ? 0 : 1),
        );
      }
      return withInputFrame(1024, () => {
        wU32(1);
        wTxOrigin(origin);
        this._exec();
        return rU32();
      });
    }

    commitTx() {
      const code = checkOk(exp.session_commit_tx(this._handle));
      if (code === 1) return null;
      rStart();
      return rCommitBody();
    }

    transact(fn, origin = "Tracked") {
      this.beginTx(origin);
      let commit = null;
      let result;
      let threw = false;
      let caught;
      try {
        result = fn();
      } catch (err) {
        threw = true;
        caught = err;
      } finally {
        commit = this.commitTx();
      }
      if (threw) {
        caught.commit = commit;
        throw caught;
      }
      return { result, commit };
    }

    ensureRoot(name, kind) {
      const kindCode = YTYPE_KIND_MAP[kind];
      if (kindCode === undefined) {
        throw new Error(`Invalid YTypeKind: ${kind}`);
      }
      return withInputFrame(1024, () => {
        wU32(5);
        wStr(name);
        wU32(kindCode);
        this._exec();
        return rIdentity();
      });
    }

    resolvePath(path) {
      return withInputFrame(1024, () => {
        wU32(6);
        wPath(path);
        this._exec();
        return rU32() === 0 ? null : rIdentity();
      });
    }

    typeStatus(identity) {
      return withInputFrame(1024, () => {
        wU32(25);
        wIdentity(identity);
        this._exec();
        return rTypeStatus();
      });
    }

    getMapValue(target, key) {
      return withInputFrame(1024, () => {
        wU32(7);
        wTarget(target);
        wStr(key);
        this._exec();
        return rU32() === 0 ? null : rReadValue();
      });
    }

    readMap(target) {
      return withInputFrame(1024, () => {
        wU32(8);
        wTarget(target);
        this._exec();
        const len = rU32();
        const out = new Array(len);
        for (let i = 0; i < len; i++) out[i] = [rStr(), rReadValue()];
        return out;
      });
    }

    readArray(target) {
      return withInputFrame(1024, () => {
        wU32(9);
        wTarget(target);
        this._exec();
        const len = rU32();
        const out = new Array(len);
        for (let i = 0; i < len; i++) out[i] = rReadValue();
        return out;
      });
    }

    readArrayAt(target, index) {
      return withInputFrame(1024, () => {
        wU32(26);
        wTarget(target);
        wU64(index);
        this._exec();
        return rU32() === 0 ? null : rReadValue();
      });
    }

    readTextLen(target) {
      return withInputFrame(1024, () => {
        wU32(27);
        wTarget(target);
        this._exec();
        return rU64();
      });
    }

    readTextString(target) {
      return withInputFrame(1024, () => {
        wU32(10);
        wTarget(target);
        this._exec();
        return rStr();
      });
    }

    readTextDelta(target) {
      return withInputFrame(1024, () => {
        wU32(11);
        wTarget(target);
        this._exec();
        return rDelta();
      });
    }

    mapSet(target, key, value) {
      const hasAny = Object.hasOwn(value, "Any");
      const anyVal = hasAny ? value.Any : undefined;
      if (
        target.Identity &&
        target.Identity.Item &&
        hasAny &&
        typeof anyVal === "number" &&
        (!Number.isInteger(anyVal) ||
          anyVal < -2147483648 ||
          anyVal > 2147483647)
      ) {
        const id = target.Identity.Item;
        const cLo = id.client >>> 0;
        const cHi = Math.floor(id.client / 4294967296) >>> 0;
        const clk = id.clock >>> 0;
        return withInputFrame(key.length * 3 + 8, () => {
          const klen = writeUtf8Raw(key, inPtr);
          wPos = inPtr + klen;
          const code = checkOk(
            exp.session_map_set_f64_id(
              this._handle,
              cLo,
              cHi,
              clk,
              klen,
              anyVal,
            ),
          );
          if (code === 1) return null;
          rStart();
          return rCommitBody();
        });
      }
      return withInputFrame(1024, () => {
        wU32(12);
        wTarget(target);
        wStr(key);
        if (hasAny) {
          wU32(0);
          wAny(anyVal);
        } else {
          wSessionValue(value);
        }
        this._exec();
        return rOptCommit();
      });
    }

    mapRemove(target, key) {
      return withInputFrame(1024, () => {
        wU32(13);
        wTarget(target);
        wStr(key);
        this._exec();
        return rOptCommit();
      });
    }

    mapClear(target) {
      return withInputFrame(1024, () => {
        wU32(28);
        wTarget(target);
        this._exec();
        return rOptCommit();
      });
    }

    arrayInsert(target, index, values) {
      return withInputFrame(1024, () => {
        wU32(14);
        wTarget(target);
        wU64(index);
        wU32(values.length);
        for (let i = 0; i < values.length; i++) wSessionValue(values[i]);
        this._exec();
        return rOptCommit();
      });
    }

    arrayPush(target, values) {
      return withInputFrame(1024, () => {
        wU32(15);
        wTarget(target);
        wU32(values.length);
        for (let i = 0; i < values.length; i++) wSessionValue(values[i]);
        this._exec();
        return rOptCommit();
      });
    }

    arrayRemove(target, index, len) {
      return withInputFrame(1024, () => {
        wU32(29);
        wTarget(target);
        wU64(index);
        wU64(len);
        this._exec();
        return rOptCommit();
      });
    }

    textInsert(target, index, text) {
      if (target.Identity && index <= 0xffffffff) {
        const idxU32 = index >>> 0;
        if (Object.hasOwn(target.Identity, "Root")) {
          const root = target.Identity.Root;
          return withInputFrame((root.length + text.length) * 3 + 16, () => {
            const rlen = writeUtf8Raw(root, inPtr);
            const tlen = writeUtf8Raw(text, inPtr + rlen);
            wPos = inPtr + rlen + tlen;
            const code = checkOk(
              exp.session_text_insert_root(this._handle, rlen, idxU32, tlen),
            );
            if (code === 1) return null;
            rStart();
            return rCommitBody();
          });
        }
        const id = target.Identity.Item;
        if (id.clock <= 0xffffffff) {
          const cLo = id.client >>> 0;
          const cHi = Math.floor(id.client / 4294967296) >>> 0;
          const clk = id.clock >>> 0;
          return withInputFrame(text.length * 3 + 8, () => {
            const tlen = writeUtf8Raw(text, inPtr);
            wPos = inPtr + tlen;
            const code = checkOk(
              exp.session_text_insert_id(
                this._handle,
                cLo,
                cHi,
                clk,
                idxU32,
                tlen,
              ),
            );
            if (code === 1) return null;
            rStart();
            return rCommitBody();
          });
        }
      }
      return withInputFrame(1024, () => {
        wU32(16);
        wTarget(target);
        wU64(index);
        wStr(text);
        this._exec();
        return rOptCommit();
      });
    }

    textRemove(target, index, len) {
      if (
        target.Identity &&
        target.Identity.Item &&
        target.Identity.Item.clock <= 0xffffffff &&
        index <= 0xffffffff &&
        len <= 0xffffffff
      ) {
        const id = target.Identity.Item;
        const cLo = id.client >>> 0;
        const cHi = Math.floor(id.client / 4294967296) >>> 0;
        const clk = id.clock >>> 0;
        const idxU32 = index >>> 0;
        const lenU32 = len >>> 0;
        const code = checkOk(
          exp.session_text_remove_id(
            this._handle,
            cLo,
            cHi,
            clk,
            idxU32,
            lenU32,
          ),
        );
        if (code === 1) return null;
        rStart();
        return rCommitBody();
      }
      return withInputFrame(1024, () => {
        wU32(17);
        wTarget(target);
        wU64(index);
        wU64(len);
        this._exec();
        return rOptCommit();
      });
    }

    textFormat(target, index, len, attrs) {
      return withInputFrame(1024, () => {
        wU32(30);
        wTarget(target);
        wU64(index);
        wU64(len);
        wFormat(attrs);
        this._exec();
        return rOptCommit();
      });
    }

    textInsertEmbed(target, index, embed) {
      return withInputFrame(1024, () => {
        wU32(31);
        wTarget(target);
        wU64(index);
        wAny(embed);
        this._exec();
        return rOptCommit();
      });
    }

    textApplyDelta(target, delta) {
      return withInputFrame(1024, () => {
        wU32(18);
        wTarget(target);
        wDelta(delta);
        this._exec();
        return rOptCommit();
      });
    }

    xmlName(target) {
      return withInputFrame(1024, () => {
        wU32(34);
        wTarget(target);
        this._exec();
        return rStr();
      });
    }

    xmlSetAttr(target, key, value) {
      return withInputFrame(1024, () => {
        wU32(35);
        wTarget(target);
        wStr(key);
        wAny(value);
        this._exec();
        return rOptCommit();
      });
    }

    xmlGetAttr(target, key) {
      return withInputFrame(1024, () => {
        wU32(36);
        wTarget(target);
        wStr(key);
        this._exec();
        return rU32() === 0 ? null : rAny();
      });
    }

    xmlRemoveAttr(target, key) {
      return withInputFrame(1024, () => {
        wU32(37);
        wTarget(target);
        wStr(key);
        this._exec();
        return rOptCommit();
      });
    }

    xmlAttrs(target) {
      return withInputFrame(1024, () => {
        wU32(38);
        wTarget(target);
        this._exec();
        const len = rU32();
        const out = new Array(len);
        for (let i = 0; i < len; i++) out[i] = [rStr(), rAny()];
        return out;
      });
    }

    xmlToString(target) {
      return withInputFrame(1024, () => {
        wU32(39);
        wTarget(target);
        this._exec();
        return rStr();
      });
    }

    createRelativePosition(target, index, assoc = 0) {
      return withInputFrame(1024, () => {
        wU32(40);
        wTarget(target);
        wU64(index);
        wI64(assoc);
        this._exec();
        return { bytes: rBytes() };
      });
    }

    resolveRelativePosition(bytes, followUndoneDeletions = false) {
      return withInputFrame(1024, () => {
        wU32(41);
        wBytes(bytes);
        wU32(followUndoneDeletions ? 1 : 0);
        this._exec();
        if (rU32() === 0) return null;
        return { type: rIdentity(), index: rU64(), assoc: rI64() };
      });
    }

    advanceTime(nowMs) {
      return withInputFrame(64, () => {
        wU32(42);
        wU64(Number(nowMs));
        this._exec();
        return rU32() !== 0;
      });
    }

    setUndoSelectionMeta(metaBytes) {
      return withInputFrame(1024, () => {
        wU32(43);
        wBytes(metaBytes);
        this._exec();
        return rU32() !== 0;
      });
    }

    undo() {
      return withInputFrame(64, () => {
        wU32(19);
        this._exec();
        return rOptCommit();
      });
    }

    redo() {
      return withInputFrame(64, () => {
        wU32(20);
        this._exec();
        return rOptCommit();
      });
    }

    stopCapturing() {
      return withInputFrame(64, () => {
        wU32(44);
        this._exec();
        return rU32() !== 0;
      });
    }

    clearHistory(undo = true, redo = true) {
      return withInputFrame(64, () => {
        wU32(45);
        wU32(undo ? 1 : 0);
        wU32(redo ? 1 : 0);
        this._exec();
        return rU32() !== 0;
      });
    }

    canUndo() {
      return exp.session_can_undo(this._handle) !== 0;
    }

    canRedo() {
      return exp.session_can_redo(this._handle) !== 0;
    }

    createUndoStack(
      scopes = [],
      captureTimeoutMs = 500,
      trackedOrigins = ["Tracked"],
    ) {
      return withInputFrame(1024, () => {
        wU32(47);
        wU32(scopes.length);
        for (let i = 0; i < scopes.length; i++) wTarget(scopes[i]);
        wU64(captureTimeoutMs);
        wU32(trackedOrigins.length);
        for (let i = 0; i < trackedOrigins.length; i++)
          wTxOrigin(trackedOrigins[i]);
        this._exec();
        return rU32();
      });
    }

    undoStack(stackId) {
      return withInputFrame(64, () => {
        wU32(48);
        wU32(stackId);
        this._exec();
        return rOptCommit();
      });
    }

    redoStack(stackId) {
      return withInputFrame(64, () => {
        wU32(49);
        wU32(stackId);
        this._exec();
        return rOptCommit();
      });
    }

    canUndoStack(stackId) {
      return withInputFrame(64, () => {
        wU32(50);
        wU32(stackId);
        this._exec();
        return rU32() !== 0;
      });
    }

    canRedoStack(stackId) {
      return withInputFrame(64, () => {
        wU32(51);
        wU32(stackId);
        this._exec();
        return rU32() !== 0;
      });
    }

    setStackSelectionMeta(stackId, stack, metaBytes) {
      return withInputFrame(1024, () => {
        wU32(52);
        wU32(stackId);
        wU32(stack === "Redo" ? 1 : 0);
        wBytes(metaBytes);
        this._exec();
        return rU32() !== 0;
      });
    }

    stopCapturingStack(stackId) {
      return withInputFrame(64, () => {
        wU32(53);
        wU32(stackId);
        this._exec();
        return rU32() !== 0;
      });
    }

    clearStackHistory(stackId, undo = true, redo = true) {
      return withInputFrame(64, () => {
        wU32(54);
        wU32(stackId);
        wU32(undo ? 1 : 0);
        wU32(redo ? 1 : 0);
        this._exec();
        return rU32() !== 0;
      });
    }

    destroyUndoStack(stackId) {
      return withInputFrame(64, () => {
        wU32(55);
        wU32(stackId);
        this._exec();
        return rU32() !== 0;
      });
    }

    applyUpdateV1(update) {
      const src =
        update instanceof Uint8Array ? update : new Uint8Array(update);
      return withInputFrame(src.length, () => {
        u8.set(src, inPtr);
        wPos = inPtr + src.length;
        const code = checkOk(
          exp.session_apply_update_v1(this._handle, src.length),
        );
        const count = code - 1;
        if (count === 0) return [];
        rStart();
        const commits = [];
        for (let i = 0; i < count; i++) {
          commits.push(rCommitBody());
        }
        return commits;
      });
    }

    encodeUpdateV1() {
      checkOk(exp.session_encode_update_v1(this._handle));
      return readRawOutBytes();
    }

    encodeStateVectorV1() {
      checkOk(exp.session_encode_sv_v1(this._handle));
      return readRawOutBytes();
    }

    encodeDiffV1(remoteSv) {
      const src =
        remoteSv instanceof Uint8Array ? remoteSv : new Uint8Array(remoteSv);
      return withInputFrame(src.length, () => {
        u8.set(src, inPtr);
        wPos = inPtr + src.length;
        checkOk(exp.session_encode_diff_v1(this._handle, src.length));
        return readRawOutBytes();
      });
    }
  }

  class Awareness {
    constructor(localId) {
      this._handle = exp.awareness_create(BigInt(localId));
      if (!this._handle) {
        throw new Error(readError() || "awareness_create failed");
      }
    }

    free() {
      if (this._handle) {
        exp.awareness_free(this._handle);
        this._handle = 0;
      }
    }

    localId() {
      return Number(exp.awareness_local_id(this._handle));
    }

    setLocalId(newLocalId) {
      checkOk(exp.awareness_set_local_id(this._handle, BigInt(newLocalId)));
      rStart();
      return rAwarenessEvent();
    }

    setLocalState(jsonString) {
      withInputFrame(jsonString.length * 3 + 16, () => {
        const len = writeUtf8Raw(jsonString, inPtr);
        wPos = inPtr + len;
        checkOk(exp.awareness_set_local_state(this._handle, len));
      });
    }

    clearLocalState() {
      checkOk(exp.awareness_clear_local_state(this._handle));
    }

    getStates() {
      checkOk(exp.awareness_get_states(this._handle));
      rStart();
      const count = rU32();
      const map = new Map();
      for (let i = 0; i < count; i++) {
        const id = rU64();
        const clock = rU64();
        const content = rStr();
        const deleted = rU32() !== 0;
        map.set(id, { clock, content, deleted });
      }
      return map;
    }

    encodeUpdate(clients = null) {
      if (clients == null) {
        checkOk(exp.awareness_encode_update(this._handle, 0, 0));
        return readRawOutBytes();
      }
      if (clients.length === 0) {
        checkOk(exp.awareness_encode_update(this._handle, 1, 0));
        return readRawOutBytes();
      }
      return withInputFrame(clients.length * 8, () => {
        for (let i = 0; i < clients.length; i++) wU64(Number(clients[i]));
        checkOk(exp.awareness_encode_update(this._handle, 1, clients.length));
        return readRawOutBytes();
      });
    }

    applyUpdateV1(bytes) {
      const src = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
      return withInputFrame(src.length, () => {
        u8.set(src, inPtr);
        wPos = inPtr + src.length;
        checkOk(exp.awareness_apply_update_v1(this._handle, src.length));
        rStart();
        return rAwarenessEvent();
      });
    }
  }

  return {
    abiVersion: exp.wasm_abi_version(),
    DocSession,
    Awareness,
    validateUpdateV1,
    encodeStateVectorFromUpdateV1,
    diffUpdateV1,
    mergeUpdatesV1,
    revertUpdateV1,
    trimScratch,
  };
}
