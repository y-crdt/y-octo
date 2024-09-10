import * as Y from "./yocto";

type ArrayType =
  | string
  | number
  | any[]
  | Uint8Array
  | { [x: string]: any }
  | null;
type ListItem =
  | Array
  | Map
  | Text
  | boolean
  | number
  | string
  | Record<string, any>
  | null;

export class Doc extends Y.Doc {
  private cachedArray: globalThis.Map<string, Array> = new globalThis.Map();
  private cachedMap: globalThis.Map<string, Map> = new globalThis.Map();
  private subscribers: Set<(result: Uint8Array, origin?: unknown) => void> =
    new Set();
  private lastState: Buffer | null = null;

  getArray(key: string): Array {
    if (this.cachedArray.has(key)) {
      return this.cachedArray.get(key)!;
    }
    const yarray = new Array([], this, this.getOrCreateArray(key));
    this.cachedArray.set(key, yarray);
    return yarray;
  }

  getMap(key: string): Map {
    if (this.cachedMap.has(key)) {
      return this.cachedMap.get(key)!;
    }
    const ymap = new Map({}, this, this.getOrCreateMap(key));
    this.cachedMap.set(key, ymap);
    return ymap;
  }

  getText(key: string): Text {
    return this.getOrCreateText(key);
  }

  triggerDiff(origin?: unknown): void {
    let diff: Buffer | null = null;
    if (this.lastState) {
      diff = this.diff(this.lastState);
      const state = this.encodeStateAsUpdateV1();
      if (!this.lastState.equals(state)) {
        this.lastState = state;
      } else {
        return;
      }
    } else {
      this.lastState = this.encodeStateAsUpdateV1();
      diff = this.diff(this.lastState);
    }

    // skip empty diffs
    if (!diff || diff.equals(new Uint8Array([0, 0]))) {
      return;
    }

    if (this.lastState?.length && diff?.length) {
      this.subscribers.forEach((callback) =>
        callback(new Uint8Array(diff!), origin || this),
      );
    }
  }

  transact(callback: (...args: any[]) => any, origin?: unknown): void {
    try {
      callback();
    } finally {
      this.triggerDiff(origin);
    }
  }

  override applyUpdate(update: Buffer): void {
    this.transact(() => {
      super.applyUpdate(update);
    });
  }

  override onUpdate(
    callback: (result: Uint8Array, origin?: unknown) => void,
  ): void {
    this.subscribers.add(callback);
  }

  override offUpdate(): void {
    this.subscribers.clear();
  }
}

export class Protocol extends Y.YProtocol {
  constructor(private readonly doc: Doc) {
    super(doc);
  }

  override applySyncStep(buffer: Buffer): Buffer | null {
    try {
      return super.applySyncStep(buffer);
    } finally {
      this.doc.triggerDiff(this.doc);
    }
  }
}

export class Array {
  private ytype?: { doc: Doc; array: Y.YArray };
  private preliminary: any[] = [];

  get itemId() {
    return this.ytype?.array.itemId;
  }

  static from<T extends ArrayType>(items: T[]): Array {
    return new Array(items);
  }

  static from_ytype(ytype?: { doc: Doc; array: Y.YArray }) {
    const array = new Array();
    array.ytype = ytype;
    return array;
  }

  constructor(items: ArrayType[] = [], ydoc?: Doc, yarray?: Y.YArray) {
    this.preliminary = items;
    if (ydoc) this.integrate(ydoc, yarray);
  }

  integrate(ydoc: Doc, yarray?: Y.YArray): Y.YArray {
    if (!this.ytype) {
      this.ytype = { doc: ydoc, array: yarray || ydoc.createArray() };
      for (const item of this.preliminary) {
        if (item instanceof Array) {
          this.ytype.array.push(item.integrate(ydoc));
        } else {
          this.ytype.array.push(item);
        }
      }
      this.preliminary = [];
      this.ytype.doc.triggerDiff();
    }
    return this.ytype.array;
  }

  get length(): number {
    return this.ytype ? this.ytype.array.length : this.preliminary.length;
  }

  get isEmpty(): boolean {
    return this.ytype
      ? this.ytype.array.isEmpty
      : this.preliminary.length === 0;
  }

  get<T = unknown>(index: number): T {
    return this.ytype ? this.ytype.array.get(index) : this.preliminary[index];
  }

  slice<T = unknown>(start: number, end?: number): T[] {
    return this.ytype
      ? this.ytype.array.slice(start, end)
      : this.preliminary.slice(start, end);
  }

  map<T = unknown>(callback: (...args: any[]) => any): T[] {
    return this.ytype
      ? this.ytype.array.map(callback)
      : this.preliminary.map(callback);
  }

  insert(index: number, value: ListItem): void {
    if (this.ytype) {
      if (value instanceof Array || value instanceof Map) {
        this.ytype.array.insert(index, value.integrate(this.ytype.doc));
      } else {
        this.ytype.array.insert(index, value);
      }
      this.ytype.doc.triggerDiff();
    } else {
      this.preliminary.splice(index, 0, value);
    }
  }

  push(value?: ListItem): void {
    if (this.ytype) {
      this.ytype.array.push(value);
      this.ytype.doc.triggerDiff();
    } else {
      this.preliminary.push(value);
    }
  }

  unshift(value?: ListItem): void {
    if (this.ytype) {
      this.ytype.array.unshift(value);
      this.ytype.doc.triggerDiff();
    } else {
      this.preliminary.unshift(value);
    }
  }

  delete(index: number, len?: number): void {
    if (this.ytype) {
      this.ytype.array.delete(index, len);
      this.ytype.doc.triggerDiff();
    } else {
      this.preliminary.splice(index, len);
    }
  }

  iter(): Y.YArrayIterator {
    return this.ytype
      ? this.ytype.array.iter()
      : this.preliminary[Symbol.iterator]();
  }

  toArray(): any[] {
    return this.ytype ? this.ytype.array.toArray() : this.preliminary;
  }

  toJSON(): any[] {
    return this.ytype ? this.ytype.array.toJSON() : this.preliminary;
  }

  observe(callback: (...args: any[]) => any): void {
    if (this.ytype) {
      this.ytype.array.observe(callback);
    } else {
      throw new Error("Not implemented");
    }
  }

  observeDeep(callback: (...args: any[]) => any): void {
    if (this.ytype) {
      this.ytype.array.observeDeep(callback);
    } else {
      throw new Error("Not implemented");
    }
  }
}

export class Map {
  private ytype?: { doc: Doc; map: Y.YMap };
  private preliminary: Record<string, any> = {};

  static from_ytype(ytype?: { doc: Doc; map: Y.YMap }) {
    const map = new Map();
    map.ytype = ytype;
    return map;
  }

  constructor(items: Record<string, any> = {}, ydoc?: Doc, ymap?: Y.YMap) {
    this.preliminary = items;
    if (ydoc) this.integrate(ydoc, ymap);
  }

  integrate(ydoc: Doc, ymap?: Y.YMap): Y.YMap {
    if (!this.ytype) {
      this.ytype = { doc: ydoc, map: ymap || ydoc.createMap() };
      for (const [key, val] of Object.entries(this.preliminary)) {
        if (val instanceof Array) {
          this.ytype.map.set(key, val.integrate(ydoc));
        } else {
          this.ytype.map.set(key, val);
        }
      }
      this.preliminary = {};
      this.ytype.doc.triggerDiff();
    }
    return this.ytype.map;
  }

  get length(): number {
    return this.ytype
      ? this.ytype.map.length
      : Object.keys(this.preliminary).length;
  }

  get size(): number {
    return this.length;
  }

  get isEmpty(): boolean {
    return this.ytype ? this.ytype.map.isEmpty : this.length === 0;
  }

  get itemId(): Y.YId | null {
    return this.ytype?.map.itemId || null;
  }

  get<T = unknown>(key: string): T {
    if (this.ytype) {
      const ret = this.ytype.map.get(key);
      if (ret) {
        if (ret instanceof Y.YArray) {
          return Array.from_ytype({ doc: this.ytype.doc, array: ret }) as T;
        } else if (ret instanceof Y.YMap) {
          return Map.from_ytype({ doc: this.ytype.doc, map: ret }) as T;
        }
      }
      return ret as T;
    } else {
      return this.preliminary[key];
    }
  }

  set<T = ListItem>(key: string, value: T) {
    if (this.ytype) {
      if (value instanceof Array || value instanceof Map) {
        this.ytype.map.set(key, value.integrate(this.ytype.doc));
      } else {
        this.ytype.map.set(key, value);
      }
      this.ytype.doc.triggerDiff();
    } else {
      this.preliminary[key] = value;
    }
    return value;
  }

  delete(key: string): void {
    if (this.ytype) {
      this.ytype.map.delete(key);
      this.ytype.doc.triggerDiff();
    } else {
      delete this.preliminary[key];
    }
  }

  clear(): void {
    if (this.ytype) {
      this.ytype.map.clear();
      this.ytype.doc.triggerDiff();
    } else {
      this.preliminary = {};
    }
  }

  toJSON(): Record<string, any> {
    return this.ytype
      ? this.ytype.map.toJSON()
      : JSON.parse(JSON.stringify(this.preliminary));
  }

  entries(): Y.YMapEntriesIterator {
    return this.ytype
      ? this.ytype.map.entries()
      : Object.entries(this.preliminary);
  }

  keys(): Y.YMapKeyIterator {
    return this.ytype ? this.ytype.map.keys() : Object.keys(this.preliminary);
  }

  values(): Y.YMapValuesIterator {
    return this.ytype
      ? this.ytype.map.values()
      : Object.values(this.preliminary);
  }

  observe(callback: (...args: any[]) => any): void {
    if (this.ytype) {
      this.ytype.map.observe(callback);
    } else {
      throw new Error("Not implemented");
    }
  }

  observeDeep(callback: (...args: any[]) => any): void {
    if (this.ytype) {
      this.ytype.map.observeDeep(callback);
    } else {
      throw new Error("Not implemented");
    }
  }
}

export class Text extends Y.YText {}

export * from "./yocto";
