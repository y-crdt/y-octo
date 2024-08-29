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

export const Doc = Y.Doc;

export class Array {
  private ytype?: { doc: Y.Doc; array: Y.YArray };
  private preliminary: any[] = [];

  static from<T extends ArrayType>(items: T[]): Array {
    return new Array(items);
  }

  constructor(items: ArrayType[], ydoc?: Y.YDoc) {
    this.preliminary = items;
    if (ydoc) this.integrate(ydoc);
  }

  integrate(ydoc: Y.YDoc): Y.YArray {
    if (!this.ytype) {
      this.ytype = { doc: ydoc, array: ydoc.createArray() };
      for (const item of this.preliminary) {
        if (item instanceof Array) {
          this.ytype.array.push(item.integrate(ydoc));
        } else {
          this.ytype.array.push(item);
        }
      }
      this.preliminary = [];
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
    } else {
      this.preliminary.splice(index, 0, value);
    }
  }

  push(value?: ListItem): void {
    if (this.ytype) {
      this.ytype.array.push(value);
    } else {
      this.preliminary.push(value);
    }
  }

  unshift(value?: ListItem): void {
    if (this.ytype) {
      this.ytype.array.unshift(value);
    } else {
      this.preliminary.unshift(value);
    }
  }

  delete(index: number, len?: number): void {
    if (this.ytype) {
      this.ytype.array.delete(index, len);
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
  private ytype?: { doc: Y.Doc; map: Y.YMap };
  private preliminary: Record<string, any> = {};

  constructor(items: Record<string, any>, ydoc?: Y.YDoc) {
    this.preliminary = items;
    if (ydoc) this.integrate(ydoc);
  }

  integrate(ydoc: Y.YDoc): Y.YMap {
    if (!this.ytype) {
      this.ytype = { doc: ydoc, map: ydoc.createMap() };
      for (const [key, val] of Object.entries(this.preliminary)) {
        if (val instanceof Array) {
          this.ytype.map.set(key, val.integrate(ydoc));
        } else {
          this.ytype.map.set(key, val);
        }
      }
      this.preliminary = {};
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
    return this.ytype ? this.ytype.map.get(key) : this.preliminary[key];
  }

  set<T = ListItem>(key: string, value: T) {
    if (this.ytype) {
      if (value instanceof Array || value instanceof Map) {
        this.ytype.map.set(key, value.integrate(this.ytype.doc));
      } else {
        this.ytype.map.set(key, value);
      }
    } else {
      this.preliminary[key] = value;
    }
  }

  delete(key: string): void {
    if (this.ytype) {
      this.ytype.map.delete(key);
    } else {
      delete this.preliminary[key];
    }
  }

  clear(): void {
    if (this.ytype) {
      this.ytype.map.clear();
    } else {
      this.preliminary = {};
    }
  }

  toJson(): Record<string, any> {
    return this.ytype
      ? this.ytype.map.toJson()
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
