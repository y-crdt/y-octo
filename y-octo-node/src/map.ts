import * as Y from "./yocto";
import { Array } from "./array";
import type { Doc } from "./doc";
import type { ListItem } from "./types";

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
