import * as Y from "./yocto";
import { Doc } from "./doc";
import { Map } from "./map";
import type { ArrayType, ListItem } from "./types";

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
