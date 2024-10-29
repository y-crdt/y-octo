import * as Y from "./yocto";
import { Array } from "./array";
import { Map } from "./map";
import type { Text } from "./text";

export class Doc extends Y.Doc {
  private cachedArray: globalThis.Map<string, Array> = new globalThis.Map();
  private cachedMap: globalThis.Map<string, Map> = new globalThis.Map();
  private subscribers: Set<(result: Uint8Array, origin?: unknown) => void> =
    new Set();
  private lastState: Buffer | null = null;

  getArray(key = ""): Array {
    if (this.cachedArray.has(key)) {
      return this.cachedArray.get(key)!;
    }
    const yarray = new Array([], this, this.getOrCreateArray(key));
    this.cachedArray.set(key, yarray);
    return yarray;
  }

  getMap(key = ""): Map {
    if (this.cachedMap.has(key)) {
      return this.cachedMap.get(key)!;
    }
    const ymap = new Map({}, this, this.getOrCreateMap(key));
    this.cachedMap.set(key, ymap);
    return ymap;
  }

  getText(key = ""): Text {
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
