import * as Y from "./yocto";
import type { Doc } from "./doc";

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
