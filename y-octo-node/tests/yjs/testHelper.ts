import assert, { deepEqual } from "node:assert";
import * as prng from "lib0/prng";
import * as object from "lib0/object";
import * as map from "lib0/map";
import * as Y from "../../index";

if (typeof window !== "undefined") {
  // @ts-ignore
  window.Y = Y; // eslint-disable-line
}

/**
 * @param {TestYInstance} y // publish message created by `y` to all other online clients
 * @param {Uint8Array} m
 */
const broadcastMessage = (y: TestYOctoInstance, m: Uint8Array) => {
  if (y.tc.onlineConns.has(y)) {
    y.tc.onlineConns.forEach(
      (remoteYInstance: { _receive: (arg0: any, arg1: any) => void }) => {
        if (remoteYInstance !== y) {
          remoteYInstance._receive(m, y);
        }
      },
    );
  }
};

export class TestYOctoInstance extends Y.Doc {
  protocol: Y.Protocol;
  updates: Uint8Array[];
  receiving: Map<TestYOctoInstance, Uint8Array[]>;
  tc: TestConnector;
  constructor(testConnector: TestConnector, clientID: number) {
    super(clientID); // overwriting clientID

    this.protocol = new Y.Protocol(this);
    this.tc = testConnector;
    this.receiving = new Map();
    testConnector.allConns.add(this);
    this.updates = [];
    // set up observe on local model
    this.onUpdate((update, origin) => {
      if (origin !== testConnector) {
        console.error("broadcasting update");
        broadcastMessage(
          this,
          this.protocol.encodeSyncStep(3, Buffer.from(update)),
        );
      }
      this.updates.push(update);
    });
    this.connect();
  }

  /**
   * Disconnect from TestConnector.
   */
  disconnect() {
    this.offUpdate();
    this.receiving = new Map();
    this.tc.onlineConns.delete(this);
  }

  /**
   * Append yourself to the list of known Y instances in testconnector.
   * Also initiate sync with all clients.
   */
  connect() {
    if (!this.tc.onlineConns.has(this)) {
      this.tc.onlineConns.add(this);
      // publish SyncStep1
      broadcastMessage(this, this.protocol.encodeSyncStep(1));
      this.tc.onlineConns.forEach((remoteYInstance) => {
        if (remoteYInstance !== this) {
          // remote instance sends instance to this instance
          this._receive(
            remoteYInstance.protocol.encodeSyncStep(1),
            remoteYInstance,
          );
        }
      });
    }
  }

  /**
   * Receive a message from another client. This message is only appended to the list of receiving messages.
   * TestConnector decides when this client actually reads this message.
   */
  _receive(message: Uint8Array, remoteClient: TestYOctoInstance) {
    map
      .setIfUndefined(this.receiving, remoteClient, () => [] as Uint8Array[])
      .push(message);
  }
}

/**
 * Keeps track of TestYInstances.
 *
 * The TestYInstances add/remove themselves from the list of connections maiained in this object.
 * I think it makes sense. Deal with it.
 */
export class TestConnector {
  allConns: Set<TestYOctoInstance>;
  onlineConns: Set<TestYOctoInstance>;
  prng: prng.PRNG;
  constructor(gen: prng.PRNG) {
    this.allConns = new Set();
    this.onlineConns = new Set();
    this.prng = gen;
  }

  createY(clientID: number) {
    return new TestYOctoInstance(this, clientID);
  }

  /**
   * Choose random connection and flush a random message from a random sender.
   *
   * If this function was unable to flush a message, because there are no more messages to flush, it returns false. true otherwise.
   */
  flushRandomMessage(): boolean {
    const gen = this.prng;
    const conns = Array.from(this.onlineConns).filter(
      (conn) => conn.receiving.size > 0,
    );
    if (conns.length > 0) {
      const receiver = prng.oneOf(gen, conns);
      const [sender, messages] = prng.oneOf(
        gen,
        Array.from(receiver.receiving),
      );

      const m = messages.shift();
      if (messages.length === 0) {
        receiver.receiving.delete(sender);
      }
      if (m === undefined) {
        return this.flushRandomMessage();
      }

      // do not publish data created when this function is executed (could be ss2 or update message)
      const update = receiver.protocol.applySyncStep(Buffer.from(m));
      if (update) {
        // send reply message
        sender._receive(update, receiver);
      }
      return true;
    }
    return false;
  }

  /**
   * @return {boolean} True iff this function actually flushed something
   */
  flushAllMessages(): boolean {
    let didSomething = false;
    while (this.flushRandomMessage()) {
      didSomething = true;
    }
    return didSomething;
  }

  reconnectAll() {
    this.allConns.forEach((conn) => conn.connect());
  }

  disconnectAll() {
    this.allConns.forEach((conn) => conn.disconnect());
  }

  syncAll() {
    this.reconnectAll();
    this.flushAllMessages();
  }

  /**
   * @return {boolean} Whether it was possible to disconnect a randon connection.
   */
  disconnectRandom(): boolean {
    if (this.onlineConns.size === 0) {
      return false;
    }
    prng.oneOf(this.prng, Array.from(this.onlineConns)).disconnect();
    return true;
  }

  /**
   * @return {boolean} Whether it was possible to reconnect a random connection.
   */
  reconnectRandom(): boolean {
    const reconnectable: TestYOctoInstance[] = [];
    this.allConns.forEach((conn: any) => {
      if (!this.onlineConns.has(conn)) {
        reconnectable.push(conn);
      }
    });
    if (reconnectable.length === 0) {
      return false;
    }
    prng.oneOf(this.prng, reconnectable).connect();
    return true;
  }
}

type InitResult = {
  testConnector: TestConnector;
  users: Array<TestYOctoInstance>;
  testObjects: Array<any>;
  array0: Y.Array;
  array1: Y.Array;
  array2: Y.Array;
  map0: Y.Map;
  map1: Y.Map;
  map2: Y.Map;
  map3: Y.Map;
  text0: Y.Text;
  text1: Y.Text;
  text2: Y.Text;
  // xml0: Y.XmlElement;
  // xml1: Y.XmlElement;
  // xml2: Y.XmlElement;
};
export const init = (
  gen: prng.PRNG,
  { users = 5 }: { users?: number } = {},
  initTestObject?: any,
): InitResult => {
  // @ts-expect-error expect
  const result: InitResult = {
    users: [],
    testConnector: new TestConnector(gen),
  };
  for (let i = 0; i < users; i++) {
    const y = result.testConnector.createY(i);
    y.clientId = i;
    result.users.push(y);
    result["array" + i] = y.getArray("array");
    result["map" + i] = y.getMap("map");
    // result["xml" + i] = y.get("xml", Y.XmlElement);
    result["text" + i] = y.getText("text");
  }
  result.testConnector.syncAll();
  result.testObjects = result.users.map(initTestObject || (() => null));
  return result;
};

/**
 * 1. reconnect and flush all
 * 2. user 0 gc
 * 3. get type content
 * 4. disconnect & reconnect all (so gc is propagated)
 * 5. compare os, ds, ss
 */
export const compare = (users: TestYOctoInstance[]) => {
  users.forEach((u) => u.connect());
  while (users[0].tc.flushAllMessages()) {} // eslint-disable-line
  // For each document, merge all received document updates with Y.mergeUpdates and create a new document which will be added to the list of "users"
  // This ensures that mergeUpdates works correctly
  const mergedDocs = users.map((user: { updates: any }, i) => {
    const ydoc = new Y.Doc();
    console.error(`Merging user ${i}'s updates: ${user.updates.join(", ")}`);
    ydoc.applyUpdate(Y.mergeUpdates(user.updates));
    console.error("Merged user", ydoc.getArray("array").toJSON());
    return ydoc;
  });
  users.push(...mergedDocs);
  const userArrayValues = users.map((u) => u.getArray("array").toJSON());
  const userMapValues = users.map((u) => u.getMap("map").toJson());
  // const userXmlValues = users.map(
  //   (u: {
  //     get: (
  //       arg0: string,
  //       arg1: any,
  //     ) => { (): any; new (): any; toString: { (): any; new (): any } };
  //   }) => u.get("xml", Y.XmlElement).toString(),
  // );
  // const userTextValues = users.map((u) => u.getText("text").toDelta());
  // for (const u of users) {
  //   t.assert(u.store.pendingDs === null);
  //   t.assert(u.store.pendingStructs === null);
  // }
  // Test Array iterator
  deepEqual(
    users[0].getArray("array").toArray(),
    Array.from(users[0].getArray("array").iter()),
  );
  // Test Map iterator
  const ymapkeys: any[] = Array.from(users[0].getMap("map").keys());
  assert(ymapkeys.length === Object.keys(userMapValues[0]).length);
  ymapkeys.forEach((key) => assert(object.hasProperty(userMapValues[0], key)));

  const mapRes: Record<string, any> = {};
  for (const [k, v] of users[0].getMap("map").entries()) {
    mapRes[k] = Y.isAbstractType(v) ? v.toJSON() : v;
  }
  deepEqual(userMapValues[0], mapRes);
  // Compare all users
  for (let i = 0; i < users.length - 1; i++) {
    deepEqual(userArrayValues[i].length, users[i].getArray("array").length);
    deepEqual(
      userArrayValues[i],
      userArrayValues[i + 1],
      `array${i} !== array${i + 1}`,
    );
    deepEqual(
      userMapValues[i],
      userMapValues[i + 1],
      `map${i} !== map${i + 1}`,
    );
    // deepEqual(userXmlValues[i], userXmlValues[i + 1]);
    // deepEqual(
    //   userTextValues[i]
    //     .map(
    //       /** @param {any} a */ (a: { insert: any }) =>
    //         typeof a.insert === "string" ? a.insert : " ",
    //     )
    //     .join("").length,
    //   users[i].getText("text").length,
    // );
    // deepEqual(
    //   userTextValues[i],
    //   userTextValues[i + 1],
    //   "",
    //   (_constructor, a, b) => {
    //     if (Y.isAbstractType(a)) {
    //       deepEqual(a.toJSON(), b.toJSON());
    //     } else if (a !== b) {
    //       t.fail("Deltas dont match");
    //     }
    //     return true;
    //   },
    // );
    deepEqual(Y.encodeStateVector(users[i]), Y.encodeStateVector(users[i + 1]));
    Y.equalDeleteSets(
      Y.createDeleteSetFromStructStore(users[i].store),
      Y.createDeleteSetFromStructStore(users[i + 1].store),
    );
    Y.compareStructStores(users[i].store, users[i + 1].store);
    deepEqual(
      Y.encodeSnapshot(Y.snapshot(users[i])),
      Y.encodeSnapshot(Y.snapshot(users[i + 1])),
    );
  }
  // users.map((u) => u.destroy());
};

export const applyRandomTests = (
  gen: prng.PRNG,
  mods: unknown[],
  iterations: number,
  initTestObject?: any,
) => {
  const result = init(gen, { users: 5 }, initTestObject);
  const { testConnector, users } = result;
  for (let i = 0; i < iterations; i++) {
    if (prng.int32(gen, 0, 100) <= 2) {
      // 2% chance to disconnect/reconnect a random user
      if (prng.bool(gen)) {
        testConnector.disconnectRandom();
      } else {
        testConnector.reconnectRandom();
      }
    } else if (prng.int32(gen, 0, 100) <= 1) {
      // 1% chance to flush all
      testConnector.flushAllMessages();
    } else if (prng.int32(gen, 0, 100) <= 50) {
      // 50% chance to flush a random message
      testConnector.flushRandomMessage();
    }
    const user = prng.int32(gen, 0, users.length - 1);
    const test: any = prng.oneOf(gen, mods);
    test(users[user], gen, result.testObjects?.[user]);
  }
  compare(users);
  return result;
};