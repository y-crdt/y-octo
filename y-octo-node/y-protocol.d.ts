import * as encoding from "lib0/encoding";
import * as decoding from "lib0/decoding";
import { Observable } from "lib0/observable";
import * as Y from "yjs";

export type AwarenessState = Record<string, any>;
export type AwarenessStates = Map<number, AwarenessState>;

export type MetaClientState = {
  clock: number;
  /**
   * unix timestamp
   */
  lastUpdated: number;
};

/**
 * The Awareness class implements a simple shared state protocol that can be used for non-persistent data like awareness information
 * (cursor, username, status, ..). Each client can update its own local state and listen to state changes of
 * remote clients. Every client may set a state of a remote peer to `null` to mark the client as offline.
 *
 * Each client is identified by a unique client id (something we borrow from `doc.clientID`). A client can override
 * its own state by propagating a message with an increasing timestamp (`clock`). If such a message is received, it is
 * applied if the known state of that client is older than the new state (`clock < newClock`). If a client thinks that
 * a remote client is offline, it may propagate a message with
 * `{ clock: currentClientClock, state: null, client: remoteClient }`. If such a
 * message is received, and the known clock of that client equals the received clock, it will override the state with `null`.
 *
 * Before a client disconnects, it should propagate a `null` state with an updated clock.
 *
 * Awareness states must be updated every 30 seconds. Otherwise the Awareness instance will delete the client state.
 */
export class Awareness extends Observable<string> {
  constructor(doc: Y.Doc);
  doc: Y.Doc;
  clientID: number;
  /**
   * Maps from client id to client state
   */
  states: AwarenessStates;
  meta: Map<number, MetaClientState>;
  _checkInterval: any;
  getLocalState(): AwarenessState | null;
  setLocalState(state: AwarenessState | null): void;
  setLocalStateField(field: string, value: any): void;
  getStates(): AwarenessStates;
}

export function removeAwarenessStates(
  awareness: Awareness,
  clients: Array<number>,
  origin: any,
): void;
export function encodeAwarenessUpdate(
  awareness: Awareness,
  clients: Array<number>,
  states?: AwarenessStates,
): Uint8Array;
export function modifyAwarenessUpdate(
  update: Uint8Array,
  modify: (arg0: any) => any,
): Uint8Array;
export function applyAwarenessUpdate(
  awareness: Awareness,
  update: Uint8Array,
  origin: any,
): void;

/**
 * Core Yjs defines two message types:
 * • YjsSyncStep1: Includes the State Set of the sending client. When received, the client should reply with YjsSyncStep2.
 * • YjsSyncStep2: Includes all missing structs and the complete delete set. When received, the client is assured that it
 *   received all information from the remote client.
 *
 * In a peer-to-peer network, you may want to introduce a SyncDone message type. Both parties should initiate the connection
 * with SyncStep1. When a client received SyncStep2, it should reply with SyncDone. When the local client received both
 * SyncStep2 and SyncDone, it is assured that it is synced to the remote client.
 *
 * In a client-server model, you want to handle this differently: The client should initiate the connection with SyncStep1.
 * When the server receives SyncStep1, it should reply with SyncStep2 immediately followed by SyncStep1. The client replies
 * with SyncStep2 when it receives SyncStep1. Optionally the server may send a SyncDone after it received SyncStep2, so the
 * client knows that the sync is finished.  There are two reasons for this more elaborated sync model: 1. This protocol can
 * easily be implemented on top of http and websockets. 2. The server should only reply to requests, and not initiate them.
 * Therefore it is necessary that the client initiates the sync.
 *
 * Construction of a message:
 * [messageType : varUint, message definition..]
 *
 * Note: A message does not include information about the room name. This must to be handled by the upper layer protocol!
 *
 * stringify[messageType] stringifies a message definition (messageType is already read from the bufffer)
 */
export type messageYjsSyncStep1 = 0;
export type messageYjsSyncStep2 = 1;
export type messageYjsUpdate = 2;
export function writeSyncStep1(encoder: encoding.Encoder, doc: Y.Doc): void;
export function writeSyncStep2(
  encoder: encoding.Encoder,
  doc: Y.Doc,
  encodedStateVector?: Uint8Array | undefined,
): void;
export function readSyncStep1(
  decoder: decoding.Decoder,
  encoder: encoding.Encoder,
  doc: Y.Doc,
): void;
export function readSyncStep2(
  decoder: decoding.Decoder,
  doc: Y.Doc,
  transactionOrigin: any,
): void;
export function writeUpdate(
  encoder: encoding.Encoder,
  update: Uint8Array,
): void;
export function readUpdate(
  decoder: decoding.Decoder,
  doc: Y.Doc,
  transactionOrigin: any,
): void;
export function readSyncMessage(
  decoder: decoding.Decoder,
  encoder: encoding.Encoder,
  doc: Y.Doc,
  transactionOrigin: any,
): messageYjsSyncStep1 | messageYjsSyncStep2 | messageYjsUpdate;
