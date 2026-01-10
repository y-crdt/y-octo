import type { Array } from "./array";
import type { Map } from "./map";

export type ArrayType =
  | string
  | number
  | any[]
  | Uint8Array
  | { [x: string]: any }
  | null;
export type ListItem =
  | Array
  | Map
  | Text
  | boolean
  | number
  | string
  | Record<string, any>
  | null;
