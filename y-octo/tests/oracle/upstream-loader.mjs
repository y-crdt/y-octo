// Resolve upstream test helpers and sync protocol to exactly one fetched Yjs
// implementation, rather than the npm peer installed for y-protocols.
import { pathToFileURL } from "node:url";
export function resolve(specifier, context, next) {
  if (specifier === "yjs")
    return next(
      pathToFileURL(`${process.env.YJS_FACTORY_SOURCE}/src/index.js`).href,
      context,
    );
  return next(specifier, context);
}
