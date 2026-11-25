//! What a document that has no room for a struct says.

use crate::JwstCodecError;

/// The item arena holds as many items as an index names.
pub(crate) const TOO_MANY_ITEMS: &str = "the document holds too many items";
/// The type arena holds as many types as an index names.
pub(crate) const TOO_MANY_TYPES: &str = "the document holds too many types";
/// A timeline holds as many blocks as it takes.
pub(crate) const TOO_MANY_STRUCTS: &str = "the document holds too many structs";
/// The list of the candidates of a conflict scan is full.
pub(crate) const TOO_MANY_CANDIDATES: &str = "the conflict scan holds too many candidates";

/// Whether the store refused a struct or a deletion for room: the item
/// arena, the type arena, a timeline or the candidates of a conflict scan
/// took no more. It takes the same struct once there is room; every other
/// refusal is of the struct itself and is the same whenever it is tried.
pub(crate) fn refused_for_room(error: &JwstCodecError) -> bool {
    matches!(
        error,
        JwstCodecError::IncompleteDocument(message)
            if [TOO_MANY_ITEMS, TOO_MANY_TYPES, TOO_MANY_STRUCTS, TOO_MANY_CANDIDATES].contains(&message.as_str())
    )
}
