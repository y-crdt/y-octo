//! create → edit → commit → anchor → undo/redo → encode inside wasm, with the
//! identity and the time passed by the host. Every step that disagrees with
//! the expected result returns a nonzero step number; a panic traps.

use std::sync::{
    Arc,
    atomic::{AtomicU32, Ordering},
};

use y_octo::{Any, DocOptions, TextAttributes, TextDeltaOp, TextInsert, UndoManager, UndoOptions, UndoStack};

static mut OUTPUT: Vec<u8> = Vec::new();

/// The update `run` encoded.
#[unsafe(no_mangle)]
pub extern "C" fn output_ptr() -> *const u8 {
    // SAFETY: the module is single threaded; the host reads after `run`.
    unsafe { (*std::ptr::addr_of!(OUTPUT)).as_ptr() }
}

#[unsafe(no_mangle)]
pub extern "C" fn output_len() -> usize {
    // SAFETY: as above.
    unsafe { (*std::ptr::addr_of!(OUTPUT)).len() }
}

/// Returns 0 when every step matched, the number of the first step that did
/// not otherwise.
#[unsafe(no_mangle)]
pub extern "C" fn run(client: u64, now: u64) -> u32 {
    match steps(client, now) {
        Ok(update) => {
            // SAFETY: as above.
            unsafe { *std::ptr::addr_of_mut!(OUTPUT) = update };
            0
        }
        Err(step) => step,
    }
}

fn steps(client: u64, now: u64) -> Result<Vec<u8>, u32> {
    let check = |ok: bool, step: u32| if ok { Ok(()) } else { Err(step) };

    // create, with the host's identity
    let doc = DocOptions::from_identity(client, "wasm-smoke".into()).build();
    check(doc.client() == client, 1)?;
    let text = doc.get_or_create_text("text").map_err(|_| 2u32)?;
    let commits = Arc::new(AtomicU32::new(0));
    let _subscription = {
        let commits = commits.clone();
        doc.subscribe(move |_| {
            commits.fetch_add(1, Ordering::SeqCst);
        })
    };
    let undo = UndoManager::<()>::new(&doc, [(&text).into()], UndoOptions::default()).map_err(|_| 3u32)?;
    undo.advance_time(now);

    // edit and commit: one transaction, one event
    doc.transact_mut(None, |tx| {
        let mut text = tx.text(&text)?;
        text.insert(0, "hello world")?;
        let bold: TextAttributes = [("bold".to_string(), Any::True)].into_iter().collect();
        text.apply_delta(&[TextDeltaOp::Retain {
            retain: 5,
            format: Some(bold),
        }])
    })
    .map_err(|_| 4u32)?;
    check(commits.load(Ordering::SeqCst) == 1, 5)?;
    check(
        text.to_delta().first()
            == Some(&TextDeltaOp::Insert {
                insert: TextInsert::Text("hello".into()),
                format: Some([("bold".to_string(), Any::True)].into_iter().collect()),
            }),
        6,
    )?;

    // anchor before "world"
    let anchor = text.relative_position(6, 0).map_err(|_| 7u32)?;
    let index = |doc: &y_octo::Doc| {
        doc.resolve_relative_position(&anchor, false)
            .map(|position| position.index)
    };

    // a later edit, outside the capture window of the host's clock
    undo.advance_time(now + 10_000);
    let mut editing = text.clone();
    editing.remove(0, 6).map_err(|_| 8u32)?;
    check(text.to_string() == "world" && index(&doc) == Some(0), 9)?;

    // undo/redo
    check(undo.undo().map_err(|_| 10u32)?.is_some(), 10)?;
    check(text.to_string() == "hello world" && index(&doc) == Some(6), 11)?;
    check(undo.peek(UndoStack::Redo).is_some(), 12)?;
    check(undo.redo().map_err(|_| 13u32)?.is_some(), 13)?;
    check(text.to_string() == "world", 14)?;
    check(undo.undo().map_err(|_| 15u32)?.is_some(), 15)?;
    check(text.to_string() == "hello world", 16)?;
    check(commits.load(Ordering::SeqCst) == 5, 17)?;

    // encode
    doc.encode_update_v1().map_err(|_| 18u32)
}
