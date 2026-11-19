#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use y_octo::*;

#[derive(Arbitrary, Debug)]
enum TextOp {
    Insert(u16, String),
    Remove(u16, u8),
}

// Map arbitrary chars into printable ASCII so byte length, char count and
// content length stay identical and the length invariant below holds.
fn to_ascii(input: &str) -> String {
    input.chars().map(|c| ((c as u8) % 94 + 32) as char).collect()
}

fuzz_target!(|ops: Vec<TextOp>| {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("test").unwrap();
    text.insert(0, "This is a string with length 32.").unwrap();

    let mut len = 32u64;
    for op in ops {
        match op {
            TextOp::Insert(pos, content) => {
                let content = to_ascii(&content);
                if content.is_empty() {
                    continue;
                }
                // insert_at rejects index > len, so stay within [0, len]
                let pos = pos as u64 % (len + 1);
                text.insert(pos, &content).unwrap();
                len += content.len() as u64;
            }
            TextOp::Remove(pos, remove_len) => {
                if len == 0 {
                    continue;
                }
                // remove_at rejects pos >= len; clamp the range to the tail
                let pos = pos as u64 % len;
                let remove_len = 1 + remove_len as u64 % (len - pos);
                text.remove(pos, remove_len).unwrap();
                len -= remove_len;
            }
        }
    }

    assert_eq!(text.to_string().len(), len as usize);
    assert_eq!(text.len(), len);
});
