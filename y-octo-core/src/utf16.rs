#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct Utf16SplitOffset {
    pub start: usize,
    pub end: usize,
    pub split_surrogate: bool,
}

fn is_cont(b: u8) -> bool {
    b >= 0x80 && b <= 0xbf
}

fn utf8_check_3(b0: u8, b1: u8, b2: u8) -> bool {
    if !is_cont(b2) {
        return false;
    }
    if b0 == 0xe0 {
        return b1 >= 0xa0 && b1 <= 0xbf;
    }
    if b0 == 0xed {
        return b1 >= 0x80 && b1 <= 0x9f;
    }
    is_cont(b1)
}

fn utf8_check_4(b0: u8, b1: u8, b2: u8, b3: u8) -> bool {
    if !is_cont(b2) || !is_cont(b3) {
        return false;
    }
    if b0 == 0xf0 {
        return b1 >= 0x90 && b1 <= 0xbf;
    }
    if b0 == 0xf4 {
        return b1 >= 0x80 && b1 <= 0x8f;
    }
    is_cont(b1)
}

fn utf8_char_step(bytes: &[u8], i: usize) -> Option<usize> {
    let len = bytes.len();
    let b0 = bytes[i];
    if b0 < 0x80 {
        return Some(i + 1);
    }
    if b0 >= 0xc2 && b0 <= 0xdf {
        if len - i < 2 || !is_cont(bytes[i + 1]) {
            return None;
        }
        return Some(i + 2);
    }
    if b0 >= 0xe0 && b0 <= 0xef {
        if len - i < 3 {
            return None;
        }
        if utf8_check_3(b0, bytes[i + 1], bytes[i + 2]) {
            return Some(i + 3);
        }
        return None;
    }
    if b0 >= 0xf0 && b0 <= 0xf4 {
        if len - i < 4 {
            return None;
        }
        if utf8_check_4(b0, bytes[i + 1], bytes[i + 2], bytes[i + 3]) {
            return Some(i + 4);
        }
        return None;
    }
    None
}

/// Pure RFC 3629 UTF-8 byte validator with zero external dependencies.
pub fn is_valid_utf8(bytes: &[u8]) -> bool {
    let mut i = 0usize;
    let len = bytes.len();
    while i < len {
        match utf8_char_step(bytes, i) {
            Some(next) => i = next,
            None => return false,
        }
    }
    true
}

/// Computes UTF-16 code unit length of valid UTF-8 `bytes` (never panics or
/// overflows even on arbitrary byte slices).
pub fn utf16_len(bytes: &[u8]) -> usize {
    let mut i = 0usize;
    let mut count = 0usize;
    let len = bytes.len();
    while i < len {
        let b = bytes[i];
        let step = if b < 128 {
            1usize
        } else if b < 224 {
            2usize
        } else if b < 240 {
            3usize
        } else {
            4usize
        };
        if len - i < step {
            break;
        }
        let units = if step == 4 { 2usize } else { 1usize };
        i += step;
        count += units;
    }
    count
}

/// Computes the byte boundary in valid UTF-8 `bytes` corresponding to UTF-16
/// `target` clock units, reporting whether `target` lands inside a surrogate
/// pair.
pub fn utf16_split_byte_offset(bytes: &[u8], target: u64) -> Utf16SplitOffset {
    let mut i = 0usize;
    let mut clock = 0u64;
    let len = bytes.len();
    while i < len {
        let b = bytes[i];
        let step = if b < 128 {
            1usize
        } else if b < 224 {
            2usize
        } else if b < 240 {
            3usize
        } else {
            4usize
        };
        if len - i < step {
            return Utf16SplitOffset {
                start: len,
                end: len,
                split_surrogate: false,
            };
        }
        let units = if step == 4 { 2u64 } else { 1u64 };
        if clock > u64::MAX - units {
            return Utf16SplitOffset {
                start: len,
                end: len,
                split_surrogate: false,
            };
        }
        let next_clock = clock + units;
        if target < next_clock {
            return Utf16SplitOffset {
                start: i,
                end: i + step,
                split_surrogate: target > clock,
            };
        }
        clock = next_clock;
        i += step;
    }
    Utf16SplitOffset {
        start: len,
        end: len,
        split_surrogate: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utf16_cases() {
        assert!(is_valid_utf8("a😀中文".as_bytes()));
        assert!(!is_valid_utf8(&[0xff, 0x00]));
        assert!(!is_valid_utf8(&[0xed, 0xa0, 0x80]));

        assert_eq!(utf16_len(b""), 0);
        assert_eq!(utf16_len("a😀b".as_bytes()), 4);
        assert_eq!(
            utf16_split_byte_offset("a😀b".as_bytes(), 0),
            Utf16SplitOffset {
                start: 0,
                end: 1,
                split_surrogate: false,
            }
        );
        assert_eq!(
            utf16_split_byte_offset("a😀b".as_bytes(), 1),
            Utf16SplitOffset {
                start: 1,
                end: 5,
                split_surrogate: false,
            }
        );
        assert_eq!(
            utf16_split_byte_offset("a😀b".as_bytes(), 2),
            Utf16SplitOffset {
                start: 1,
                end: 5,
                split_surrogate: true,
            }
        );
        assert_eq!(
            utf16_split_byte_offset("a😀b".as_bytes(), 3),
            Utf16SplitOffset {
                start: 5,
                end: 6,
                split_surrogate: false,
            }
        );
        assert_eq!(
            utf16_split_byte_offset("a😀b".as_bytes(), 99),
            Utf16SplitOffset {
                start: 6,
                end: 6,
                split_surrogate: false,
            }
        );
    }
}
