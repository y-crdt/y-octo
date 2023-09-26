use std::sync::atomic::{AtomicU8, Ordering};

#[rustfmt::skip]
#[allow(dead_code)]
pub mod item_flags {
    pub const ITEM_KEEP                 : u8 = 0b0000_0001;
    pub const ITEM_COUNTABLE            : u8 = 0b0000_0010;
    pub const ITEM_DELETED              : u8 = 0b0000_0100;
    pub const ITEM_MARKED               : u8 = 0b0000_1000;
    pub const ITEM_HAS_PARENT_SUB       : u8 = 0b0010_0000;
    pub const ITEM_HAS_RIGHT_ID         : u8 = 0b0100_0000;
    pub const ITEM_HAS_LEFT_ID          : u8 = 0b1000_0000;
    pub const ITEM_HAS_SIBLING          : u8 = 0b1100_0000;
}

#[derive(Debug)]
pub struct ItemFlag(AtomicU8);

impl Default for ItemFlag {
    fn default() -> Self {
        Self(AtomicU8::new(0))
    }
}

impl Clone for ItemFlag {
    fn clone(&self) -> Self {
        Self(AtomicU8::new(self.0.load(Ordering::Acquire)))
    }
}

impl From<u8> for ItemFlag {
    fn from(flags: u8) -> Self {
        Self(AtomicU8::new(flags))
    }
}

#[allow(dead_code)]
impl ItemFlag {
    #[inline(always)]
    pub fn set(&self, flag: u8) {
        self.0.fetch_or(flag, Ordering::SeqCst);
    }

    #[inline(always)]
    pub fn clear(&self, flag: u8) {
        self.0.fetch_and(flag, Ordering::SeqCst);
    }

    #[inline(always)]
    pub fn check(&self, flag: u8) -> bool {
        self.0.load(Ordering::Acquire) & flag == flag
    }

    #[inline(always)]
    pub fn not(&self, flag: u8) -> bool {
        self.0.load(Ordering::Acquire) & flag == 0
    }

    #[inline(always)]
    pub fn keep(&self) -> bool {
        self.check(item_flags::ITEM_KEEP)
    }

    #[inline(always)]
    pub fn set_keep(&self) {
        self.set(item_flags::ITEM_KEEP);
    }

    #[inline(always)]
    pub fn clear_keep(&self) {
        self.clear(item_flags::ITEM_KEEP);
    }

    #[inline(always)]
    pub fn countable(&self) -> bool {
        self.check(item_flags::ITEM_COUNTABLE)
    }

    #[inline(always)]
    pub fn set_countable(&self) {
        self.set(item_flags::ITEM_COUNTABLE);
    }

    #[inline(always)]
    pub fn clear_countable(&self) {
        self.clear(!item_flags::ITEM_COUNTABLE);
    }

    #[inline(always)]
    pub fn deleted(&self) -> bool {
        self.check(item_flags::ITEM_DELETED)
    }

    #[inline(always)]
    pub fn set_deleted(&self) {
        self.set(item_flags::ITEM_DELETED);
    }

    #[inline(always)]
    pub fn clear_deleted(&self) {
        self.clear(!item_flags::ITEM_DELETED);
    }
}
