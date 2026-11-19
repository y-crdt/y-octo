pub use std::sync::{Arc, Weak};
#[allow(unused)]
#[cfg(not(loom))]
pub(crate) use std::sync::{
    Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard,
    atomic::{AtomicBool, AtomicU8, AtomicU16, AtomicU32, Ordering},
};
#[cfg(all(test, not(loom)))]
pub(crate) use std::{
    sync::{MutexGuard, atomic::AtomicUsize},
    thread,
};

#[cfg(loom)]
pub(crate) use loom::{
    sync::{
        Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
        atomic::{AtomicBool, AtomicU8, AtomicU16, AtomicU32, AtomicUsize, Ordering},
    },
    thread,
};

#[macro_export(local_inner_macros)]
macro_rules! loom_model {
    ($test:block) => {
        #[cfg(loom)]
        loom::model(move || $test);

        #[cfg(not(loom))]
        $test
    };
    // the model body runs on a 4 KiB coroutine stack; tests with deeper call
    // chains move the body onto a spawned thread with an explicit stack size
    ($stack_size:expr, $test:block) => {
        #[cfg(loom)]
        loom::model(move || {
            loom::thread::Builder::new()
                .stack_size($stack_size)
                .spawn(move || $test)
                .unwrap()
                .join()
                .unwrap();
        });

        #[cfg(not(loom))]
        $test
    };
}
