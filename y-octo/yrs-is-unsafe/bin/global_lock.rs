use std::thread::spawn;

use yrs::{Doc, Transact};

fn main() {
    let doc = Doc::new();

    {
        let doc = doc.clone();
        spawn(move || {
            let _ = doc.transact_mut();
        });
    }
    {
        let doc = doc.clone();
        spawn(move || {
            let _ = doc.transact_mut();
        });
    }
    {
        let doc = doc.clone();
        spawn(move || {
            let _ = doc.transact_mut();
        });
    }
    {
        let doc = doc.clone();
        spawn(move || {
            let _ = doc.transact_mut();
        });
    }
}
