use std::thread::spawn;

use yrs::Doc;

fn main() {
    let doc = Doc::new();

    let t1 = {
        let doc = doc.clone();
        spawn(move || {
            let _ = doc.get_or_insert_map("text");
        })
    };

    let t2 = {
        let doc = doc.clone();
        spawn(move || {
            let _ = doc.get_or_insert_map("text");
        })
    };

    t1.join().unwrap();
    t2.join().unwrap();
}
