# Why we're not using [yrs](https://crates.io/crates/yrs)

## Multi-threading safety

One of the biggest reason why we are writing our own yjs compatible Rust implementation is [yrs](https://crates.io/crates/yrs) is not safe for multi-threading.

You can run the following code to see the problem:

```bash
cargo run --bin yrs-is-unsafe
```

The source codes is under the [yrs-is-unsafe](y-octo/yrs-is-unsafe/src/main.rs):

<details>
<summary>main.rs</summary>

```rust
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
```

</details>

We are facing this problem in our Rust server, and the iOS/Android clients which are running with the multi-threading runtime.

Adding a global lock is not a good solution in this case. First the performance will be bad, and deadlocks will come after that. In general the deadlocks in application level are more difficult to debug than in the library level.
Second, we assume the Rust compiler can guarantee the multi-threading safety, and with [yrs](https://crates.io/crates/yrs) we must to guarantee the safety by ourselves, and it often leads to bugs.

## Memory efficiency

In the previous versions of [Mysc](https://www.mysc.app/) mobile apps, there are always oom issues happened.
You can run the following command to see the problem:

```bash
cargo build --release --bin yrs-mem
/usr/bin/time -l ./target/release/yrs-mem
```

[The source codes](../yrs-is-unsafe/bin/mem_usage.rs):

<details>
<summary>mem_usage.rs</summary>

```rust
use yrs::{updates::decoder::Decode, Update};

fn main() {
    if let Ok(_) = Update::decode_v1(&[255, 255, 255, 122]) {};
}
```

</details>

On my MacBook pro, the results is like that:

```text
.05 real         0.01 user         0.04 sys
           538050560  maximum resident set size
                   0  average shared memory size
                   0  average unshared data size
                   0  average unshared stack size
               32959  page reclaims
                   1  page faults
                   0  swaps
                   0  block input operations
                   0  block output operations
                   0  messages sent
                   0  messages received
                   0  signals received
                   0  voluntary context switches
                   5  involuntary context switches
           298179580  instructions retired
           166031219  cycles elapsed
           538003008  peak memory footprint
```

There is `538050560` bytes memory used, which is about **538MB**. It's too bad for mobile apps or the similar low memory devices.

## Panic everywhere

Unlike most of the Rust libraries, [yrs](https://crates.io/crates/yrs) [panics everywhere](https://github.com/search?q=repo%3Ay-crdt%2Fy-crdt+panic+language%3ARust&type=code&l=Rust), rather than returning the `Result` type. It causes the application crash easily without the guarantee of the compiler's safety checks. We must add `catch_unwind` everywhere in our application to avoid the crash, that is bad.
