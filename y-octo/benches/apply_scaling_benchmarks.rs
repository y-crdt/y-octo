//! Cost of applying one small remote update to documents of different sizes.
//! With incremental GC and merge it should not grow with the document.

use std::time::{Duration, Instant};

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use y_octo::{Doc, StateVector};

const UPDATES_PER_ROUND: u64 = 32;

/// The receiver starts with separate text items, half of them deleted. The
/// sender has seen the same structs but not the deletions, so its deltas
/// include each new insertion without the receiver's historical delete set.
fn fixture(items: u64) -> (Vec<u8>, Vec<Vec<u8>>) {
    let source = Doc::with_client(1);
    let mut text = source.get_or_create_text("text").unwrap();
    for _ in 0..items {
        text.insert(0, "a").unwrap();
    }

    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(source.encode_update_v1().unwrap())
        .unwrap();
    let mut peer_text = peer.get_or_create_text("text").unwrap();
    let mut known = peer.get_state_vector();
    let updates = (0..UPDATES_PER_ROUND)
        .map(|_| {
            peer_text.insert(0, "b").unwrap();
            let update = peer.encode_state_as_update_v1(&known).unwrap();
            known = peer.get_state_vector();
            update
        })
        .collect();

    for i in 1..=items / 2 {
        text.remove(i, 1).unwrap();
    }
    (source.encode_update_v1().unwrap(), updates)
}

fn apply_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("apply/remote prepends");
    group.throughput(Throughput::Elements(UPDATES_PER_ROUND));
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(3));

    for items in [20_000u64, 200_000] {
        let (base, updates) = fixture(items);
        let expected = StateVector::from([(1, items), (2, UPDATES_PER_ROUND)]);

        group.bench_function(BenchmarkId::from_parameter(items), |b| {
            b.iter_custom(|rounds| {
                let mut elapsed = Duration::ZERO;
                for _ in 0..rounds {
                    let mut doc = Doc::with_client(3);
                    doc.apply_update_from_binary_v1(&base).unwrap();
                    #[cfg(feature = "debug")]
                    assert_eq!(doc.store_status().nodes as u64, items);

                    // A fresh receiver per round caps growth at 32 structs.
                    let start = Instant::now();
                    for update in &updates {
                        doc.apply_update_from_binary_v1(update).unwrap();
                    }
                    elapsed += start.elapsed();

                    assert_eq!(doc.get_state_vector(), expected);
                    assert!(!doc.has_pending_updates());
                    #[cfg(feature = "debug")]
                    assert_eq!(doc.store_status().nodes as u64, items + UPDATES_PER_ROUND);
                }
                elapsed
            });
        });
    }

    group.finish();
}

criterion_group!(benches, apply_scaling);
criterion_main!(benches);
