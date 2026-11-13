mod utils;

use std::time::Duration;

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use path_ext::PathExt;
use utils::Files;
use y_octo::{Doc, ReadDoc, StateVector, Update};

fn update(c: &mut Criterion) {
    let files = Files::load();

    let mut group = c.benchmark_group("update");
    group.measurement_time(Duration::from_secs(15));

    for file in &files.files {
        group.throughput(Throughput::Bytes(file.content.len() as u64));
        group.bench_with_input(
            BenchmarkId::new("parse with jwst", file.path.name_str()),
            &file.content,
            |b, content| {
                b.iter(|| {
                    use y_octo::*;
                    let mut decoder = RawDecoder::new(content);
                    Update::read(&mut decoder).unwrap()
                });
            },
        );
    }

    group.finish();

    let mut merge = c.benchmark_group("update-merge-sources");
    for count in [512, 2048, 8192] {
        let doc = Doc::with_client(1);
        let mut text = doc.get_or_create_text("text").unwrap();
        let updates = (0..count)
            .map(|clock| {
                text.insert(clock, "x").unwrap();
                let bytes = doc.encode_state_as_update_v1(&StateVector::from([(1, clock)])).unwrap();
                Update::decode_v1(bytes).unwrap()
            })
            .collect::<Vec<_>>();
        let bytes = Update::merge(updates.clone()).encode_v1().unwrap();
        let merged = ReadDoc::from_full_update_v1(bytes).unwrap();
        assert_eq!(merged.text("text").unwrap().len(), count);
        merge.throughput(Throughput::Elements(count));
        merge.bench_with_input(BenchmarkId::from_parameter(count), &updates, |b, updates| {
            b.iter_batched(|| updates.clone(), Update::merge, BatchSize::PerIteration);
        });
    }
    merge.finish();
}

criterion_group!(benches, update);
criterion_main!(benches);
