use std::{
    alloc::{GlobalAlloc, Layout, System},
    fs,
    hint::black_box,
    path::Path,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::{Duration, Instant},
};

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use y_octo::{Any, Doc, ReadDoc, Update};

struct CountingAllocator;

static CURRENT: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            allocated(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        CURRENT.fetch_sub(layout.size(), Ordering::Relaxed);
        unsafe { System.dealloc(ptr, layout) };
    }

    unsafe fn realloc(&self, ptr: *mut u8, old: Layout, new_size: usize) -> *mut u8 {
        let value = unsafe { System.realloc(ptr, old, new_size) };
        if !value.is_null() {
            if new_size >= old.size() {
                allocated(new_size - old.size());
            } else {
                CURRENT.fetch_sub(old.size() - new_size, Ordering::Relaxed);
            }
        }
        value
    }
}

fn allocated(size: usize) {
    let current = CURRENT.fetch_add(size, Ordering::Relaxed) + size;
    PEAK.fetch_max(current, Ordering::Relaxed);
}

fn fixture_inputs() -> Vec<(&'static str, Arc<[u8]>)> {
    vec![
        (
            "basic",
            Arc::from(include_bytes!("../src/fixtures/basic.bin").as_slice()),
        ),
        (
            "database",
            Arc::from(include_bytes!("../src/fixtures/database.bin").as_slice()),
        ),
        (
            "large",
            Arc::from(include_bytes!("../src/fixtures/large.bin").as_slice()),
        ),
        (
            "with-subdoc",
            Arc::from(include_bytes!("../src/fixtures/with-subdoc.bin").as_slice()),
        ),
        (
            "left-right",
            Arc::from(include_bytes!("../src/fixtures/edge-case-left-right-same-node.bin").as_slice()),
        ),
    ]
}

fn generated_inputs() -> Vec<(&'static str, Arc<[u8]>)> {
    if std::env::var_os("YOCTO_LARGE_BENCH").is_none() {
        return Vec::new();
    }

    let mixed = Doc::new();
    mixed
        .get_or_create_text("mixed")
        .unwrap()
        .insert(0, "x".repeat(11 * 1024 * 1024))
        .unwrap();

    let map_updates = (0..10)
        .map(|segment| {
            let doc = Doc::new();
            let mut map = doc.get_or_create_map("map").unwrap();
            for offset in 0..10_000 {
                let index = segment * 10_000 + offset;
                map.insert(format!("key-{index:06}"), index as i64).unwrap();
            }
            Update::decode_v1(doc.encode_update_v1().unwrap()).unwrap()
        })
        .collect::<Vec<_>>();

    let array_updates = (0..100)
        .map(|segment| {
            let doc = Doc::new();
            let mut array = doc.get_or_create_array("array").unwrap();
            for offset in 0..10_000 {
                array.push((segment * 10_000 + offset) as i64).unwrap();
            }
            Update::decode_v1(doc.encode_update_v1().unwrap()).unwrap()
        })
        .collect::<Vec<_>>();

    let text_doc = Doc::new();
    text_doc
        .get_or_create_text("text")
        .unwrap()
        .insert(0, "format-heavy text ".repeat(100_000))
        .unwrap();

    let any_doc = Doc::new();
    let mut nested = Any::Null;
    for index in 0..64 {
        nested = Any::Array(vec![Any::from(index), nested]);
    }
    any_doc
        .get_or_create_map("any")
        .unwrap()
        .insert("nested".into(), nested)
        .unwrap();

    vec![
        ("mixed-10m", Arc::from(mixed.encode_update_v1().unwrap())),
        ("map-100k", Arc::from(Update::merge(map_updates).encode_v1().unwrap())),
        ("array-1m", Arc::from(Update::merge(array_updates).encode_v1().unwrap())),
        ("long-text", Arc::from(text_doc.encode_update_v1().unwrap())),
        ("deep-any", Arc::from(any_doc.encode_update_v1().unwrap())),
    ]
}

fn corpus_inputs() -> Vec<(String, Arc<[u8]>)> {
    let Some(directory) = std::env::var_os("YOCTO_READONLY_CORPUS") else {
        return Vec::new();
    };
    let mut inputs = Vec::new();
    let Ok(entries) = fs::read_dir(Path::new(&directory)) else {
        return inputs;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().is_some_and(|extension| extension == "bin")
            && let Ok(bytes) = fs::read(&path)
        {
            inputs.push((entry.file_name().to_string_lossy().into_owned(), Arc::from(bytes)));
        }
    }
    inputs.sort_by(|left, right| left.0.cmp(&right.0));
    inputs
}

fn memory_report(name: &str, input: &Arc<[u8]>) {
    CURRENT.store(0, Ordering::Relaxed);
    PEAK.store(0, Ordering::Relaxed);
    let start = Instant::now();
    let mutable = Doc::try_from_binary_v1(input.as_ref());
    let elapsed = start.elapsed();
    let mutable_peak = PEAK.load(Ordering::Relaxed);
    let mutable_retained = CURRENT.load(Ordering::Relaxed);
    let mutable_result = mutable
        .as_ref()
        .map(|_| "ok".to_string())
        .unwrap_or_else(|error| format!("error:{error}"));
    drop(mutable);

    CURRENT.store(0, Ordering::Relaxed);
    PEAK.store(0, Ordering::Relaxed);
    let start = Instant::now();
    let readonly = ReadDoc::from_full_update_v1(input.clone());
    let read_elapsed = start.elapsed();
    let read_peak = PEAK.load(Ordering::Relaxed);
    let read_retained = CURRENT.load(Ordering::Relaxed);
    let read_result = readonly
        .as_ref()
        .map(|_| "ok".to_string())
        .unwrap_or_else(|error| format!("error:{error}"));
    drop(readonly);

    eprintln!(
        "readonly-report name={name} bytes={} mutable_us={} mutable_peak={} mutable_retained={} \
         mutable_result={mutable_result:?} read_us={} read_peak={} read_retained={} read_result={read_result:?}",
        input.len(),
        elapsed.as_micros(),
        mutable_peak,
        mutable_retained,
        read_elapsed.as_micros(),
        read_peak,
        read_retained,
    );
}

fn readonly(c: &mut Criterion) {
    let mut inputs = fixture_inputs();
    inputs.extend(generated_inputs());
    if std::env::var_os("YOCTO_READONLY_REPORT").is_some() {
        for (name, input) in &inputs {
            memory_report(name, input);
        }
        for (name, input) in corpus_inputs() {
            memory_report(&name, &input);
        }
    }

    let mut decode = c.benchmark_group("readonly-decode");
    decode.sample_size(10).measurement_time(Duration::from_secs(1));
    for (name, input) in &inputs {
        decode.throughput(Throughput::Bytes(input.len() as u64));
        decode.bench_with_input(BenchmarkId::new("mutable", name), input, |b, input| {
            b.iter(|| Doc::try_from_binary_v1(black_box(input.as_ref())).unwrap())
        });
        decode.bench_with_input(BenchmarkId::new("readonly", name), input, |b, input| {
            b.iter(|| ReadDoc::from_full_update_v1(black_box(input.clone())).unwrap())
        });
    }
    decode.finish();

    if let Some((_, map_input)) = inputs.iter().find(|(name, _)| *name == "map-100k") {
        let doc = ReadDoc::from_full_update_v1(map_input.clone()).unwrap();
        let map = doc.map("map").unwrap();
        c.bench_function("readonly-query/map-hit-100k", |b| {
            b.iter(|| map.get(black_box("key-099999")))
        });
        c.bench_function("readonly-query/map-miss-100k", |b| {
            b.iter(|| map.get(black_box("missing")))
        });
    }
    if let Some((_, array_input)) = inputs.iter().find(|(name, _)| *name == "array-1m") {
        let doc = ReadDoc::from_full_update_v1(array_input.clone()).unwrap();
        let array = doc.array("array").unwrap();
        c.bench_function("readonly-query/array-iteration-1m", |b| {
            b.iter(|| {
                array.iter().for_each(|value| {
                    black_box(value);
                })
            })
        });
        c.bench_function("readonly-query/array-random-get-1m", |b| {
            b.iter(|| array.get(black_box(999_999)))
        });
    }
    if let Some((_, text_input)) = inputs.iter().find(|(name, _)| *name == "long-text") {
        let doc = ReadDoc::from_full_update_v1(text_input.clone()).unwrap();
        let text = doc.text("text").unwrap();
        c.bench_function("readonly-query/text-runs", |b| {
            b.iter(|| {
                text.runs().for_each(|run| {
                    black_box(run);
                })
            })
        });
        c.bench_function("readonly-query/text-to-delta", |b| b.iter(|| text.to_delta()));
    }
}

criterion_group!(benches, readonly);
criterion_main!(benches);
