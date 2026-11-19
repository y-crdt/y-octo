use std::{
    alloc::{GlobalAlloc, Layout, System},
    env, fs,
    hint::black_box,
    sync::atomic::{AtomicUsize, Ordering},
    time::Instant,
};

use serde_json::json;
use y_octo::{DocOptions, ReadDoc, Update as OctoUpdate, memory_layout, profiling_counters, reset_profiling_counters};
use yrs::{
    Doc as YrsDoc, Options as YrsOptions, ReadTxn, StateVector as YrsStateVector, Transact, Update as YrsUpdate,
    updates::decoder::Decode,
};

struct CountingAllocator;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);

fn add_live(size: usize) {
    let live = LIVE.fetch_add(size, Ordering::Relaxed) + size;
    ALLOCS.fetch_add(1, Ordering::Relaxed);
    let mut peak = PEAK.load(Ordering::Relaxed);
    while live > peak {
        match PEAK.compare_exchange_weak(peak, live, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => break,
            Err(current) => peak = current,
        }
    }
}

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            add_live(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) };
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            if new_size >= layout.size() {
                add_live(new_size - layout.size());
            } else {
                LIVE.fetch_sub(layout.size() - new_size, Ordering::Relaxed);
            }
        }
        new_ptr
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn snapshot(engine: &str, file: &str, stage: &str, started: Instant, extra: serde_json::Value) {
    let live = LIVE.load(Ordering::Relaxed);
    let peak = PEAK.load(Ordering::Relaxed);
    let allocations = ALLOCS.load(Ordering::Relaxed);
    println!(
        "{}",
        json!({
            "engine": engine,
            "file": file,
            "stage": stage,
            "elapsed_ms": started.elapsed().as_secs_f64() * 1000.0,
            "live_requested_bytes": live,
            "peak_requested_bytes": peak,
            "allocation_calls": allocations,
            "extra": extra,
        })
    );
}

fn profile_octo(file: &str, output: Option<&str>) {
    let started = Instant::now();
    let data = fs::read(file).unwrap();
    snapshot(
        "y-octo",
        file,
        "read",
        started,
        json!({"input_bytes": data.len(), "layout": memory_layout()}),
    );

    let stage = Instant::now();
    reset_profiling_counters();
    let update = OctoUpdate::decode_v1(&data).unwrap();
    snapshot(
        "y-octo",
        file,
        "decode",
        stage,
        json!({"clock_len": profiling_counters()}),
    );

    let mut doc = DocOptions::new().auto_gc(false).build();
    let stage = Instant::now();
    reset_profiling_counters();
    doc.apply_update(update).unwrap();
    snapshot(
        "y-octo",
        file,
        "apply_no_gc",
        stage,
        json!({"store": doc.store_status(), "clock_len": profiling_counters()}),
    );

    let stage = Instant::now();
    doc.clear_change_tracking();
    snapshot(
        "y-octo",
        file,
        "clear_change_tracking",
        stage,
        json!(doc.store_status()),
    );

    let stage = Instant::now();
    doc.gc().unwrap();
    snapshot("y-octo", file, "gc", stage, json!(doc.store_status()));

    let stage = Instant::now();
    let encoded = doc.encode_update_v1().unwrap();
    snapshot("y-octo", file, "encode", stage, json!({"output_bytes": encoded.len()}));
    if let Some(output) = output {
        fs::write(output, &encoded).unwrap();
    }
    black_box((&doc, &encoded));
}

fn profile_readonly(file: &str) {
    let started = Instant::now();
    let data = fs::read(file).unwrap();
    snapshot(
        "y-octo-readonly",
        file,
        "read",
        started,
        json!({"input_bytes": data.len()}),
    );

    let stage = Instant::now();
    let doc = ReadDoc::from_full_update_v1(data).unwrap();
    let roots = doc.root_names().count();
    snapshot("y-octo-readonly", file, "decode", stage, json!({"roots": roots}));
    black_box(&doc);
}

fn profile_yrs(file: &str, output: Option<&str>) {
    let started = Instant::now();
    let data = fs::read(file).unwrap();
    snapshot(
        "yrs",
        file,
        "read",
        started,
        json!({
            "input_bytes": data.len(),
            "layout": {
                "id": std::mem::size_of::<yrs::ID>(),
                "option_id": std::mem::size_of::<Option<yrs::ID>>(),
                "item": std::mem::size_of::<yrs::block::Item>(),
                "item_content": std::mem::size_of::<yrs::block::ItemContent>(),
                "item_ptr": std::mem::size_of::<yrs::block::ItemPtr>(),
                "option_item_ptr": std::mem::size_of::<Option<yrs::block::ItemPtr>>(),
                "block_range": std::mem::size_of::<yrs::block::BlockRange>(),
            }
        }),
    );

    let stage = Instant::now();
    let update = YrsUpdate::decode_v1(&data).unwrap();
    snapshot("yrs", file, "decode", stage, json!({}));

    let doc = YrsDoc::with_options(YrsOptions::default());
    let stage = Instant::now();
    {
        let mut txn = doc.transact_mut();
        txn.apply_update(update).unwrap();
    }
    snapshot("yrs", file, "apply_default_gc", stage, json!({}));

    let stage = Instant::now();
    let encoded = doc.transact().encode_state_as_update_v1(&YrsStateVector::default());
    snapshot("yrs", file, "encode", stage, json!({"output_bytes": encoded.len()}));
    if let Some(output) = output {
        fs::write(output, &encoded).unwrap();
    }
    black_box((&doc, &encoded));
}

fn profile_yrs_latest(file: &str, output: Option<&str>) {
    use yrs_latest::{ReadTxn, Transact, updates::decoder::Decode};

    let started = Instant::now();
    let data = fs::read(file).unwrap();
    snapshot(
        "yrs-0.27.3",
        file,
        "read",
        started,
        json!({
            "input_bytes": data.len(),
            "layout": {
                "id": std::mem::size_of::<yrs_latest::ID>(),
                "item": std::mem::size_of::<yrs_latest::block::Item>(),
                "item_content": std::mem::size_of::<yrs_latest::block::ItemContent>(),
                "item_ptr": std::mem::size_of::<yrs_latest::block::ItemPtr>(),
            }
        }),
    );

    let stage = Instant::now();
    let update = yrs_latest::Update::decode_v1(&data).unwrap();
    snapshot("yrs-0.27.3", file, "decode", stage, json!({}));

    let doc = yrs_latest::Doc::with_options(yrs_latest::Options::default());
    let stage = Instant::now();
    {
        let mut txn = doc.transact_mut();
        txn.apply_update(update).unwrap();
    }
    snapshot("yrs-0.27.3", file, "apply_default_gc", stage, json!({}));

    let stage = Instant::now();
    let encoded = doc
        .transact()
        .encode_state_as_update_v1(&yrs_latest::StateVector::default());
    snapshot(
        "yrs-0.27.3",
        file,
        "encode",
        stage,
        json!({"output_bytes": encoded.len()}),
    );
    if let Some(output) = output {
        fs::write(output, &encoded).unwrap();
    }
    black_box((&doc, &encoded));
}

fn main() {
    let mut args = env::args();
    let _program = args.next();
    let engine = args
        .next()
        .expect("usage: profile_ydoc <y-octo|read-only|yrs|yrs-latest> <file>");
    let file = args
        .next()
        .expect("usage: profile_ydoc <y-octo|read-only|yrs|yrs-latest> <file>");
    let output = args.next();
    match engine.as_str() {
        "y-octo" => profile_octo(&file, output.as_deref()),
        "read-only" => profile_readonly(&file),
        "yrs" => profile_yrs(&file, output.as_deref()),
        "yrs-latest" => profile_yrs_latest(&file, output.as_deref()),
        _ => panic!("unknown engine: {engine}"),
    }
}
