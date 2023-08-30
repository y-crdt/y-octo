use yrs::{updates::decoder::Decode, Update};

fn main() {
    if let Ok(_) = Update::decode_v1(&[255, 255, 255, 122]) {};
}
