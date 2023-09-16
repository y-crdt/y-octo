use yrs::{updates::decoder::Decode, Update};

fn main() {
    if Update::decode_v1(&[255, 255, 255, 122]).is_ok() {};
}
