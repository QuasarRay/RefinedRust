#![allow(dead_code)]

fn choose() -> bool {
    true
}

#[mapper::run]
#[mapper::points]
pub fn conditional_field_drop<T>(x: (T, Box<i32>)) {
    if choose() {
        std::mem::drop(x.0)
    } else {
        std::mem::drop(x.1)
    }
}
