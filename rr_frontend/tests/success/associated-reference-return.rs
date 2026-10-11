//@check-pass
#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![allow(dead_code)]
#![register_tool(rr)]
#![rr::package("associated_reference_return")]

// Explicit method specifications translate the expected trait signature, whose
// associated return types must normalize without erasing the impl lifetime.
trait SharedItem<'a> {
    type Item;
    #[rr::requires("True")]
    fn next(&mut self, value: &'a i32) -> (Self::Item,);
}

impl<'a> SharedItem<'a> for () {
    type Item = &'a i32;

    #[rr::verify]
    #[rr::requires("True")]
    fn next(&mut self, value: &'a i32) -> (&'a i32,) {
        (value,)
    }
}

trait MutableItem<'a> {
    type Item;
    #[rr::requires("True")]
    fn next(&mut self, value: &'a mut i32) -> (Self::Item,);
}

impl<'a> MutableItem<'a> for () {
    type Item = &'a mut i32;

    #[rr::verify]
    #[rr::requires("True")]
    fn next(&mut self, value: &'a mut i32) -> (&'a mut i32,) {
        (value,)
    }
}

fn main() {}
