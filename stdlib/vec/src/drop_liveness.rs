//! Verification regressions: the buffer's element lifetime ends before its glue runs.

use crate::{RawVec, RawVecInner};
use std::alloc::Global;
use std::marker::PhantomData;
use std::mem::Alignment;

#[rr::exists("l")]
#[rr::returns("(l, 0%nat, [])")]
fn bind_element_lifetime<'a>(value: &'a u8) -> RawVec<&'a u8> {
    RawVec {
        inner: RawVecInner::new_in(Global, Alignment::of::<*const u8>()),
        _marker: PhantomData,
    }
}

#[rr::returns("()")]
fn drop_after_element_lifetime() {
    let buffer;
    {
        let value = 42_u8;
        buffer = bind_element_lifetime(&value);
    }
    // The helper's return type fixes the element lifetime, even without storing
    // a reference. Ordinary Drop rejects this just as for a full buffer.
}
