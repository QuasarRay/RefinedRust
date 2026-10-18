//! Thin-pointer boundary for the allocator API.

#![rr::import("rrstd.vec.theories", "allocation")]

use std::alloc::{AllocError, Allocator, Layout};
use std::ptr::NonNull;

// TODO(verification): These wrappers are trusted specifications (only_spec).
// Erase NonNull<[u8]> metadata inside this boundary because slice support is
// deferred. RawVec only uses the requested extent, not the returned slice length.
// The abstract FreeablePerm tracks a fitting requested layout, including when
// the allocator returns excess capacity. No exact-size allocation is assumed.
// The pinned nightly's Allocator safety contract forbids unwinding from these
// operations (core/src/alloc/mod.rs, Safety). This is part of the trusted boundary.
#[rr::only_spec]
#[rr::may_unwind_if("False")]
#[rr::exists("res" : "(loc + unit)%type", "v" : "val")]
#[rr::returns("res")]
#[rr::ensures(#iris "if_iOk res (λ l, raw_allocation π ({A::FreeablePerm} alloc) l layout v)")]
pub(super) fn allocate_raw<A: Allocator>(
    alloc: &A,
    layout: Layout,
) -> Result<*mut u8, AllocError> {
    alloc.allocate(layout).map(|ptr| ptr.cast::<u8>().as_ptr())
}

#[rr::only_spec]
#[rr::may_unwind_if("False")]
#[rr::exists("res" : "(loc + unit)%type")]
#[rr::returns("res")]
#[rr::ensures(#iris "if_iOk res (λ l, raw_allocation π ({A::FreeablePerm} alloc) l layout (replicate layout.(layout_sz) (MByte byte0)))")]
pub(super) fn allocate_zeroed_raw<A: Allocator>(
    alloc: &A,
    layout: Layout,
) -> Result<*mut u8, AllocError> {
    alloc.allocate_zeroed(layout).map(|ptr| ptr.cast::<u8>().as_ptr())
}

#[rr::only_spec]
#[rr::may_unwind_if("False")]
#[rr::params("v" : "val")]
#[rr::requires("Hgrow_size" : "(old_layout.(layout_sz) ≤ new_layout.(layout_sz))%nat")]
#[rr::requires(#iris "raw_allocation π ({A::FreeablePerm} alloc) ptr old_layout v")]
#[rr::exists("res" : "(loc + unit)%type", "suffix" : "val")]
#[rr::returns("res")]
#[rr::ensures(#iris "if_iOk res (λ l, raw_allocation π ({A::FreeablePerm} alloc) l new_layout (v ++ suffix))")]
#[rr::ensures(#iris "if_iErr res (λ _, raw_allocation π ({A::FreeablePerm} alloc) ptr old_layout v)")]
pub(super) unsafe fn grow_raw<A: Allocator>(
    alloc: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<*mut u8, AllocError> {
    // SAFETY: The caller supplies the allocator's grow preconditions.
    unsafe { alloc.grow(ptr, old_layout, new_layout) }
        .map(|ptr| ptr.cast::<u8>().as_ptr())
}

#[rr::only_spec]
#[rr::may_unwind_if("False")]
#[rr::params("v" : "val")]
#[rr::requires("Hshrink_size" : "(new_layout.(layout_sz) ≤ old_layout.(layout_sz))%nat")]
#[rr::requires(#iris "raw_allocation π ({A::FreeablePerm} alloc) ptr old_layout v")]
#[rr::exists("res" : "(loc + unit)%type")]
#[rr::returns("res")]
#[rr::ensures(#iris "if_iOk res (λ l, raw_allocation π ({A::FreeablePerm} alloc) l new_layout (take new_layout.(layout_sz) v))")]
#[rr::ensures(#iris "if_iErr res (λ _, raw_allocation π ({A::FreeablePerm} alloc) ptr old_layout v)")]
pub(super) unsafe fn shrink_raw<A: Allocator>(
    alloc: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> Result<*mut u8, AllocError> {
    // SAFETY: The caller supplies the allocator's shrink preconditions.
    unsafe { alloc.shrink(ptr, old_layout, new_layout) }
        .map(|ptr| ptr.cast::<u8>().as_ptr())
}

// TODO(verification): Keep deallocation at the same trusted boundary as the
// allocation operations, consuming both the fitting-layout permission and bytes.
#[rr::only_spec]
#[rr::may_unwind_if("False")]
#[rr::params("v" : "val")]
#[rr::requires(#iris "raw_allocation π ({A::FreeablePerm} alloc) ptr layout v")]
pub(super) unsafe fn deallocate_raw<A: Allocator>(
    alloc: &A,
    ptr: NonNull<u8>,
    layout: Layout,
) {
    // SAFETY: The caller supplies the allocator's deallocate preconditions.
    unsafe { alloc.deallocate(ptr, layout) }
}
