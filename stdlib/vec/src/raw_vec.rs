//! RawVec operations ported from Rust nightly-2026-08-28
//! (e457a7b0d326d67b4322ef0d11bd715cfaeda48f), alloc/src/raw_vec/mod.rs.
// TODO(verification): Omit upstream stability, cfg, optimization and const-trait
// attributes in this standalone crate. Use ordinary impls without Destruct bounds.

#![rr::import("rrstd.vec.theories", "allocation")]

use core::mem::{Alignment, SizedTypeProperties};
use core::ptr::{self, NonNull, Unique};
use core::{cmp, hint};
use std::alloc::{Allocator, Global, Layout, handle_alloc_error};
use std::collections::TryReserveError;
use std::collections::TryReserveErrorKind::*;

use super::allocation::{allocate_raw, allocate_zeroed_raw, deallocate_raw, grow_raw, shrink_raw};
use super::{Cap, PhantomData, RawVec, RawVecInner};

// TODO(verification): Model the missing intrinsic locally. Unlike an ignored
// MIR assumption, this contract requires its condition to be proved at the call.
#[rr::only_spec]
#[rr::requires("Hcondition" : "condition = true")]
unsafe fn assert_unchecked(condition: bool) {
    unsafe { hint::assert_unchecked(condition) }
}


#[rr::may_unwind_if("True")]
#[rr::ensures("False")]
const fn capacity_overflow() -> ! {
    // TODO(verification): Omit the upstream panic message: its formatting uses
    // unsupported function pointers. Keep the same diverging panic behavior.
    panic!();
}

#[rr::refined_by("bool")]
enum AllocInit {
    #[rr::pattern("false")]
    Uninitialized,
    #[rr::pattern("true")]
    Zeroed,
}

// TODO(verification): Cap is usize rather than the upstream niche type, so zero
// and capacity assignments do not call Cap::new_unchecked/as_inner.
const ZERO_CAP: Cap = 0;

/// # Safety
/// For non-ZSTs, cap must be <= isize::MAX.
#[rr::requires("Hcapacity" : "size_of_st {st_of T} = 0%nat ∨ cap ≤ MaxInt ISize")]
#[rr::returns("if decide (size_of_st {st_of T} = 0%nat) then 0 else cap")]
const unsafe fn new_cap<T>(cap: usize) -> Cap {
    // TODO(verification): Use the modeled size_of shim instead of the generic
    // SizedTypeProperties::IS_ZST associated constant, unsupported by translation.
    if size_of::<T>() == 0 { ZERO_CAP } else { cap }
}

impl<T> RawVec<T, Global> {
    #[rr::exists("l" : "loc")]
    #[rr::returns("(l, raw_vec_effective_capacity (size_of_st {st_of T}) 0, replicate (raw_vec_effective_capacity (size_of_st {st_of T}) 0) None)")]
    pub(crate) const fn new() -> Self {
        Self::new_in(Global)
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc")]
    #[rr::returns("(l, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity), replicate (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity)) None)")]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        // TODO(verification): Use modeled Layout::new instead of generic T::LAYOUT.
        Self { inner: RawVecInner::with_capacity(capacity, Layout::new::<T>()), _marker: PhantomData }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc")]
    #[rr::returns("(l, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity), replicate (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity)) None)")]
    pub(crate) fn with_capacity_zeroed(capacity: usize) -> Self {
        Self {
            // TODO(verification): Layout::new models the same layout as T::LAYOUT.
            inner: RawVecInner::with_capacity_zeroed_in(capacity, Global, Layout::new::<T>()),
            _marker: PhantomData,
        }
    }
}

impl RawVecInner<Global> {
    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc", "cap" : "nat", "v" : "val")]
    #[rr::returns("(l, cap, tt)")]
    #[rr::ensures("cap = (if decide (elem_layout.(layout_sz) = 0%nat) then 0%nat else Z.to_nat capacity)")]
    #[rr::ensures("(elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z")]
    #[rr::ensures(#iris "raw_vec_storage π (λ l sz, freeable_nz l sz 1 HeapAlloc) l cap elem_layout v")]
    fn with_capacity(capacity: usize, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Uninitialized, Global, elem_layout) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }
}

#[rr::returns("raw_vec_min_non_zero_cap size")]
const fn min_non_zero_cap(size: usize) -> usize {
    if size == 1 { 8 } else if size <= 1024 { 4 } else { 1 }
}

impl<T, A: Allocator> RawVec<T, A> {
    pub(crate) const MIN_NON_ZERO_CAP: usize = min_non_zero_cap(size_of::<T>());

    #[rr::exists("l" : "loc")]
    #[rr::returns("(l, raw_vec_effective_capacity (size_of_st {st_of T}) 0, replicate (raw_vec_effective_capacity (size_of_st {st_of T}) 0) None)")]
    pub(crate) const fn new_in(alloc: A) -> Self {
        // TODO(verification): Omit the generic compile-time assertion; the
        // modeled type layout already guarantees size is a multiple of alignment.
        Self { inner: RawVecInner::new_in(alloc, Alignment::of::<T>()), _marker: PhantomData }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc")]
    #[rr::returns("(l, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity), replicate (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity)) None)")]
    pub(crate) fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            // TODO(verification): Layout::new models the same layout as T::LAYOUT.
            inner: RawVecInner::with_capacity_in(capacity, alloc, Layout::new::<T>()),
            _marker: PhantomData,
        }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("res" : "result (loc * nat * list (option {xt_of T}))%type reserve_error")]
    #[rr::returns("res")]
    #[rr::ensures("match res with | inl (l, cap, els) => cap = raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity) ∧ els = replicate cap None | inr _ => True end")]
    #[rr::ensures("match res with | inl _ => True | inr ReserveCapacityOverflow => (MaxInt ISize < Z.of_nat (size_of_st {st_of T}) * capacity)%Z | inr (ReserveAllocError layout) => layout = mk_rust_layout (size_of_st {st_of T} * Z.to_nat capacity) (alignment_of_align (ly_align {ly_of T})) ∧ (0 < Z.of_nat (size_of_st {st_of T}) * capacity ≤ MaxInt ISize)%Z end")]
    pub(crate) fn try_with_capacity_in(capacity: usize, alloc: A) -> Result<Self, TryReserveError> {
        // TODO(verification): Use modeled Layout::new instead of generic T::LAYOUT.
        match RawVecInner::try_with_capacity_in(capacity, alloc, Layout::new::<T>()) {
            Ok(inner) => Ok(Self { inner, _marker: PhantomData }),
            Err(e) => Err(e),
        }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc")]
    #[rr::returns("(l, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity), replicate (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity)) None)")]
    pub(crate) fn with_capacity_zeroed_in(capacity: usize, alloc: A) -> Self {
        Self {
            // TODO(verification): Layout::new models the same layout as T::LAYOUT.
            inner: RawVecInner::with_capacity_zeroed_in(capacity, alloc, Layout::new::<T>()),
            _marker: PhantomData,
        }
    }

    // TODO(verification): Defer into_box: its Box<[MaybeUninit<T>], A> result
    // and raw slice construction require slice support, unlike buffer management.

    /// # Safety
    /// The pointer must be non-null, aligned and allocated by alloc with the
    /// supplied capacity; for non-ZSTs the allocation must fit in isize::MAX.
    #[rr::params("els" : "list (option {xt_of T})")]
    #[rr::requires("Hptr_nonnull" : "ptr.(loc_a) ≠ 0")]
    #[rr::requires("Hptr_aligned" : "ptr `has_layout_loc` {ly_of T}")]
    #[rr::requires("Hallocation_size" : "(size_of_array_in_bytes {st_of T} (Z.to_nat capacity) ≤ MaxInt ISize)%Z")]
    #[rr::requires(#type "ptr" : "RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) els" @ "array_t (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity)) (maybe_uninit {T})")]
    #[rr::requires(#iris "(if decide (size_of_array_in_bytes {st_of T} (Z.to_nat capacity) = 0%nat) then True else {A::FreeablePerm} alloc ptr (size_of_array_in_bytes {st_of T} (Z.to_nat capacity)))")]
    #[rr::returns("(ptr, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity), els)")]
    pub(crate) const unsafe fn from_raw_parts_in(ptr: *mut T, capacity: usize, alloc: A) -> Self {
        unsafe {
            let ptr = ptr.cast();
            let capacity = new_cap::<T>(capacity);
            Self {
                inner: RawVecInner::from_raw_parts_in(ptr, capacity, alloc),
                _marker: PhantomData,
            }
        }
    }

    /// # Safety
    /// See from_raw_parts_in.
    #[rr::params("els" : "list (option {xt_of T})")]
    #[rr::requires("Hptr_aligned" : "ptr `has_layout_loc` {ly_of T}")]
    #[rr::requires("Hallocation_size" : "(size_of_array_in_bytes {st_of T} (Z.to_nat capacity) ≤ MaxInt ISize)%Z")]
    #[rr::requires(#type "ptr" : "RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) els" @ "array_t (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity)) (maybe_uninit {T})")]
    #[rr::requires(#iris "(if decide (size_of_array_in_bytes {st_of T} (Z.to_nat capacity) = 0%nat) then True else {A::FreeablePerm} alloc ptr (size_of_array_in_bytes {st_of T} (Z.to_nat capacity)))")]
    #[rr::returns("(ptr, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat capacity), els)")]
    pub(crate) unsafe fn from_nonnull_in(ptr: NonNull<T>, capacity: usize, alloc: A) -> Self {
        unsafe {
            let ptr = ptr.cast();
            let capacity = new_cap::<T>(capacity);
            Self { inner: RawVecInner::from_nonnull_in(ptr, capacity, alloc), _marker: PhantomData }
        }
    }

    #[rr::returns("self.1.1")]
    pub(crate) const fn ptr(&self) -> *mut T { self.inner.ptr() }
    #[rr::returns("self.1.1")]
    pub(crate) const fn non_null(&self) -> NonNull<T> { self.inner.non_null() }
    #[rr::returns("Z.of_nat self.1.2")]
    pub(crate) const fn capacity(&self) -> usize { self.inner.capacity(size_of::<T>()) }
    // The allocator refinement is existential in the public RawVec invariant.
    #[rr::exists("a" : "{xt_of A}")]
    #[rr::returns("a")]
    pub(crate) const fn allocator(&self) -> &A { self.inner.allocator() }

    #[rr::may_unwind_if("True")]
    #[rr::requires("len ≤ self.cur.1.2")]
    #[rr::exists("l" : "loc", "cap" : "nat")]
    #[rr::observe("self.ghost": "(l, cap, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) (self.cur.2 ++ replicate (cap - self.cur.1.2) None))")]
    #[rr::ensures("(self.cur.1.2 ≤ cap)%nat ∧ len + additional ≤ cap")]
    #[rr::ensures("cap = (if decide (len + additional ≤ self.cur.1.2) then self.cur.1.2 else Z.to_nat (raw_vec_amortized_capacity (size_of_st {st_of T}) self.cur.1.2 (len + additional)))")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) self.cur.2)")]
    pub(crate) fn reserve(&mut self, len: usize, additional: usize) {
        // TODO(verification): Use the modeled constructor instead of the
        // unsupported generic associated layout constant.
        unsafe { self.inner.reserve(len, additional, Layout::new::<T>()) }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc", "cap" : "nat")]
    #[rr::observe("self.ghost": "(l, cap, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) (self.cur.2 ++ replicate (cap - self.cur.1.2) None))")]
    #[rr::ensures("(self.cur.1.2 < cap)%nat ∧ cap = Z.to_nat (raw_vec_amortized_capacity (size_of_st {st_of T}) self.cur.1.2 (Z.of_nat self.cur.1.2 + 1))")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) self.cur.2)")]
    pub(crate) fn grow_one(&mut self) {
        // TODO(verification): Use the modeled constructor instead of the
        // unsupported generic associated layout constant.
        unsafe { self.inner.grow_one(Layout::new::<T>()) }
    }

    #[rr::may_unwind_if("True")]
    #[rr::requires("len ≤ self.cur.1.2")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc", "cap" : "nat")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost": "match res with | Ok _ => (l, cap, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) (self.cur.2 ++ replicate (cap - self.cur.1.2) None)) | Err _ => (self.cur.1.1, self.cur.1.2, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) self.cur.2) end")]
    #[rr::ensures("if_Ok res (λ _, (self.cur.1.2 ≤ cap)%nat ∧ len + additional ≤ cap ∧ cap = (if decide (len + additional ≤ self.cur.1.2) then self.cur.1.2 else Z.to_nat (raw_vec_amortized_capacity (size_of_st {st_of T}) self.cur.1.2 (len + additional))))")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => (MaxInt USize < len + additional ∨ MaxInt ISize < Z.of_nat (size_of_st {st_of T}) * raw_vec_amortized_capacity (size_of_st {st_of T}) self.cur.1.2 (len + additional))%Z | ReserveAllocError layout => layout = mk_rust_layout (size_of_st {st_of T} * Z.to_nat (raw_vec_amortized_capacity (size_of_st {st_of T}) self.cur.1.2 (len + additional))) (alignment_of_align (ly_align {ly_of T})) ∧ (0 < Z.of_nat (size_of_st {st_of T}) * raw_vec_amortized_capacity (size_of_st {st_of T}) self.cur.1.2 (len + additional) ≤ MaxInt ISize)%Z end)")]
    pub(crate) fn try_reserve(&mut self, len: usize, additional: usize) -> Result<(), TryReserveError> {
        // TODO(verification): Use the modeled constructor instead of the
        // unsupported generic associated layout constant.
        unsafe { self.inner.try_reserve(len, additional, Layout::new::<T>()) }
    }

    #[rr::may_unwind_if("True")]
    #[rr::requires("len ≤ self.cur.1.2")]
    #[rr::exists("l" : "loc", "cap" : "nat")]
    #[rr::observe("self.ghost": "(l, cap, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) (self.cur.2 ++ replicate (cap - self.cur.1.2) None))")]
    #[rr::ensures("(self.cur.1.2 ≤ cap)%nat ∧ len + additional ≤ cap")]
    #[rr::ensures("cap = (if decide (len + additional ≤ self.cur.1.2) then self.cur.1.2 else Z.to_nat (len + additional))")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) self.cur.2)")]
    pub(crate) fn reserve_exact(&mut self, len: usize, additional: usize) {
        // TODO(verification): Use the modeled constructor instead of the generic
        // associated layout constant, which the frontend cannot translate.
        unsafe { self.inner.reserve_exact(len, additional, Layout::new::<T>()) }
    }

    #[rr::may_unwind_if("True")]
    #[rr::requires("len ≤ self.cur.1.2")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc", "cap" : "nat")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost": "match res with | Ok _ => (l, cap, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) (self.cur.2 ++ replicate (cap - self.cur.1.2) None)) | Err _ => (self.cur.1.1, self.cur.1.2, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) self.cur.2) end")]
    #[rr::ensures("if_Ok res (λ _, (self.cur.1.2 ≤ cap)%nat ∧ len + additional ≤ cap ∧ cap = (if decide (len + additional ≤ self.cur.1.2) then self.cur.1.2 else Z.to_nat (len + additional)))")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => (MaxInt USize < len + additional ∨ MaxInt ISize < Z.of_nat (size_of_st {st_of T}) * (len + additional))%Z | ReserveAllocError layout => layout = mk_rust_layout (size_of_st {st_of T} * Z.to_nat (len + additional)) (alignment_of_align (ly_align {ly_of T})) ∧ (0 < Z.of_nat (size_of_st {st_of T}) * (len + additional) ≤ MaxInt ISize)%Z end)")]
    pub(crate) fn try_reserve_exact(&mut self, len: usize, additional: usize) -> Result<(), TryReserveError> {
        // TODO(verification): Use Layout::new to avoid the unsupported generic
        // associated constant while retaining the same element layout.
        unsafe { self.inner.try_reserve_exact(len, additional, Layout::new::<T>()) }
    }

    #[rr::may_unwind_if("True")]
    #[rr::requires("Hshrink_cap": "cap ≤ self.cur.1.2")]
    #[rr::exists("l" : "loc")]
    #[rr::observe("self.ghost": "(l, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat cap), RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) (take (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat cap)) self.cur.2))")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) self.cur.2)")]
    pub(crate) fn shrink_to_fit(&mut self, cap: usize) {
        // TODO(verification): Use the modeled layout constructor instead of the
        // generic associated layout constant unsupported by the frontend.
        unsafe { self.inner.shrink_to_fit(cap, Layout::new::<T>()) }
    }

    #[rr::may_unwind_if("False")]
    #[rr::requires("Hshrink_cap": "cap ≤ self.cur.1.2")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost": "match res with | Ok _ => (l, raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat cap), RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) (take (raw_vec_effective_capacity (size_of_st {st_of T}) (Z.to_nat cap)) self.cur.2)) | Err _ => (self.cur.1.1, self.cur.1.2, RT_xrt (listRT (place_rfnRT (optionRT (place_rfnRT {rt_of T})))) self.cur.2) end")]
    #[rr::ensures("if_Err res (λ err, err = ReserveAllocError (mk_rust_layout (size_of_st {st_of T} * Z.to_nat cap) (alignment_of_align (ly_align {ly_of T}))) ∧ 0 < cap ∧ size_of_st {st_of T} ≠ 0%nat)")]
    pub(crate) fn try_shrink_to_fit(&mut self, cap: usize) -> Result<(), TryReserveError> {
        // TODO(verification): Use the modeled layout constructor instead of the
        // generic associated layout constant unsupported by the frontend.
        unsafe { self.inner.try_shrink_to_fit(cap, Layout::new::<T>()) }
    }
}

impl<A: Allocator> RawVecInner<A> {
    // TODO(verification): Temporarily trust this constructor while the upstream
    // NonZero-dependent dangling-pointer construction remains deferred.
    #[rr::only_spec]
    #[rr::exists("l" : "loc")]
    #[rr::returns("(l, 0%nat, alloc)")]
    #[rr::ensures("l.(loc_a) ≠ 0 ∧ l `aligned_to` (alignment_to_align_nat align)")]
    #[rr::ensures(#iris "loc_in_bounds l 0 0")]
    const fn new_in(alloc: A, align: Alignment) -> Self {
        let ptr = Unique::from_non_null(NonNull::without_provenance(align.as_nonzero_usize()));
        Self { ptr, cap: ZERO_CAP, alloc }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc", "cap" : "nat", "v" : "val")]
    #[rr::returns("(l, cap, alloc)")]
    #[rr::ensures("cap = (if decide (elem_layout.(layout_sz) = 0%nat) then 0%nat else Z.to_nat capacity)")]
    #[rr::ensures("(elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z")]
    #[rr::ensures(#iris "raw_vec_storage π ({A::FreeablePerm} alloc) l cap elem_layout v")]
    fn with_capacity_in(capacity: usize, alloc: A, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Uninitialized, alloc, elem_layout) {
            Ok(this) => {
                // TODO(verification): Route the intrinsic through its local
                // contract so capacity sufficiency is an explicit obligation.
                unsafe { assert_unchecked(!this.needs_to_grow(0, capacity, elem_layout)) };
                this
            }
            Err(err) => handle_error(err),
        }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("res" : "result (loc * nat * {xt_of A})%type reserve_error", "v" : "val")]
    #[rr::returns("res")]
    #[rr::ensures(#iris "if_iOk res (λ '(l, cap, _), raw_vec_storage π ({A::FreeablePerm} alloc) l cap elem_layout v)")]
    #[rr::ensures("if_Ok res (λ '(_, cap, a), a = alloc ∧ cap = (if decide (elem_layout.(layout_sz) = 0%nat) then 0%nat else Z.to_nat capacity) ∧ (elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z)")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => (MaxInt ISize < Z.of_nat elem_layout.(layout_sz) * capacity)%Z | ReserveAllocError layout => layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat capacity) elem_layout.(layout_alignment) ∧ (0 < Z.of_nat elem_layout.(layout_sz) * capacity ≤ MaxInt ISize)%Z end)")]
    fn try_with_capacity_in(capacity: usize, alloc: A, elem_layout: Layout) -> Result<Self, TryReserveError> {
        Self::try_allocate_in(capacity, AllocInit::Uninitialized, alloc, elem_layout)
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("l" : "loc", "cap" : "nat")]
    #[rr::returns("(l, cap, alloc)")]
    #[rr::ensures("cap = (if decide (elem_layout.(layout_sz) = 0%nat) then 0%nat else Z.to_nat capacity)")]
    #[rr::ensures("(elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z")]
    #[rr::ensures(#iris "raw_vec_storage π ({A::FreeablePerm} alloc) l cap elem_layout (replicate (elem_layout.(layout_sz) * cap) (MByte byte0))")]
    fn with_capacity_zeroed_in(capacity: usize, alloc: A, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Zeroed, alloc, elem_layout) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }

    #[rr::may_unwind_if("True")]
    #[rr::exists("res" : "result (loc * nat * {xt_of A})%type reserve_error", "v" : "val")]
    #[rr::returns("res")]
    #[rr::ensures(#iris "if_iOk res (λ '(l, cap, _), raw_vec_storage π ({A::FreeablePerm} alloc) l cap elem_layout v)")]
    #[rr::ensures("if_Ok res (λ '(_, cap, a), a = alloc ∧ cap = (if decide (elem_layout.(layout_sz) = 0%nat) then 0%nat else Z.to_nat capacity) ∧ (init = true → v = replicate (elem_layout.(layout_sz) * cap) (MByte byte0)) ∧ (elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z)")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => (MaxInt ISize < Z.of_nat elem_layout.(layout_sz) * capacity)%Z | ReserveAllocError layout => layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat capacity) elem_layout.(layout_alignment) ∧ (0 < Z.of_nat elem_layout.(layout_sz) * capacity ≤ MaxInt ISize)%Z end)")]
    fn try_allocate_in(capacity: usize, init: AllocInit, alloc: A, elem_layout: Layout) -> Result<Self, TryReserveError> {
        let layout = match layout_array(capacity, elem_layout) {
            Ok(layout) => layout,
            Err(_) => return Err(CapacityOverflow.into()),
        };
        if layout.size() == 0 {
            return Ok(Self::new_in(alloc, elem_layout.alignment()));
        }
        // TODO(verification): Use trusted thin-pointer wrappers instead of the
        // allocator's slice-valued results; RawVec does not inspect their length.
        let result = match init {
            AllocInit::Uninitialized => allocate_raw(&alloc, layout),
            AllocInit::Zeroed => allocate_zeroed_raw(&alloc, layout),
        };
        let ptr = match result {
            Ok(ptr) => ptr,
            Err(_) => return Err(AllocError { layout, non_exhaustive: () }.into()),
        };
        Ok(Self {
            // TODO(verification): The wrapper guarantees a non-null raw pointer,
            // replacing the upstream cast from NonNull<[u8]>.
            ptr: unsafe { Unique::new_unchecked(ptr) },
            cap: capacity,
            alloc,
        })
    }

    #[rr::requires("Hptr_nonnull" : "ptr.(loc_a) ≠ 0")]
    #[rr::requires("Hstored_cap" : "cap ≤ MaxInt ISize")]
    #[rr::returns("(ptr, Z.to_nat cap, alloc)")]
    pub(super) const unsafe fn from_raw_parts_in(ptr: *mut u8, cap: Cap, alloc: A) -> Self {
        Self { ptr: unsafe { Unique::new_unchecked(ptr) }, cap, alloc }
    }

    #[rr::requires("Hstored_cap" : "cap ≤ MaxInt ISize")]
    #[rr::returns("(ptr, Z.to_nat cap, alloc)")]
    unsafe fn from_nonnull_in(ptr: NonNull<u8>, cap: Cap, alloc: A) -> Self {
        Self { ptr: ptr.into(), cap, alloc }
    }

    #[rr::returns("self.1.1")]
    const fn ptr<T>(&self) -> *mut T { self.non_null::<T>().as_ptr() }
    #[rr::returns("self.1.1")]
    const fn non_null<T>(&self) -> NonNull<T> { self.ptr.cast().as_non_null_ptr() }
    #[rr::returns("Z.of_nat (raw_vec_effective_capacity (Z.to_nat elem_size) self.1.2)")]
    const fn capacity(&self, elem_size: usize) -> usize {
        if elem_size == 0 { usize::MAX } else { self.cap }
    }
    #[rr::returns("self.2")]
    const fn allocator(&self) -> &A { &self.alloc }

    /// # Safety
    /// elem_layout must match the original element layout, and its size must be
    /// a multiple of its alignment.
    // TODO(verification): Use a non-const function to avoid requiring the
    // upstream const Into conversion and its additional const-trait features.
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::returns("if decide (elem_layout.(layout_sz) = 0%nat ∨ self.1.2 = 0%nat) then None else Some ( *[self.1.1; mk_rust_layout (elem_layout.(layout_sz) * self.1.2) elem_layout.(layout_alignment)])")]
    unsafe fn current_memory(&self, elem_layout: Layout) -> Option<(NonNull<u8>, Layout)> {
        if elem_layout.size() == 0 || self.cap == 0 {
            None
        } else {
            unsafe {
                let alloc_size = elem_layout.size().unchecked_mul(self.cap);
                let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
                Some((self.ptr.into(), layout))
            }
        }
    }

    #[rr::may_unwind_if("True")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hlen_capacity" : "len ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("l" : "loc", "cap" : "nat", "suffix" : "val")]
    #[rr::observe("self.ghost" : "(l, cap, $# self.cur.2)")]
    #[rr::ensures(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) l cap elem_layout (v ++ suffix)")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, $# self.cur.2)")]
    #[rr::ensures_on_unwind(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::ensures("len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) cap) ∧ cap = (if decide (len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)) then self.cur.1.2 else Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional))) ∧ (elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z")]
    unsafe fn reserve(&mut self, len: usize, additional: usize, elem_layout: Layout) {
        #[cold]
        #[rr::may_unwind_if("True")]
        #[rr::params("v" : "val")]
        #[rr::requires("Hlen_capacity" : "len ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) slf.cur.1.2)")]
        #[rr::requires("Hgrow_requested" : "Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) slf.cur.1.2) < len + additional")]
        #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * slf.cur.1.2 ≤ MaxInt ISize)%Z")]
        #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} slf.cur.2) slf.cur.1.1 slf.cur.1.2 elem_layout v")]
        #[rr::exists("l" : "loc", "suffix" : "val")]
        #[rr::observe("slf.ghost" : "(l, Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) slf.cur.1.2 (len + additional)), $# slf.cur.2)")]
        #[rr::ensures(#iris "raw_vec_storage π ({A::FreeablePerm} slf.cur.2) l (Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) slf.cur.1.2 (len + additional))) elem_layout (v ++ suffix)")]
        #[rr::ensures_on_unwind(#iris "Obs slf.ghost (slf.cur.1.1, slf.cur.1.2, $# slf.cur.2)")]
        #[rr::ensures_on_unwind(#iris "raw_vec_storage π ({A::FreeablePerm} slf.cur.2) slf.cur.1.1 slf.cur.1.2 elem_layout v")]
        #[rr::ensures("elem_layout.(layout_sz) ≠ 0%nat ∧ (len + additional ≤ MaxInt USize)%Z ∧ (elem_layout.(layout_sz) * Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) slf.cur.1.2 (len + additional)) ≤ MaxInt ISize)%Z")]
        unsafe fn do_reserve_and_handle<A: Allocator>(slf: &mut RawVecInner<A>, len: usize, additional: usize, elem_layout: Layout) {
            if let Err(err) = unsafe { slf.grow_amortized(len, additional, elem_layout) } {
                handle_error(err);
            }
        }
        if self.needs_to_grow(len, additional, elem_layout) {
            unsafe { do_reserve_and_handle(self, len, additional, elem_layout) };
        }
    }

    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hlen_capacity" : "len ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc", "cap" : "nat", "suffix" : "val")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost" : "match res with | inl _ => (l, cap, $# self.cur.2) | inr _ => (self.cur.1.1, self.cur.1.2, $# self.cur.2) end")]
    #[rr::ensures(#iris "if_iOk res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) l cap elem_layout (v ++ suffix))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v)")]
    #[rr::ensures("if_Ok res (λ _, len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) cap) ∧ cap = (if decide (len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)) then self.cur.1.2 else Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional))) ∧ (elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z)")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => elem_layout.(layout_sz) = 0%nat ∨ (MaxInt USize < len + additional)%Z ∨ (MaxInt ISize < Z.of_nat elem_layout.(layout_sz) * raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional))%Z | ReserveAllocError layout => layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional))) elem_layout.(layout_alignment) ∧ (0 < Z.of_nat elem_layout.(layout_sz) * raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional) ≤ MaxInt ISize)%Z end)")]
    #[rr::ensures("if_Err res (λ _, Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2) < len + additional)")]
    unsafe fn try_reserve(&mut self, len: usize, additional: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        if self.needs_to_grow(len, additional, elem_layout) {
            unsafe { self.grow_amortized(len, additional, elem_layout)? };
        }
        // TODO(verification): Use the local intrinsic boundary so reservation
        // sufficiency remains a proved precondition rather than an ignored Assume.
        unsafe { assert_unchecked(!self.needs_to_grow(len, additional, elem_layout)) };
        Ok(())
    }

    #[rr::may_unwind_if("True")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("l" : "loc", "suffix" : "val")]
    #[rr::observe("self.ghost" : "(l, Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (Z.of_nat self.cur.1.2 + 1)), $# self.cur.2)")]
    #[rr::ensures(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) l (Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (Z.of_nat self.cur.1.2 + 1))) elem_layout (v ++ suffix)")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, $# self.cur.2)")]
    #[rr::ensures_on_unwind(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::ensures("elem_layout.(layout_sz) ≠ 0%nat ∧ self.cur.1.2 < Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (Z.of_nat self.cur.1.2 + 1)) ∧ (elem_layout.(layout_sz) * Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (Z.of_nat self.cur.1.2 + 1)) ≤ MaxInt ISize)%Z")]
    unsafe fn grow_one(&mut self, elem_layout: Layout) {
        // TODO(verification): Read the capacity before creating the mutable
        // reborrow; the model does not support the upstream two-phase borrow.
        let cap = self.cap;
        if let Err(err) = unsafe { self.grow_amortized(cap, 1, elem_layout) } {
            handle_error(err);
        }
    }

    #[rr::may_unwind_if("True")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hlen_capacity" : "len ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("l" : "loc", "cap" : "nat", "suffix" : "val")]
    #[rr::observe("self.ghost" : "(l, cap, $# self.cur.2)")]
    #[rr::ensures(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) l cap elem_layout (v ++ suffix)")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, $# self.cur.2)")]
    #[rr::ensures_on_unwind(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::ensures("len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) cap) ∧ cap = (if decide (len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)) then self.cur.1.2 else Z.to_nat (len + additional)) ∧ (elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z")]
    unsafe fn reserve_exact(&mut self, len: usize, additional: usize, elem_layout: Layout) {
        if let Err(err) = unsafe { self.try_reserve_exact(len, additional, elem_layout) } {
            handle_error(err);
        }
    }

    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hlen_capacity" : "len ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc", "cap" : "nat", "suffix" : "val")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost" : "match res with | inl _ => (l, cap, $# self.cur.2) | inr _ => (self.cur.1.1, self.cur.1.2, $# self.cur.2) end")]
    #[rr::ensures(#iris "if_iOk res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) l cap elem_layout (v ++ suffix))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v)")]
    #[rr::ensures("if_Ok res (λ _, len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) cap) ∧ cap = (if decide (len + additional ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)) then self.cur.1.2 else Z.to_nat (len + additional)) ∧ (elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z)")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => elem_layout.(layout_sz) = 0%nat ∨ (MaxInt USize < len + additional)%Z ∨ (MaxInt ISize < Z.of_nat elem_layout.(layout_sz) * (len + additional))%Z | ReserveAllocError layout => layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat (len + additional)) elem_layout.(layout_alignment) ∧ (0 < Z.of_nat elem_layout.(layout_sz) * (len + additional) ≤ MaxInt ISize)%Z end)")]
    #[rr::ensures("if_Err res (λ _, Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2) < len + additional)")]
    unsafe fn try_reserve_exact(&mut self, len: usize, additional: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        if self.needs_to_grow(len, additional, elem_layout) {
            unsafe { self.grow_exact(len, additional, elem_layout)? };
        }
        // TODO(verification): Use the local intrinsic boundary so reservation
        // sufficiency remains a proved precondition rather than an ignored Assume.
        unsafe { assert_unchecked(!self.needs_to_grow(len, additional, elem_layout)) };
        Ok(())
    }

    #[rr::returns("bool_decide (additional > (Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.1.2) - len) mod (MaxInt USize + 1))")]
    const fn needs_to_grow(&self, len: usize, additional: usize, elem_layout: Layout) -> bool {
        additional > self.capacity(elem_layout.size()).wrapping_sub(len)
    }

    // TODO(verification): Accept the thin raw pointer returned by our wrappers
    // instead of NonNull<[u8]>; successful allocation guarantees non-nullness.
    #[rr::requires("Hptr_nonnull" : "ptr.(loc_a) ≠ 0")]
    #[rr::requires("Hnew_cap" : "cap ≤ MaxInt ISize")]
    #[rr::observe("self.ghost" : "(ptr, Z.to_nat cap, $# self.cur.2)")]
    unsafe fn set_ptr_and_cap(&mut self, ptr: *mut u8, cap: usize) {
        self.ptr = unsafe { Unique::new_unchecked(ptr) };
        self.cap = cap;
    }

    /// # Safety
    /// elem_layout must match the original padded element layout and
    /// additional must be positive. For non-ZSTs, len + additional must
    /// exceed the current capacity; ZSTs return capacity overflow directly.
    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hlen_capacity" : "len ≤ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2)")]
    #[rr::requires("Hadditional_positive" : "0 < additional")]
    #[rr::requires("Hgrow_requested" : "elem_layout.(layout_sz) = 0%nat ∨ Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2) < len + additional")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc", "suffix" : "val")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost" : "match res with | inl _ => (l, Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional)), $# self.cur.2) | inr _ => (self.cur.1.1, self.cur.1.2, $# self.cur.2) end")]
    #[rr::ensures(#iris "if_iOk res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) l (Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional))) elem_layout (v ++ suffix))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v)")]
    #[rr::ensures("if_Ok res (λ _, elem_layout.(layout_sz) ≠ 0%nat ∧ (len + additional ≤ MaxInt USize)%Z ∧ (elem_layout.(layout_sz) * Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional)) ≤ MaxInt ISize)%Z)")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => elem_layout.(layout_sz) = 0%nat ∨ (MaxInt USize < len + additional)%Z ∨ (MaxInt ISize < Z.of_nat elem_layout.(layout_sz) * raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional))%Z | ReserveAllocError layout => layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat (raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional))) elem_layout.(layout_alignment) ∧ (0 < Z.of_nat elem_layout.(layout_sz) * raw_vec_amortized_capacity elem_layout.(layout_sz) self.cur.1.2 (len + additional) ≤ MaxInt ISize)%Z end)")]
    unsafe fn grow_amortized(&mut self, len: usize, additional: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        debug_assert!(additional > 0);
        if elem_layout.size() == 0 {
            return Err(CapacityOverflow.into());
        }
        let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
        let cap = cmp::max(self.cap * 2, required_cap);
        let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);
        let ptr = unsafe { self.finish_grow(cap, elem_layout)? };
        unsafe { self.set_ptr_and_cap(ptr, cap) };
        Ok(())
    }

    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hgrow_requested" : "Z.of_nat (raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2) < len + additional")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc", "suffix" : "val")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost" : "match res with | inl _ => (l, Z.to_nat (len + additional), $# self.cur.2) | inr _ => (self.cur.1.1, self.cur.1.2, $# self.cur.2) end")]
    #[rr::ensures(#iris "if_iOk res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) l (Z.to_nat (len + additional)) elem_layout (v ++ suffix))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v)")]
    #[rr::ensures("if_Ok res (λ _, elem_layout.(layout_sz) ≠ 0%nat ∧ (len + additional ≤ MaxInt USize)%Z ∧ (elem_layout.(layout_sz) * Z.to_nat (len + additional) ≤ MaxInt ISize)%Z)")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => elem_layout.(layout_sz) = 0%nat ∨ (MaxInt USize < len + additional)%Z ∨ (MaxInt ISize < Z.of_nat elem_layout.(layout_sz) * (len + additional))%Z | ReserveAllocError layout => layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat (len + additional)) elem_layout.(layout_alignment) ∧ (0 < Z.of_nat elem_layout.(layout_sz) * (len + additional) ≤ MaxInt ISize)%Z end)")]
    unsafe fn grow_exact(&mut self, len: usize, additional: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        if elem_layout.size() == 0 {
            return Err(CapacityOverflow.into());
        }
        let cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
        let ptr = unsafe { self.finish_grow(cap, elem_layout)? };
        unsafe { self.set_ptr_and_cap(ptr, cap) };
        Ok(())
    }

    /// # Safety
    /// elem_layout must match the original padded element layout and cap must
    /// exceed the current capacity.
    #[cold]
    // TODO(verification): Return a raw pointer and route allocator operations
    // through the trusted wrappers, avoiding slice types in the verified body.
    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Helem_nonzero" : "elem_layout.(layout_sz) ≠ 0%nat")]
    #[rr::requires("Hgrow_cap" : "Z.of_nat self.1.2 < cap")]
    #[rr::requires("Hallocation_size" : "(elem_layout.(layout_sz) * self.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.2) self.1.1 self.1.2 elem_layout v")]
    #[rr::exists("res" : "result loc reserve_error", "suffix" : "val")]
    #[rr::returns("res")]
    #[rr::ensures(#iris "if_iOk res (λ l, raw_vec_storage π ({A::FreeablePerm} self.2) l (Z.to_nat cap) elem_layout (v ++ suffix))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.2) self.1.1 self.1.2 elem_layout v)")]
    #[rr::ensures("if_Ok res (λ _, (elem_layout.(layout_sz) * Z.to_nat cap ≤ MaxInt ISize)%Z)")]
    #[rr::ensures("if_Err res (λ err, match err with | ReserveCapacityOverflow => (MaxInt ISize < Z.of_nat elem_layout.(layout_sz) * cap)%Z | ReserveAllocError layout => layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat cap) elem_layout.(layout_alignment) ∧ (Z.of_nat elem_layout.(layout_sz) * cap ≤ MaxInt ISize)%Z end)")]
    unsafe fn finish_grow(&self, cap: usize, elem_layout: Layout) -> Result<*mut u8, TryReserveError> {
        let new_layout = layout_array(cap, elem_layout)?;
        let memory = if let Some((ptr, old_layout)) = unsafe { self.current_memory(elem_layout) } {
            debug_assert!(old_layout.align() == new_layout.align());
            unsafe {
                // TODO(verification): Use the local intrinsic boundary so the
                // alignment equality is a proved precondition, not an ignored Assume.
                assert_unchecked(old_layout.align() == new_layout.align());
                grow_raw(&self.alloc, ptr, old_layout, new_layout)
            }
        } else {
            allocate_raw(&self.alloc, new_layout)
        };
        memory.map_err(
            #[rr::returns("ReserveAllocError {new_layout}")]
            |_| AllocError { layout: new_layout, non_exhaustive: () }.into(),
        )
    }

    #[rr::may_unwind_if("True")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hshrink_cap": "cap ≤ raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2")]
    #[rr::requires("Hallocation_size": "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("l" : "loc")]
    #[rr::observe("self.ghost": "(l, (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap), $# self.cur.2)")]
    #[rr::ensures(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) l (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap) elem_layout (take (elem_layout.(layout_sz) * Z.to_nat cap) v)")]
    #[rr::ensures_on_unwind(#iris "Obs self.ghost (self.cur.1.1, self.cur.1.2, $# self.cur.2)")]
    #[rr::ensures_on_unwind(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    unsafe fn shrink_to_fit(&mut self, cap: usize, elem_layout: Layout) {
        if let Err(err) = unsafe { self.shrink(cap, elem_layout) } {
            handle_error(err);
        }
    }

    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hshrink_cap": "cap ≤ raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2")]
    #[rr::requires("Hallocation_size": "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost": "match res with | Ok _ => (l, (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap), $# self.cur.2) | Err _ => (self.cur.1.1, self.cur.1.2, $# self.cur.2) end")]
    #[rr::ensures(#iris "if_iOk res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) l (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap) elem_layout (take (elem_layout.(layout_sz) * Z.to_nat cap) v))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v)")]
    #[rr::ensures("if_Err res (λ err, ∃ layout, err = ReserveAllocError layout ∧ layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat cap) elem_layout.(layout_alignment) ∧ (0 < cap ∧ elem_layout.(layout_sz) ≠ 0%nat))")]
    unsafe fn try_shrink_to_fit(&mut self, cap: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        unsafe { self.shrink(cap, elem_layout) }
    }

    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hshrink_cap": "cap ≤ raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2")]
    #[rr::requires("Hallocation_size": "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost": "match res with | Ok _ => (l, (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap), $# self.cur.2) | Err _ => (self.cur.1.1, self.cur.1.2, $# self.cur.2) end")]
    #[rr::ensures(#iris "if_iOk res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) l (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap) elem_layout (take (elem_layout.(layout_sz) * Z.to_nat cap) v))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v)")]
    #[rr::ensures("if_Err res (λ err, ∃ layout, err = ReserveAllocError layout ∧ layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat cap) elem_layout.(layout_alignment) ∧ (0 < cap ∧ elem_layout.(layout_sz) ≠ 0%nat))")]
    unsafe fn shrink(&mut self, cap: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        // TODO(verification): Omit the custom panic message: its formatting
        // machinery contains function pointers unsupported by the frontend.
        assert!(cap <= self.capacity(elem_layout.size()));
        unsafe { self.shrink_unchecked(cap, elem_layout) }
    }

    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hshrink_cap": "cap ≤ raw_vec_effective_capacity elem_layout.(layout_sz) self.cur.1.2")]
    #[rr::requires("Hallocation_size": "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::exists("res" : "result unit reserve_error", "l" : "loc")]
    #[rr::returns("res")]
    #[rr::observe("self.ghost": "match res with | Ok _ => (l, (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap), $# self.cur.2) | Err _ => (self.cur.1.1, self.cur.1.2, $# self.cur.2) end")]
    #[rr::ensures(#iris "if_iOk res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) l (if decide (elem_layout.(layout_sz) * self.cur.1.2 = 0)%nat then self.cur.1.2 else Z.to_nat cap) elem_layout (take (elem_layout.(layout_sz) * Z.to_nat cap) v))")]
    #[rr::ensures(#iris "if_iErr res (λ _, raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v)")]
    #[rr::ensures("if_Err res (λ err, ∃ layout, err = ReserveAllocError layout ∧ layout = mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat cap) elem_layout.(layout_alignment) ∧ (0 < cap ∧ elem_layout.(layout_sz) ≠ 0%nat))")]
    unsafe fn shrink_unchecked(&mut self, cap: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        let Some((ptr, layout)) = (unsafe { self.current_memory(elem_layout) }) else {
            return Ok(());
        };
        if cap == 0 {
            // TODO(verification): Use the local trusted deallocation boundary.
            unsafe { deallocate_raw(&self.alloc, ptr, layout) };
            self.ptr = unsafe { Unique::new_unchecked(ptr::without_provenance_mut(elem_layout.align())) };
            self.cap = ZERO_CAP;
        } else {
            let ptr = unsafe {
                let new_size = elem_layout.size().unchecked_mul(cap);
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                // TODO(verification): Replace the slice-valued shrink result
                // with the raw-pointer wrapper result.
                shrink_raw(&self.alloc, ptr, layout, new_layout)
                    .map_err(
                        #[rr::returns("ReserveAllocError {new_layout}")]
                        |_| AllocError { layout: new_layout, non_exhaustive: () },
                    )?
            };
            unsafe { self.set_ptr_and_cap(ptr, cap) };
        }
        Ok(())
    }

    /// # Safety
    /// The original element layout must be supplied and self must not be used
    /// again: deallocation leaves ptr and cap unchanged.
    #[rr::may_unwind_if("False")]
    #[rr::params("v" : "val")]
    #[rr::requires("Hallocation_size": "(elem_layout.(layout_sz) * self.cur.1.2 ≤ MaxInt ISize)%Z")]
    #[rr::requires(#iris "raw_vec_storage π ({A::FreeablePerm} self.cur.2) self.cur.1.1 self.cur.1.2 elem_layout v")]
    #[rr::observe("self.ghost": "(self.cur.1.1, self.cur.1.2, $# self.cur.2)")]
    pub(super) unsafe fn deallocate(&mut self, elem_layout: Layout) {
        if let Some((ptr, layout)) = unsafe { self.current_memory(elem_layout) } {
            // TODO(verification): Use the local trusted deallocation boundary.
            unsafe { deallocate_raw(&self.alloc, ptr, layout) };
        }
    }
}

#[rr::may_unwind_if("True")]
#[rr::ensures("False")]
fn handle_error(e: TryReserveError) -> ! {
    match e.kind() {
        CapacityOverflow => capacity_overflow(),
        AllocError { layout, .. } => handle_alloc_error(layout),
    }
}

// TODO(verification): Use an ordinary function rather than the upstream const
// function, matching the non-const port.
#[rr::returns("if bool_decide (Z.of_nat elem_layout.(layout_sz) * cap ≤ MaxInt ISize) then Ok (mk_rust_layout (elem_layout.(layout_sz) * Z.to_nat cap) elem_layout.(layout_alignment)) else Err ReserveCapacityOverflow")]
fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError> {
    debug_assert!(elem_layout.size() == elem_layout.pad_to_align().size());
    elem_layout.repeat_packed(cap).map_err(
        #[rr::returns("ReserveCapacityOverflow")]
        |_| CapacityOverflow.into(),
    )
}
