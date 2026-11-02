use core::marker::PhantomData;
use core::ptr::NonNull;

// This wrapper carries only the non-null pointer. Ownership of the pointee
// and the allocation belongs to Box's invariant, not to BoxRaw.
#[rr::export_as(alloc::boxed::BoxRaw)]
#[repr(transparent)]
#[rr::refined_by("l" : "loc")]
pub struct BoxRaw<T: ?Sized> {
    #[rr::field("#(l)")]
    pointer: NonNull<T>,
    #[rr::field("#(tt)")]
    _marker: PhantomData<T>,
}

#[rr::verify]
impl<T: ?Sized> Clone for BoxRaw<T> {
    fn clone(&self) -> Self { *self }
}

#[rr::verify]
impl<T: ?Sized> Copy for BoxRaw<T> {}

#[rr::export_as(alloc::boxed::BoxRaw)]
impl<T: ?Sized> BoxRaw<T> {
    #[rr::requires("Hptr_nonnull": "ptr.(loc_a) ≠ 0")]
    #[rr::returns("ptr")]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        unsafe { BoxRaw { pointer: NonNull::new_unchecked(ptr), _marker: PhantomData } }
    }

    #[rr::returns("self")]
    pub const fn cast<U>(self) -> BoxRaw<U> {
        BoxRaw { pointer: self.pointer.cast(), _marker: PhantomData }
    }

    #[rr::returns("self")]
    pub const fn as_non_null_ptr(self) -> NonNull<T> { self.pointer }

    #[rr::returns("self")]
    pub const fn as_ptr(self) -> *mut T { self.pointer.as_ptr() }
}

#[rr::export_as(alloc::boxed::BoxRaw)]
impl<T> BoxRaw<T> {
    #[rr::exists("l")]
    #[rr::returns("l")]
    #[rr::ensures("l `has_layout_loc` {ly_of T}")]
    #[rr::ensures(#type "l" : "()" @ "uninit UnitSynType")]
    #[rr::ensures(#iris "freeable_nz l 0 1 HeapAlloc")]
    pub const fn dangling() -> Self {
        unsafe { Self::new_unchecked(core::ptr::dangling_mut()) }
    }
}

#[rr::instantiate("FromFn" := "id")]
impl<T: ?Sized> From<BoxRaw<T>> for NonNull<T> {
    #[rr::default_spec]
    fn from(value: BoxRaw<T>) -> Self { value.as_non_null_ptr() }
}
