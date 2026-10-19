#![rr::include("ptr")]
#![rr::include("result")]
#![rr::include("mem")]
#![rr::include("num")]
#![rr::include("option")]
#![rr::import("rrstd.alloc.theories", "layout")]

use std::mem::Alignment;
use core::mem;


#[rr::export_as(alloc::alloc::Layout)]
#[rr::refined_by("l" : "rust_layout")]
#[derive(Copy, Clone)]
// Rust requires:
// > All layouts have an associated size and a power-of-two alignment. The size, when rounded up to
// > the nearest multiple of `align`, does not overflow `isize` (i.e., the rounded value will always be
// > less than or equal to `isize::MAX`).
// For convenience we strengthen this and require `size` to be a multiple of `align`.
// (This is more convenient, as it then fits Rust's actual layout requirements).
// TODO: do we run into an problems in desirable cases for this?
#[rr::inv("layout_wf l")]
#[rr::inv("Z.of_nat l.(layout_sz) ∈ isize")]
pub struct Layout {
    // size of the requested block of memory, measured in bytes.
    #[rr::field("#(Z.of_nat l.(layout_sz))")]
    size: usize,

    // alignment of the requested block of memory, measured in bytes.
    // we ensure that this is always a power-of-two, because API's
    // like `posix_memalign` require it and it is a reasonable
    // constraint to impose on Layout constructors.
    //
    // (However, we do not analogously require `align >= sizeof(void*)`,
    //  even though that is *also* a requirement of `posix_memalign`.)
    #[rr::field("#(l.(layout_alignment))")]
    align: Alignment,
}

#[rr::export_as(alloc::alloc::LayoutError)]
pub struct LayoutError;

#[rr::export_as(alloc::alloc::Layout)]
impl Layout {
    #[rr::returns("Z.of_nat self.(layout_sz)")]
    pub const fn size(&self) -> usize {
        self.size
    }

    #[rr::returns("Z.of_nat (layout_alignment_nat self)")]
    pub const fn align(&self) -> usize {
        self.align.as_usize()
    }

    #[rr::returns("self.(layout_alignment)")]
    pub const fn alignment(&self) -> Alignment {
        self.align
    }

    #[rr::returns("self")]
    pub const fn pad_to_align(&self) -> Self {
        // TODO(verification): The current Layout invariant already requires
        // size to be a multiple of alignment, so upstream's rounding is the
        // identity. Revisit this body and spec if that invariant is relaxed.
        Layout { size: self.size, align: self.align }
    }

    #[rr::returns("if bool_decide (Z.of_nat self.(layout_sz) * n ≤ MaxInt ISize) then Ok (mk_rust_layout (self.(layout_sz) * Z.to_nat n) self.(layout_alignment)) else Err ( *[])")]
    pub const fn repeat_packed(&self, n: usize) -> Result<Self, LayoutError> {
        if let Some(size) = self.size.checked_mul(n) {
            Self::from_size_alignment(size, self.align)
        } else {
            Err(LayoutError)
        }
    }

    // TODO: for stronger spec we'd need the weaker invariant on the size...
    #[rr::requires("Hsize_aligned": "Z.divide (alignment_to_align alignment) size")]
    #[rr::returns("if bool_decide (size ≤ MaxInt ISize) then Ok (mk_rust_layout (Z.to_nat size) alignment) else Err ( *[])")]
    pub const fn from_size_alignment(size: usize, alignment: Alignment) -> Result<Self, LayoutError> {
        // TODO(verification): The modeled Layout domain requires exact size
        // divisibility. Under that precondition upstream's rounded-size check
        // reduces to the isize bound; general layouts need a weaker invariant.
        if size <= isize::MAX as usize {
            Ok(unsafe { Self::from_size_alignment_unchecked(size, alignment) })
        } else {
            Err(LayoutError)
        }
    }

    #[rr::requires("Hsize_in_range": "size ∈ isize")]
    #[rr::requires("Hsize_aligned": "Z.divide (alignment_to_align alignment) size")]
    #[rr::returns("mk_rust_layout (Z.to_nat size) alignment")]
    pub const unsafe fn from_size_alignment_unchecked(size: usize, alignment: Alignment) -> Self {
        // TODO(verification): As for from_size_align_unchecked, the specification
        // carries the unsafe preconditions rather than upstream's UB-check macro.
        Self { size, align: alignment }
    }

    #[rr::requires("is_power_of_two (Z.to_nat align)")]
    #[rr::requires("size ∈ isize")]
    #[rr::requires("Z.divide align size")]
    #[rr::returns("Ok (mk_rust_layout (Z.to_nat size) (alignment_of_align align))")]
    pub const fn from_size_align(size: usize, align: usize) -> Result<Self, LayoutError> {
        Ok(unsafe {Self::from_size_align_unchecked(size, align) })
        /*
        if Layout::is_size_align_valid(size, align) {
            // SAFETY: Layout::is_size_align_valid checks the preconditions for this call.
            unsafe { Ok(Layout { size, align: Alignment::new_unchecked(align) }) }
        } else {
            Err(LayoutError)
        }
        */
    }

    #[rr::requires("is_power_of_two (Z.to_nat align)")]
    #[rr::requires("size ∈ isize")]
    #[rr::requires("Z.divide align size")]
    #[rr::returns("mk_rust_layout (Z.to_nat size) (alignment_of_align align)")]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Self {
        // SAFETY: the caller is required to uphold the preconditions.
        unsafe { Layout { size, align: Alignment::new_unchecked(align) } }
    }


    /*
    const fn is_size_align_valid(size: usize, align: usize) -> bool {
        let Some(align) = Alignment::new(align) else { return false };
        if size > Self::max_size_for_align(align) {
            return false;
        }
        true
    }

    const fn max_size_for_align(align: Alignment) -> usize {
        // (power-of-two implies align != 0.)
        // Rounded up size is:
        //   size_rounded_up = (size + align - 1) & !(align - 1);
        //
        // We know from above that align != 0. If adding (align - 1)
        // does not overflow, then rounding up will be fine.
        //

        // Conversely, &-masking with !(align - 1) will subtract off
        // only low-order-bits. Thus if overflow occurs with the sum,
        // the &-mask cannot subtract enough to undo that overflow.
        //
        // Above implies that checking for summation overflow is both
        // necessary and sufficient.

        // SAFETY: the maximum possible alignment is `isize::MAX + 1`,
        // so the subtraction cannot overflow.
        unsafe { unchecked_sub(isize::MAX as usize + 1, align.as_usize()) }
    }
    */

    #[rr::returns("mk_rust_layout (ly_size {ly_of T}) (alignment_of_align (ly_align {ly_of T}))")]
    pub const fn new<T>() -> Self {
        unsafe { Self::from_size_align_unchecked(mem::size_of::<T>(), mem::align_of::<T>()) }
        //<T as SizedTypeProperties>::LAYOUT
    }
}
