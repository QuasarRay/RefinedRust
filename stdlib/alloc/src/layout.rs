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
        let new_size = self.size_rounded_up_to_custom_alignment(self.align);
        unsafe { Layout::from_size_alignment_unchecked(new_size, self.alignment()) }
    }

    // TODO(verification): Keep the existing aligned-size domain in the helper
    // contract. The upstream computation is unchanged; padding on this domain
    // is zero, including when called by pad_to_align.
    #[rr::requires("Hsize_aligned": "Z.divide (alignment_to_align alignment) (Z.of_nat self.(layout_sz))")]
    #[rr::returns("Z.of_nat self.(layout_sz)")]
    const fn size_rounded_up_to_custom_alignment(&self, alignment: Alignment) -> usize {
        unsafe {
            let align_m1 = alignment.as_usize().unchecked_sub(1);
            self.size.unchecked_add(align_m1) & !align_m1
        }
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
        if Self::is_size_alignment_valid(size, alignment) {
            Ok(Layout { size, align: alignment })
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
        if Layout::is_size_align_valid(size, align) {
            // SAFETY: Layout::is_size_align_valid checks the preconditions for this call.
            // TODO(verification): Use the modeled Alignment constructor in place
            // of upstream's transmute from a validated power-of-two integer.
            unsafe { Ok(Layout { size, align: Alignment::new_unchecked(align) }) }
        } else {
            Err(LayoutError)
        }
    }

    #[rr::requires("is_power_of_two (Z.to_nat align)")]
    #[rr::requires("size ∈ isize")]
    #[rr::requires("Z.divide align size")]
    #[rr::returns("mk_rust_layout (Z.to_nat size) (alignment_of_align align)")]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Self {
        // SAFETY: the caller is required to uphold the preconditions.
        unsafe { Layout { size, align: Alignment::new_unchecked(align) } }
    }


    #[rr::requires("is_power_of_two (Z.to_nat align)")]
    #[rr::returns("bool_decide (size ≤ MaxInt ISize + 1 - align)")]
    const fn is_size_align_valid(size: usize, align: usize) -> bool {
        let Some(alignment) = Alignment::new(align) else { return false };
        Self::is_size_alignment_valid(size, alignment)
    }

    #[rr::returns("bool_decide (size ≤ MaxInt ISize + 1 - alignment_to_align alignment)")]
    const fn is_size_alignment_valid(size: usize, alignment: Alignment) -> bool {
        size <= Self::max_size_for_alignment(alignment)
    }

    #[rr::returns("MaxInt ISize + 1 - alignment_to_align alignment")]
    const fn max_size_for_alignment(alignment: Alignment) -> usize {
        unsafe { (isize::MAX as usize + 1).unchecked_sub(alignment.as_usize()) }
    }

    #[rr::returns("mk_rust_layout (ly_size {ly_of T}) (alignment_of_align (ly_align {ly_of T}))")]
    pub const fn new<T>() -> Self {
        unsafe { Self::from_size_align_unchecked(mem::size_of::<T>(), mem::align_of::<T>()) }
        //<T as SizedTypeProperties>::LAYOUT
    }
}
