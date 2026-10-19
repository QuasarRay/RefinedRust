#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(core_intrinsics)]
#![allow(internal_features)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.num")]
#![rr::include("option")]

use paste::paste;

macro_rules! u_abs_diff_impl {
    ($t:ty) => {
        paste! {
            #[rr::export_as(#method core::num::$t::abs_diff)]
            #[rr::returns("Z.abs (x - other)")]
            pub fn [<$t _abs_diff>](x: $t, other: $t) -> $t {
                if x < other {
                    other - x
                } else {
                    x - other
                }
            }
        }
    }
}

u_abs_diff_impl!(u8);
u_abs_diff_impl!(u16);
u_abs_diff_impl!(u32);
u_abs_diff_impl!(u64);
u_abs_diff_impl!(u128);
u_abs_diff_impl!(usize);


macro_rules! i_abs_diff_impl {
    ($t:ty, $ut:ty) => {
        paste! {
            #[rr::only_spec]
            #[rr::export_as(#method core::num::$t::abs_diff)]
            #[rr::returns("Z.abs (x - other)")]
            pub fn [<$t _abs_diff>](x: $t, other: $t) -> $ut {
                if x < other {
                    // Converting a non-negative x from signed to unsigned by using
                    // `x as U` is left unchanged, but a negative x is converted
                    // to value x + 2^N. Thus if `s` and `o` are binary variables
                    // respectively indicating whether `self` and `other` are
                    // negative, we are computing the mathematical value:
                    //
                    //    (other + o*2^N) - (self + s*2^N)    mod  2^N
                    //    other - self + (o-s)*2^N            mod  2^N
                    //    other - self                        mod  2^N
                    //
                    // Finally, taking the mod 2^N of the mathematical value of
                    // `other - self` does not change it as it already is
                    // in the range [0, 2^N).
                    (other as $ut).wrapping_sub(x as $ut)
                } else {
                    (x as $ut).wrapping_sub(other as $ut)
                }
            }

            #[rr::export_as(#method core::num::$t::is_positive)]
            #[rr::returns("bool_decide (x > 0)")]
            pub fn [<$t _is_positive>](x: $t) -> bool { x > 0 }

            #[rr::export_as(#method core::num::$t::is_negative)]
            #[rr::returns("bool_decide (x < 0)")]
            pub fn [<$t _is_negative>](x: $t) -> bool { x < 0 }

        }
    }
}

i_abs_diff_impl!(i8, u8);
i_abs_diff_impl!(i16, u16);
i_abs_diff_impl!(i32, u32);
i_abs_diff_impl!(i64, u64);
i_abs_diff_impl!(i128, u128);
i_abs_diff_impl!(isize, usize);

macro_rules! i_abs_impl {
    ($t:ty, $x:expr) => {
        paste! {
            #[rr::export_as(#method core::num::$t::abs)]
            #[rr::requires($x)]
            #[rr::returns("Z.abs x")]
            pub fn [<$t _abs>](x: $t) -> $t {
                // Note that the #[rustc_inherit_overflow_checks] and #[inline]
                // above mean that the overflow semantics of the subtraction
                // depend on the crate we're being called from.
                if x.is_negative() {
                    -x
                } else {
                    x
                }
            }
        }
    }
}
// TOOD: requires attribute parser needs to support it.
//i_abs_impl!(i8, "x <> MinInt i8");


macro_rules! u_is_power_of_two_impl {
    ($t:ty) => {
        paste! {
            #[rr::only_spec]
            #[rr::export_as(#method core::num::$t::is_power_of_two)]
            #[rr::returns("bool_decide (is_power_of_two (Z.to_nat x))")]
            pub fn [<$t _is_power_of_two>](x: $t) -> bool {
                x.count_ones() == 1
            }
        }
    }
}

// Only for unsized types
u_is_power_of_two_impl!(u8);
u_is_power_of_two_impl!(u16);
u_is_power_of_two_impl!(u32);
u_is_power_of_two_impl!(u64);
u_is_power_of_two_impl!(u128);
u_is_power_of_two_impl!(usize);


macro_rules! u_checked_sub_impl {
    ($t:ty) => {
        paste! {
            #[rr::export_as(#method core::num::$t::checked_sub)]
            #[rr::returns("if bool_decide (x >= rhs) then Some (x - rhs)%Z else None")]
            pub fn [<$t _checked_sub>](x: $t, rhs: $t) -> Option<$t> {
                // Per PR#103299, there's no advantage to the `overflowing` intrinsic
                // for *unsigned* subtraction and we just emit the manual check anyway.
                // Thus, rather than using `overflowing_sub` that produces a wrapping
                // subtraction, check it ourself so we can use an unchecked one.

                if x < rhs {
                    None
                } else {
                    // SAFETY: just checked this can't overflow
                    Some(unsafe { x.unchecked_sub(rhs) })
                }
            }

            #[rr::only_spec]
            #[rr::export_as(#method core::num::$t::unchecked_sub)]
            #[rr::requires("(rhs ≤ x)%Z")]
            #[rr::returns("(x - rhs)%Z")]
            pub unsafe fn [<$t _unchecked_sub>](x : $t, rhs: $t) -> $t {
                // SAFETY: this is guaranteed to be safe by the caller.
                //unsafe {
                    //intrinsics::unchecked_sub(x, rhs)
                //}
                unimplemented!();
            }

            #[rr::only_spec]
            #[rr::export_as(#method core::num::$t::saturating_sub)]
            #[rr::returns("Z.max 0%Z (x - rhs)%Z")]
            pub fn [<$t _saturating_sub>](x: $t, rhs: $t) -> $t {
                //intrinsics::saturating_sub(self, rhs)
                //unimplemented!();
                if x <= rhs {
                    0
                } else {
                    unsafe { x.unchecked_sub(rhs) }
                }
            }
        }
    }
}

// Only for unsized types
u_checked_sub_impl!(u8);
u_checked_sub_impl!(u16);
u_checked_sub_impl!(u32);
u_checked_sub_impl!(u64);
u_checked_sub_impl!(u128);
u_checked_sub_impl!(usize);

macro_rules! u_checked_add_impl {
    ($t:ty, $spec:tt) => {
        paste! {
            #[rr::export_as(#method core::num::$t::checked_add)]
            #[rr::returns($spec)]
            pub fn [<$t _checked_add>](x: $t, rhs: $t) -> Option<$t> {
                if core::intrinsics::add_with_overflow(x, rhs).1 {
                    None
                } else {
                    Some(unsafe { core::intrinsics::unchecked_add(x, rhs) })
                }
            }
        }
    }
}

u_checked_add_impl!(u8, "if bool_decide (x + rhs ≤ MaxInt u8) then Some (x + rhs)%Z else None");
u_checked_add_impl!(u16, "if bool_decide (x + rhs ≤ MaxInt u16) then Some (x + rhs)%Z else None");
u_checked_add_impl!(u32, "if bool_decide (x + rhs ≤ MaxInt u32) then Some (x + rhs)%Z else None");
u_checked_add_impl!(u64, "if bool_decide (x + rhs ≤ MaxInt u64) then Some (x + rhs)%Z else None");
u_checked_add_impl!(u128, "if bool_decide (x + rhs ≤ MaxInt u128) then Some (x + rhs)%Z else None");
u_checked_add_impl!(usize, "if bool_decide (x + rhs ≤ MaxInt usize) then Some (x + rhs)%Z else None");

macro_rules! u_checked_mul_impl {
    ($t:ty, $spec:tt, $range:tt) => {
        paste! {
            #[rr::export_as(#method core::num::$t::checked_mul)]
            #[rr::returns($spec)]
            pub fn [<$t _checked_mul>](x: $t, rhs: $t) -> Option<$t> {
                let (value, overflow) = core::intrinsics::mul_with_overflow(x, rhs);
                if overflow {
                    None
                } else {
                    Some(value)
                }
            }

            #[rr::export_as(#method core::num::$t::unchecked_mul)]
            #[rr::requires("Hproduct_in_range": $range)]
            #[rr::returns("(x * rhs)%Z")]
            pub unsafe fn [<$t _unchecked_mul>](x: $t, rhs: $t) -> $t {
                unsafe { core::intrinsics::unchecked_mul(x, rhs) }
            }
        }
    }
}

u_checked_mul_impl!(u8, "if bool_decide (x * rhs ≤ MaxInt u8) then Some (x * rhs)%Z else None", "x * rhs ∈ u8");
u_checked_mul_impl!(u16, "if bool_decide (x * rhs ≤ MaxInt u16) then Some (x * rhs)%Z else None", "x * rhs ∈ u16");
u_checked_mul_impl!(u32, "if bool_decide (x * rhs ≤ MaxInt u32) then Some (x * rhs)%Z else None", "x * rhs ∈ u32");
u_checked_mul_impl!(u64, "if bool_decide (x * rhs ≤ MaxInt u64) then Some (x * rhs)%Z else None", "x * rhs ∈ u64");
u_checked_mul_impl!(u128, "if bool_decide (x * rhs ≤ MaxInt u128) then Some (x * rhs)%Z else None", "x * rhs ∈ u128");
u_checked_mul_impl!(usize, "if bool_decide (x * rhs ≤ MaxInt usize) then Some (x * rhs)%Z else None", "x * rhs ∈ usize");

macro_rules! u_unchecked_add_impl {
    ($t:ty, $range:tt) => {
        paste! {
            #[rr::export_as(#method core::num::$t::unchecked_add)]
            #[rr::requires("Hsum_in_range": $range)]
            #[rr::returns("(x + rhs)%Z")]
            pub unsafe fn [<$t _unchecked_add>](x: $t, rhs: $t) -> $t {
                unsafe { core::intrinsics::unchecked_add(x, rhs) }
            }
        }
    }
}

u_unchecked_add_impl!(u8, "x + rhs ∈ u8");
u_unchecked_add_impl!(u16, "x + rhs ∈ u16");
u_unchecked_add_impl!(u32, "x + rhs ∈ u32");
u_unchecked_add_impl!(u64, "x + rhs ∈ u64");
u_unchecked_add_impl!(u128, "x + rhs ∈ u128");
u_unchecked_add_impl!(usize, "x + rhs ∈ usize");

macro_rules! u_wrapping_sub_impl {
    ($t:ty, $spec:tt) => {
        paste! {
            #[rr::export_as(#method core::num::$t::wrapping_sub)]
            #[rr::returns($spec)]
            pub fn [<$t _wrapping_sub>](x: $t, rhs: $t) -> $t {
                core::intrinsics::wrapping_sub(x, rhs)
            }
        }
    }
}

u_wrapping_sub_impl!(u8, "wrap_to_it (x - rhs) u8");
u_wrapping_sub_impl!(u16, "wrap_to_it (x - rhs) u16");
u_wrapping_sub_impl!(u32, "wrap_to_it (x - rhs) u32");
u_wrapping_sub_impl!(u64, "wrap_to_it (x - rhs) u64");
u_wrapping_sub_impl!(u128, "wrap_to_it (x - rhs) u128");
u_wrapping_sub_impl!(usize, "wrap_to_it (x - rhs) usize");
