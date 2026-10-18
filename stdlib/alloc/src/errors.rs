#![rr::import("rrstd.alloc.theories", "errors")]

use crate::layout::{Layout, LayoutError};

#[rr::export_as(core::alloc::AllocError)]
#[rr::refined_by("()" : "unit")]
#[derive(Copy, Clone)]
pub struct AllocError;

#[rr::export_as(alloc::collections::TryReserveError)]
#[rr::refined_by("kind" : "reserve_error")]
#[derive(Clone)]
pub struct TryReserveError {
    #[rr::field("#kind")]
    kind: TryReserveErrorKind,
}

#[rr::export_as(alloc::collections::TryReserveErrorKind)]
#[rr::refined_by("reserve_error")]
pub enum TryReserveErrorKind {
    #[rr::pattern("ReserveCapacityOverflow")]
    #[rr::refinement("*[]")]
    CapacityOverflow,
    #[rr::pattern("ReserveAllocError" $ "layout", "extra")]
    #[rr::refinement("*[layout; extra]")]
    AllocError { layout: Layout, non_exhaustive: () },
}

#[rr::export_as(alloc::collections::TryReserveError)]
impl TryReserveError {
    #[rr::returns("self")]
    pub fn kind(&self) -> TryReserveErrorKind {
        // TODO(verification): Omit upstream's const qualifier until const Clone
        // trait calls are supported; the returned error kind is unchanged.
        self.kind.clone()
    }
}

// TODO(verification): This local Copy implementation permits cloning the whole
// enum instead of projecting invariant-bearing fields through shared ownership.
// All payloads are Copy (Layout and unit). Upstream does not expose Copy for this
// enum, so omit this implementation from the exported verification interface.
#[rr::skip]
impl Copy for TryReserveErrorKind {}

// TODO(verification): Replace upstream's manual const Clone with an ordinary
// whole-value copy, preserving both payload refinements.
impl Clone for TryReserveErrorKind {
    #[rr::default_spec]
    fn clone(&self) -> Self {
        *self
    }
}

// TODO(verification): Use ordinary From implementations instead of the
// pinned nightly's const implementations.
#[rr::instantiate("FromFn" := "id")]
impl From<TryReserveErrorKind> for TryReserveError {
    #[rr::default_spec]
    fn from(kind: TryReserveErrorKind) -> Self {
        Self { kind }
    }
}

#[rr::instantiate("FromFn" := "λ _, ReserveCapacityOverflow")]
impl From<LayoutError> for TryReserveErrorKind {
    #[rr::default_spec]
    fn from(_: LayoutError) -> Self {
        Self::CapacityOverflow
    }
}
