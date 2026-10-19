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
    #[rr::pattern("ReserveAllocError" $ "layout")]
    #[rr::refinement("layout")]
    #[rr::refined_by("layout" : "rust_layout")]
    AllocError {
        #[rr::field("#layout")]
        layout: Layout,
        #[rr::field("#tt")]
        non_exhaustive: (),
    },
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

// TODO(verification): Use an ordinary Clone impl until const trait calls are
// supported by the model; retain upstream's field-by-field implementation.
impl Clone for TryReserveErrorKind {
    #[rr::default_spec]
    fn clone(&self) -> Self {
        match self {
            Self::CapacityOverflow => Self::CapacityOverflow,
            Self::AllocError { layout, non_exhaustive: () } => {
                Self::AllocError { layout: *layout, non_exhaustive: () }
            }
        }
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
