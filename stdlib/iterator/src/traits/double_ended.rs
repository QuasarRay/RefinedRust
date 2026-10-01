#![rr::import("rrstd.iterator.theories", "double_ended")]
use crate::traits::iterator::Iterator;

use std::ops::{ControlFlow, Try};
use std::cmp::{self, Ordering};

#[rr::export_as(core::iter::DoubleEndedIterator)]
#[rr::external_attrs("NextBack")]
pub trait DoubleEndedIterator: Iterator {
    /// Removes and returns an element from the end of the iterator.
    ///
    /// Returns `None` when there are no more elements.
    ///
    /// The [trait-level] docs contain more details.
    ///
    /// [trait-level]: DoubleEndedIterator
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let numbers = vec![1, 2, 3, 4, 5, 6];
    ///
    /// let mut iter = numbers.iter();
    ///
    /// assert_eq!(Some(&1), iter.next());
    /// assert_eq!(Some(&6), iter.next_back());
    /// assert_eq!(Some(&5), iter.next_back());
    /// assert_eq!(Some(&2), iter.next());
    /// assert_eq!(Some(&3), iter.next());
    /// assert_eq!(Some(&4), iter.next());
    /// assert_eq!(None, iter.next());
    /// assert_eq!(None, iter.next_back());
    /// ```
    ///
    /// # Remarks
    ///
    /// The elements yielded by `DoubleEndedIterator`'s methods may differ from
    /// the ones yielded by [`Iterator`]'s methods:
    ///
    /// ```
    /// let vec = vec![(1, 'a'), (1, 'b'), (1, 'c'), (2, 'a'), (2, 'b')];
    /// let uniq_by_fst_comp = || {
    ///     let mut seen = std::collections::HashSet::new();
    ///     vec.iter().copied().filter(move |x| seen.insert(x.0))
    /// };
    ///
    /// assert_eq!(uniq_by_fst_comp().last(), Some((2, 'a')));
    /// assert_eq!(uniq_by_fst_comp().next_back(), Some((2, 'b')));
    ///
    /// assert_eq!(
    ///     uniq_by_fst_comp().fold(vec![], |mut v, x| {v.push(x); v}),
    ///     vec![(1, 'a'), (2, 'a')]
    /// );
    /// assert_eq!(
    ///     uniq_by_fst_comp().rfold(vec![], |mut v, x| {v.push(x); v}),
    ///     vec![(2, 'b'), (1, 'c')]
    /// );
    /// ```
    #[rr::params("p")]
    #[rr::requires(#iris "{Self::Inv} π p self.cur")]
    #[rr::exists("new_it_state" : "{xt_of Self}")]
    #[rr::observe("self.ghost": "$# new_it_state")]
    #[rr::ensures(#iris "{NextBack} π p self.cur ret new_it_state")]
    #[rr::ensures(#iris "{Self::Inv} π p new_it_state")]
    fn next_back(&mut self) -> Option<Self::Item>;

    #[rr::verify]
    #[rr::params("p", "ClosInv" : "thread_id → result {xt_of B} _ → list {xt_of Self::Item} → {xt_of Self} → {xt_of F} → iProp Σ")]
    #[rr::requires(#iris "{Self::Inv} π p self.cur")]
    #[rr::requires(#iris "ClosInv π (Ok init) [] self.cur f")]
    #[rr::requires(#iris "□ (∀ seq acc it_state it_state' clos_state e,
        IteratorNextBackFusedTrans traits_double_ended_DoubleEndedIterator_Self_spec_attrs π p self.cur seq it_state -∗
        {NextBack} π p it_state (Some e) it_state' -∗
        ClosInv π (Ok acc) seq it_state clos_state -∗
        ∃ pclos, {F::Pre} π pclos clos_state *[acc; e] ∗
        {NextBack} π p it_state (Some e) it_state' ∗
        IteratorNextBackFusedTrans traits_double_ended_DoubleEndedIterator_Self_spec_attrs π p self.cur seq it_state ∗
        (∀ b clos_state', {F::PostMut} π pclos clos_state *[acc; e] clos_state' b -∗
            ClosInv π ({R::BranchFn} b) (seq ++ [e]) it_state' clos_state' ∗ True))")]
    #[rr::requires("closure_may_unwind {F::UnwindCondition} → False")]
    #[rr::exists("seq", "s2", "s2'", "clos_state'")]
    #[rr::observe("self.ghost": "$# s2'")]
    #[rr::ensures(#iris "{Self::Inv} π p s2'")]
    #[rr::ensures(#iris "IteratorNextBackFusedTrans traits_double_ended_DoubleEndedIterator_Self_spec_attrs π p self.cur seq s2")]
    #[rr::ensures(#iris "ClosInv π ({R::BranchFn} ret) seq s2 clos_state'")]
    #[rr::ensures(#iris "if_iOk ({R::BranchFn} ret) (λ ret, {NextBack} π p s2 None s2' ∗ True)")]
    #[rr::ensures(#iris "if_iErr ({R::BranchFn} ret) (λ err, ⌜s2 = s2'⌝ ∗ True)")]
    #[rr::ensures(#iris "ty_ghost_drop {F} π ($# clos_state')")]
    #[rr::may_unwind_if("{F::DropGlueUnwind}")]
    fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        let mut accum = init;
        while let Some(x) = self.next_back() {
            #[rr::params("γ", "init_state")]
            #[rr::inv_vars("self", "accum", "f")]
            #[rr::invariant("self.ghost = γ")]
            #[rr::exists("seq")]
            #[rr::invariant(#iris "IteratorNextBackFusedTrans traits_double_ended_DoubleEndedIterator_Self_spec_attrs π p init_state seq self.cur")]
            #[rr::invariant(#iris "{Self::Inv} π p self.cur")]
            #[rr::invariant(#iris "ClosInv π (Ok accum) seq self.cur f")]
            #[rr::ignore] || {};
            accum = f(accum, x)?;
        }
        try { accum }
    }
}
