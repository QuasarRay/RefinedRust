#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]

#![feature(allocator_api)]
#![allow(internal_features)]
#![feature(ptr_internals)]
#![feature(sized_type_properties)]

#![rr::import("rrstd.linkedlist.theories", "linkedlist")]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.linkedlist")]

#![rr::include("alloc")]
#![rr::include("iterator")]
#![rr::include("range")]
#![rr::include("option")]
#![rr::include("rr_internal")]
#![rr::include("closures")]
#![rr::include("cmp")]
#![rr::include("index")]
#![rr::include("ptr_advanced")]
#![rr::include("clone")]
#![rr::include("controlflow")]
#![rr::include("sized")]
#![rr::include("boxed")]
#![rr::include("ptr")]
#![rr::include("num")]
#![rr::include("mem")]

use std::alloc::{Allocator, AllocatorClone, Global};
use std::marker::PhantomData;
use core::ptr::{Unique, NonNull};
use std::ptr;
use std::mem;
use std::alloc::Layout;
use std::mem::SizedTypeProperties;


#[rr::refined_by("x" : "LinkedListRT {rt_of T} {rt_of A}")]
#[rr::depends_on(Node)]
#[rr::inv("Hlen" : "length x.(linked_list_locs) = length x.(linked_list_elems)")]
#[rr::inv("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) x.(linked_list_locs)")]
#[rr::inv("Hbound" : "length x.(linked_list_elems) ≤ MaxInt usize")]
// TODO: this shouldn't wrap everything
#[rr::inv(#iris "LL
    (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
    (λ alloc l, {A::FreeablePerm} alloc l (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
    x.(linked_list_elems) x.(linked_list_locs) x.(linked_list_alloc)")]
// TODO
//#[rr::ghost_drop(#iris "[∗ list] elem ∈ x.(linked_list_elems), ∃ x, place_rfn_interp_owned elem x ∗ ty_ghost_drop {T} π x")]
#[rr::ghost_drop(#iris "True")]
#[rr::ty_lfts("ty_lfts {T} ++ ty_lfts {A}")]
#[rr::ty_wf_E("ty_wf_E {T} ++ ty_wf_E {A}")]
// dropping may unwind only if dropping T or A may unwind
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind} ∨ {A::DropGlueUnwind}")]
pub struct LinkedList<
    T,
    A: Allocator = Global,
> {
    #[rr::field("#(<#>@{{option}} (head x.(linked_list_locs)))")]
    head: Option<NonNull<Node<T>>>,
    #[rr::field("#(<#>@{{option}} (last x.(linked_list_locs)))")]
    tail: Option<NonNull<Node<T>>>,
    #[rr::field("#(Z.of_nat (length x.(linked_list_elems)))")]
    len: usize,
    #[rr::field("#($# x.(linked_list_alloc))")]
    alloc: A,
    #[rr::field("#(tt)")]
    marker: PhantomData<Box<Node<T>, A>>,
}

#[rr::refined_by("(next, prev, element)" : "(option loc * option loc * place_rfn {rt_of T})%type")]
#[rr::ty_lfts("ty_lfts {T}")]
#[rr::ty_wf_E("ty_wf_E {T}")]
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
struct Node<T> {
    #[rr::field("#(<#>@{{option}} next)")]
    next: Option<NonNull<Node<T>>>,
    #[rr::field("#(<#>@{{option}} prev)")]
    prev: Option<NonNull<Node<T>>>,
    #[rr::field("element")]
    element: T,
}

#[rr::refined_by("xs" : "listRT (place_rfnRT {rt_of T})")]
#[rr::depends_on(Node)]
#[rr::exists("all_elems" : "list (place_rfn {rt_of T})")]
#[rr::exists("locs" : "list loc")]
#[rr::exists("idx" : "nat")]
#[rr::exists("back_idx" : "nat")]
#[rr::inv("Hsuffix" : "xs = drop idx (take back_idx all_elems)")]
#[rr::inv("Hidx" : "idx ≤ back_idx")]
#[rr::inv("Hback" : "back_idx ≤ length all_elems")]
#[rr::inv("Hlen" : "length locs = length all_elems")]
#[rr::inv("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
#[rr::inv("Hbound" : "length all_elems ≤ MaxInt usize")]
#[rr::inv(#iris "LL
    (λ l next prev elem, guarded false (l ◁ₗ[π, Shared {'a}] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
    (λ _ _, True) all_elems locs tt")]
#[rr::ty_lfts("ty_lfts {T}")]
#[rr::ty_wf_E("ty_wf_E {T}")]
pub struct Iter<'a, T: 'a> {
    #[rr::field("#(<#>@{{option}} (locs !! idx))")]
    head: Option<NonNull<Node<T>>>,
    #[rr::field("#(<#>@{{option}} (last (take back_idx locs)))")]
    tail: Option<NonNull<Node<T>>>,
    #[rr::field("#(Z.of_nat (length xs))")]
    len: usize,
    #[rr::field("#(tt)")]
    marker: PhantomData<&'a Node<T>>,
}

// Raw iterator state: backing-node ownership is passed explicitly by the
// concrete next/next_back specifications, rather than owned by this type.
#[rr::refined_by("(head, tail, len)" : "(option loc * option loc * Z)%type")]
#[rr::ghost_drop("True")]
#[rr::ty_lfts("ty_lfts {T} ++ [ulft_a]")]
#[rr::ty_wf_E("ty_wf_E {T} ++ ty_outlives_E {T} ulft_a")]
pub struct IterMut<'a, T: 'a> {
    #[rr::field("#(<#>@{{option}} head)")]
    head: Option<NonNull<Node<T>>>,
    #[rr::field("#(<#>@{{option}} tail)")]
    tail: Option<NonNull<Node<T>>>,
    #[rr::field("#len")]
    len: usize,
    #[rr::field("#tt")]
    marker: PhantomData<&'a mut Node<T>>,
}

#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind} ∨ {A::DropGlueUnwind}")]
pub struct IntoIter<
    T,
    A: Allocator = Global,
> {
    list: LinkedList<T, A>,
}

impl<T> Node<T> {
    #[rr::returns("(None, None, element)")]
    fn new(element: T) -> Self {
        Node { next: None, prev: None, element }
    }

    #[rr::params("next", "prev", "element", "a")]
    #[rr::args("((next, prev, element), a)")]
    #[rr::returns("element")]
    #[rr::may_unwind_if("{A::DropGlueUnwind}")]
    fn into_element<A: Allocator>(self: Box<Self, A>) -> T {
        self.element
    }
}

impl<T> LinkedList<T> {
    #[rr::returns("mk_linked_list_x [] [] tt")]
    pub const fn new() -> Self {
        LinkedList { head: None, tail: None, len: 0, alloc: Global, marker: PhantomData }
    }
}

// private methods
impl<T, A: Allocator> LinkedList<T, A> {
    /// Adds the given node to the front of the list.
    ///
    /// # Safety
    /// `node` must point to a valid node in the list's allocator.
    /// This method takes ownership of the node, so the pointer should not be used again.
    #[inline]
    #[rr::raw_mut_self]
    #[rr::params("l", "node", "locs", "elems", "alloc", "element" : "{xt_of T}")]
    #[rr::args("l" @ "alias_ref_t", "node")]
    #[rr::requires(#type "l" : "-[
        #(<#>@{{option}} (head locs));
        #(<#>@{{option}} (last locs));
        #(Z.of_nat (length elems));
        #($# alloc);
        #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::requires("Hlen" : "length locs = length elems")]
    #[rr::requires("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires("Hbound" : "length elems < MaxInt usize")]
    #[rr::requires(#iris "LL
        (λ node_loc next prev elem, guarded true (node_loc ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc node_loc, {A::FreeablePerm} alloc node_loc (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        (<#> <$#> elems) locs alloc")]
    #[rr::requires(#type "node" : "(None, None, # $#element)" @ "Node_inv_t {rt_of T} -[] -[{T}]")]
    #[rr::requires(#iris "{A::FreeablePerm} alloc node (ly_size (use_struct_layout_alg' (Node_sls {st_of T})))")]
    #[rr::requires("node.(loc_a) ≠ 0")]
    #[rr::ensures(#type "l" : "-[
        #(<#>@{{option}} (head (node :: locs)));
        #(<#>@{{option}} (last (node :: locs)));
        #(Z.of_nat (length (element :: elems)));
        #($# alloc);
        #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::ensures(#iris "LL
        (λ node_loc next prev elem, guarded true (node_loc ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc node_loc, {A::FreeablePerm} alloc node_loc (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        (<#> <$#> (element :: elems)) (node :: locs) alloc")]
    #[rr::ensures("length (node :: locs) = length (element :: elems)")]
    #[rr::ensures("Forall (λ l, l.(loc_a) ≠ 0) (node :: locs)")]
    #[rr::ensures("length (element :: elems) ≤ MaxInt usize")]
    unsafe fn push_front_node(&mut self, node: NonNull<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            (*node.as_ptr()).next = self.head;
            (*node.as_ptr()).prev = None;
            let node = Some(node);

            match self.head {
                None => self.tail = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the front of the list.
    #[inline]
    #[rr::observe("self.ghost": "mk_linked_list_x (tail ($# self.cur.(linked_list_elems))) (tail self.cur.(linked_list_locs)) self.cur.(linked_list_alloc)")]
    #[rr::ensures("if_Some ret (λ x, head self.cur.(linked_list_elems) = Some x.1.2 ∧ x.1.1.2 = None ∧ x.2 = self.cur.(linked_list_alloc))")]
    #[rr::ensures("if_None ret (self.cur.(linked_list_elems) = [])")]
    fn pop_front_node(&mut self) -> Option<Box<Node<T>, &A>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        // TODO: Restore Option::map once closure trait attributes can refer to the
        // enclosing semantic type for T. An explicit branch keeps T_ty in scope.
        if let Some(node) = self.head {
            Some(unsafe {
            let node = Box::from_raw_in(node.as_ptr(), &self.alloc);
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            node
            })
        } else {
            None
        }
    }

    /// Adds the given node to the back of the list.
    ///
    /// # Safety
    /// `node` must point to a valid node in the list's allocator.
    /// This method takes ownership of the node, so the pointer should not be used again.
    #[inline]
    #[rr::raw_mut_self]
    #[rr::params("l", "node", "locs", "elems", "alloc", "element" : "{xt_of T}")]
    #[rr::args("l" @ "alias_ref_t", "node")]
    #[rr::requires(#type "l" : "-[
        #(<#>@{{option}} (head locs));
        #(<#>@{{option}} (last locs));
        #(Z.of_nat (length elems));
        #($# alloc);
        #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::requires("Hlen" : "length locs = length elems")]
    #[rr::requires("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires("Hbound" : "length elems < MaxInt usize")]
    #[rr::requires(#iris "LL
        (λ node_loc next prev elem, guarded true (node_loc ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc node_loc, {A::FreeablePerm} alloc node_loc (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        (<#> <$#> elems) locs alloc")]
    #[rr::requires(#type "node" : "(None, None, # $#element)" @ "Node_inv_t {rt_of T} -[] -[{T}]")]
    #[rr::requires(#iris "{A::FreeablePerm} alloc node (ly_size (use_struct_layout_alg' (Node_sls {st_of T})))")]
    #[rr::requires("Hnode_nonnull" : "node.(loc_a) ≠ 0")]
    #[rr::ensures(#type "l" : "-[
        #(<#>@{{option}} (head (locs ++ [node])));
        #(<#>@{{option}} (last (locs ++ [node])));
        #(Z.of_nat (length (elems ++ [element])));
        #($# alloc);
        #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::ensures(#iris "LL
        (λ node_loc next prev elem, guarded true (node_loc ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc node_loc, {A::FreeablePerm} alloc node_loc (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        (<#> <$#> (elems ++ [element])) (locs ++ [node]) alloc")]
    #[rr::ensures("length (locs ++ [node]) = length (elems ++ [element])")]
    #[rr::ensures("Forall (λ l, l.(loc_a) ≠ 0) (locs ++ [node])")]
    #[rr::ensures("length (elems ++ [element]) ≤ MaxInt usize")]
    unsafe fn push_back_node(&mut self, node: NonNull<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            (*node.as_ptr()).next = None;
            (*node.as_ptr()).prev = self.tail;
            let node = Some(node);

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the back of the list.
    #[inline]
    #[rr::observe("self.ghost": "mk_linked_list_x (removelast ($# self.cur.(linked_list_elems))) (removelast self.cur.(linked_list_locs)) self.cur.(linked_list_alloc)")]
    #[rr::ensures("if_Some ret (λ x, last self.cur.(linked_list_elems) = Some x.1.2 ∧ x.1.1.1 = None ∧ x.2 = self.cur.(linked_list_alloc))")]
    #[rr::ensures("if_None ret (self.cur.(linked_list_elems) = [])")]
    fn pop_back_node(&mut self) -> Option<Box<Node<T>, &A>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        // TODO: Restore Option::map once closure trait attributes can refer to the
        // enclosing semantic type for T. An explicit branch keeps T_ty in scope.
        if let Some(node) = self.tail {
            Some(unsafe {
            let node = Box::from_raw_in(node.as_ptr(), &self.alloc);
            self.tail = node.prev;

            match self.tail {
                None => self.head = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = None,
            }

            self.len -= 1;
            node
            })
        } else {
            None
        }
    }

    /// Unlinks the specified node from the current list.
    ///
    /// Warning: this will not check that the provided node belongs to the current list.
    ///
    /// This method takes care not to create mutable references to `element`, to
    /// maintain validity of aliasing pointers.
    #[inline]
    #[rr::raw_mut_self]
    #[rr::params("l", "node", "locs", "elems", "i", "alloc")]
    #[rr::args("l" @ "alias_ref_t", "node")]
    #[rr::requires(#type "l" : "-[
        #(<#>@{{option}} (head locs));
        #(<#>@{{option}} (last locs));
        #(Z.of_nat (length elems));
        #($# alloc);
        #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::requires("Hlen" : "length locs = length elems")]
    #[rr::requires("Hnode" : "locs !! i = Some node")]
    #[rr::requires("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires("Hbound" : "length elems ≤ MaxInt usize")]
    #[rr::requires(#iris "LL
        (λ node_loc next prev elem, guarded true (node_loc ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc node_loc, {A::FreeablePerm} alloc node_loc (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        elems locs alloc")]
    #[rr::ensures(#type "l" : "-[
        #(<#>@{{option}} (head (delete i locs)));
        #(<#>@{{option}} (last (delete i locs)));
        #(Z.of_nat (length (delete i elems)));
        #($# alloc);
        #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::ensures(#iris "LL
        (λ node_loc next prev elem, guarded true (node_loc ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc node_loc, {A::FreeablePerm} alloc node_loc (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        (delete i elems) (delete i locs) alloc")]
    #[rr::ensures(#type "node" : "(locs !! S i, last (take i locs), elems !!! i)" @ "Node_inv_t {rt_of T} -[] -[{T}]")]
    #[rr::ensures(#iris "{A::FreeablePerm} alloc node (ly_size (use_struct_layout_alg' (Node_sls {st_of T})))")]
    #[rr::ensures("length (delete i locs) = length (delete i elems)")]
    #[rr::ensures("Forall (λ l, l.(loc_a) ≠ 0) (delete i locs)")]
    #[rr::ensures("length (delete i elems) ≤ MaxInt usize")]
    unsafe fn unlink_node(&mut self, mut node: NonNull<Node<T>>) {
        let node = unsafe { &mut *node.as_ptr() }; // this one is ours now, we can create an &mut.

        // Not creating new mutable (unique!) references overlapping `element`.
        match node.prev {
            Some(prev) => unsafe { (*prev.as_ptr()).next = node.next },
            // this node is the head node
            None => self.head = node.next,
        };

        match node.next {
            Some(next) => unsafe { (*next.as_ptr()).prev = node.prev },
            // this node is the tail node
            None => self.tail = node.prev,
        };

        self.len -= 1;
    }

    /// Splices a series of nodes between two existing nodes.
    ///
    /// Warning: this will not check that the provided node belongs to the two existing lists.
    #[inline]
    unsafe fn splice_nodes(
        &mut self,
        existing_prev: Option<NonNull<Node<T>>>,
        existing_next: Option<NonNull<Node<T>>>,
        mut splice_start: NonNull<Node<T>>,
        mut splice_end: NonNull<Node<T>>,
        splice_length: usize,
    ) {
        // This method takes care not to create multiple mutable references to whole nodes at the same time,
        // to maintain validity of aliasing pointers into `element`.
        if let Some(mut existing_prev) = existing_prev {
            unsafe {
                existing_prev.as_mut().next = Some(splice_start);
            }
        } else {
            self.head = Some(splice_start);
        }
        if let Some(mut existing_next) = existing_next {
            unsafe {
                existing_next.as_mut().prev = Some(splice_end);
            }
        } else {
            self.tail = Some(splice_end);
        }
        unsafe {
            splice_start.as_mut().prev = existing_prev;
            splice_end.as_mut().next = existing_next;
        }

        self.len += splice_length;
    }

    /// Detaches all nodes from a linked list as a series of nodes.
    #[inline]
    fn detach_all_nodes(mut self) -> Option<(NonNull<Node<T>>, NonNull<Node<T>>, usize)> {
        let head = self.head.take();
        let tail = self.tail.take();
        let len = std::mem::replace(&mut self.len, 0);
        if let Some(head) = head {
            // SAFETY: In a LinkedList, either both the head and tail are None because
            // the list is empty, or both head and tail are Some because the list is populated.
            // Since we have verified the head is Some, we are sure the tail is Some too.
            let tail = unsafe { tail.unwrap_unchecked() };
            Some((head, tail, len))
        } else {
            None
        }
    }

    /*
    #[inline]
    unsafe fn split_off_before_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self
    where
        A: AllocatorClone,
    {
        // The split node is the new head node of the second part
        if let Some(mut split_node) = split_node {
            let first_part_head;
            let first_part_tail;
            unsafe {
                first_part_tail = split_node.as_mut().prev.take();
            }
            if let Some(mut tail) = first_part_tail {
                unsafe {
                    tail.as_mut().next = None;
                }
                first_part_head = self.head;
            } else {
                first_part_head = None;
            }

            let first_part = LinkedList {
                head: first_part_head,
                tail: first_part_tail,
                len: at,
                alloc: self.alloc.clone(),
                marker: PhantomData,
            };

            // Fix the head ptr of the second part
            self.head = Some(split_node);
            self.len = self.len - at;

            first_part
        } else {
            mem::replace(self, LinkedList::new_in(self.alloc.clone()))
        }
    }
    */

    #[inline]
    #[rr::raw_mut_self]
    #[rr::params("l", "split_node" : "option loc", "locs", "elems", "i", "alloc")]
    #[rr::args(
        "l" @ "alias_ref_t",
        "split_node",
        "Z.of_nat i"
    )]
    #[rr::unsafe_elctx("ty_outlives_E {T} ulft_1")]
    #[rr::unsafe_elctx("ty_outlives_E {A} ulft_1")]
    #[rr::requires(#type "l" : "-[
        #(<#>@{{option}} (head locs));
        #(<#>@{{option}} (last locs));
        #(Z.of_nat (length elems));
        #($# alloc);
        #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::requires("Hlen" : "length locs = length elems")]
    #[rr::requires("Hsplit" : "split_node = last (take i locs)")]
    #[rr::requires("Hat" : "i ≤ length elems")]
    #[rr::requires("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires("Hbound" : "length elems ≤ MaxInt usize")]
    #[rr::requires(#iris "LL
        (λ node_loc next prev elem, guarded true (node_loc ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc node_loc, {A::FreeablePerm} alloc node_loc (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        (<#> <$#> elems) locs alloc")]
    #[rr::ensures(#type "l" :
        "$# (mk_linked_list_x (take i elems) (take i locs) alloc)" @
        "LinkedList_inv_t T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]"
    )]
    #[rr::returns("mk_linked_list_x (drop i elems) (drop i locs) alloc")]
    unsafe fn split_off_after_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self
    where
        A: AllocatorClone,
    {
        // The split node is the new tail node of the first part and owns
        // the head of the second part.
        if let Some(mut split_node) = split_node {
            let second_part_head;
            let second_part_tail;
            unsafe {
                second_part_head = split_node.as_mut().next.take();
            }
            if let Some(mut head) = second_part_head {
                unsafe {
                    head.as_mut().prev = None;
                }
                second_part_tail = self.tail;
            } else {
                second_part_tail = None;
            }

            let second_part = LinkedList {
                head: second_part_head,
                tail: second_part_tail,
                len: self.len - at,
                alloc: self.alloc.clone(),
                marker: PhantomData,
            };

            // Fix the tail ptr of the first part
            self.tail = Some(split_node);
            self.len = at;

            second_part
        } else {
            // TODO: extracted for verification to avoid two-phase borrow
            let cloned_alloc = self.alloc.clone();
            mem::replace(self, LinkedList::new_in(cloned_alloc))
        }
    }
}


impl<T, A: Allocator> LinkedList<T, A> {

    #[inline]
    #[rr::returns("mk_linked_list_x [] [] alloc")]
    pub const fn new_in(alloc: A) -> Self {
        LinkedList { head: None, tail: None, len: 0, alloc, marker: PhantomData }
    }

    #[rr::returns("self.(linked_list_elems)")]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { head: self.head, tail: self.tail, len: self.len, marker: PhantomData }
    }

    /// Provides a forward iterator with mutable references.
    ///
    /// # Safety
    /// The caller must retain exclusive ownership of the backing nodes and
    /// pass the full backing list to each iterator step. The concrete step
    /// contracts return raw aliases and preserve that ownership.
    #[rr::raw_mut_self]
    #[rr::params("l", "locs", "elems", "alloc")]
    #[rr::args("l" @ "alias_ref_t")]
    #[rr::unsafe_elctx("ty_outlives_E {T} ulft_1")]
    #[rr::unsafe_elctx("ty_outlives_E {A} ulft_1")]
    #[rr::requires("Hlen" : "length locs = length elems")]
    #[rr::requires("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires("Hbound" : "length elems ≤ MaxInt usize")]
    #[rr::requires(#type "l" : "-[
        #(<#>@{{option}} (head locs)); #(<#>@{{option}} (last locs));
        #(Z.of_nat (length elems)); #($# alloc); #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::requires(#iris "LL
        (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ alloc l, {A::FreeablePerm} alloc l (ly_size (use_struct_layout_alg' (Node_sls {st_of T}))))
        (<#> <$#> elems) locs alloc")]
    #[rr::returns("(head locs, last locs, Z.of_nat (length elems))")]
    #[rr::ensures(#type "l" : "-[
        #(<#>@{{option}} (head locs)); #(<#>@{{option}} (last locs));
        #(Z.of_nat (length elems)); #($# alloc); #tt
    ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::ensures(#iris "LL
        (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ _ _, True) (<#> <$#> elems) locs tt")]
    #[rr::ensures(#iris "[∗ list] l ∈ locs, {A::FreeablePerm} alloc l (ly_size (use_struct_layout_alg' (Node_sls {st_of T})))")]
    pub unsafe fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut { head: self.head, tail: self.tail, len: self.len, marker: PhantomData }
    }

    /// Provides a cursor at the front element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    #[must_use]
    #[rr::returns("mk_cursor_x self 0")]
    pub fn cursor_front(&self) -> Cursor<'_, T, A> {
        Cursor { list: self, index: 0, current: self.head }
    }

    /// Provides a cursor at the back element, or at the ghost position when empty.
    #[rr::returns("mk_cursor_x self (Nat.pred (length self.(linked_list_elems)))")]
    pub fn cursor_back(&self) -> Cursor<'_, T, A> {
        Cursor { list: self, index: self.len.saturating_sub(1), current: self.tail }
    }

    /// Provides an editing cursor at the front element, or at the ghost position when empty.
    #[rr::exists("γ")]
    #[rr::ensures(#iris "Inherit [ulft_1] (RelEq (T:= LinkedListRT {rt_of T} {rt_of A}) γ self.ghost)")]
    #[rr::returns("mk_cursor_mut_x self.cur 0 γ")]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut { index: 0, current: self.head, list: self }
    }

    /// Provides an editing cursor at the back element, or at the ghost position when empty.
    #[rr::exists("γ")]
    #[rr::ensures(#iris "Inherit [ulft_1] (RelEq (T:= LinkedListRT {rt_of T} {rt_of A}) γ self.ghost)")]
    #[rr::returns("mk_cursor_mut_x self.cur (Nat.pred (length self.cur.(linked_list_elems))) γ")]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut { index: self.len.saturating_sub(1), current: self.tail, list: self }
    }

    #[rr::returns("bool_decide (self.(linked_list_elems) = [])")]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    #[rr::returns("length self.(linked_list_elems)")]
    pub fn len(&self) -> usize {
        self.len
    }

    #[rr::observe("self.ghost": "mk_linked_list_x ([] : list (place_rfn {rt_of T})) [] self.cur.(linked_list_alloc)")]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    pub fn clear(&mut self) {
        // We need to drop the nodes while keeping self.alloc
        // We can do this by moving (head, tail, len) into a new list that borrows self.alloc
        drop(LinkedList {
            head: self.head.take(),
            tail: self.tail.take(),
            len: std::mem::take(&mut self.len),
            alloc: &self.alloc,
            marker: PhantomData,
        });
    }

    /*
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == x)
    }
    */

    #[rr::returns("head self.(linked_list_elems)")]
    pub fn front(&self) -> Option<&T> {
        // TODO: Use `self.head.as_ref().map(...)` once closure specifications can
        // refer to the semantic type `{T}`.
        match self.head {
            Some(node) => unsafe { Some(&(*node.as_ptr()).element) },
            None => None,
        }
    }

    #[rr::exists("γ")]
    #[rr::returns("match self.cur.(linked_list_elems) with x :: _ => Some (x, γ) | [] => None end")]
    #[rr::observe("self.ghost": "mk_linked_list_x (match self.cur.(linked_list_elems) with _ :: xs => PlaceGhost (rt := {rt_of T}) γ :: ($# xs) | [] => [] end) self.cur.(linked_list_locs) self.cur.(linked_list_alloc)")]
    pub fn front_mut<'a>(&'a mut self) -> Option<&'a mut T> {
        // TODO: Use `self.head.as_mut().map(...)` once closure specifications can
        // refer to the semantic type `{T}` and nested mutable accessor calls are
        // supported here.
        match self.head {
            Some(node) => unsafe { Some(&mut (*node.as_ptr()).element) },
            None => None,
        }
    }

    #[rr::returns("last self.(linked_list_elems)")]
    pub fn back(&self) -> Option<&T> {
        // TODO: Use `self.tail.as_ref().map(...)` once closure specifications can
        // refer to the semantic type `{T}`.
        match self.tail {
            Some(node) => unsafe { Some(&(*node.as_ptr()).element) },
            None => None,
        }
    }

    #[rr::exists("γ")]
    #[rr::returns("match last self.cur.(linked_list_elems) with Some x => Some (x, γ) | None => None end")]
    #[rr::observe("self.ghost": "mk_linked_list_x (match self.cur.(linked_list_elems) with x :: xs => ($# (removelast (x :: xs))) ++ [PlaceGhost (rt := {rt_of T}) γ] | [] => [] end) self.cur.(linked_list_locs) self.cur.(linked_list_alloc)")]
    pub fn back_mut<'a>(&'a mut self) -> Option<&'a mut T> {
        // TODO: Use `self.tail.as_mut().map(...)` once closure specifications can
        // refer to the semantic type `{T}` and nested mutable accessor calls are
        // supported here.
        match self.tail {
            Some(node) => unsafe { Some(&mut (*node.as_ptr()).element) },
            None => None,
        }
    }

    #[rr::exists("new_loc": "loc")]
    #[rr::observe("self.ghost": "mk_linked_list_x (PlaceIn ($#elt) :: ($# self.cur.(linked_list_elems))) (new_loc :: self.cur.(linked_list_locs)) self.cur.(linked_list_alloc)")]
    pub fn push_front(&mut self, elt: T) {
        let _ = self.push_front_mut(elt);
    }

    #[rr::exists("γ")]
    #[rr::exists("new_loc" : "loc")]
    #[rr::returns("(elt, γ)")]
    #[rr::observe(
        "self.ghost":
        "mk_linked_list_x
            (PlaceGhost (rt := {rt_of T}) γ ::
             ($# self.cur.(linked_list_elems)))
            (new_loc :: self.cur.(linked_list_locs))
            self.cur.(linked_list_alloc)"
    )]
    pub fn push_front_mut(&mut self, elt: T) -> &mut T {
        let mut node =
            Box::into_non_null_with_allocator(Box::new_in(Node::new(elt), &self.alloc)).0;
        // SAFETY: node is a unique pointer to a node in self.alloc
        unsafe {
            self.push_front_node(node);
            &mut node.as_mut().element
        }
    }

    #[rr::returns("head self.cur.(linked_list_elems)")]
    #[rr::observe("self.ghost": "mk_linked_list_x (tail ($# self.cur.(linked_list_elems))) (tail self.cur.(linked_list_locs)) self.cur.(linked_list_alloc)")]
    pub fn pop_front(&mut self) -> Option<T> {
        self.pop_front_node().map(
            #[rr::params("next", "prev", "element", "a")]
            #[rr::args("((next, prev, element), a)")]
            #[rr::returns("element")]
            |node| Node::into_element(node),
        )
    }

    #[rr::exists("new_loc": "loc")]
    #[rr::observe("self.ghost": "mk_linked_list_x (($# self.cur.(linked_list_elems)) ++ [PlaceIn ($#elt)]) (self.cur.(linked_list_locs) ++ [new_loc]) self.cur.(linked_list_alloc)")]
    pub fn push_back(&mut self, elt: T) {
        let _ = self.push_back_mut(elt);
    }

    #[rr::exists("γ")]
    #[rr::exists("new_loc" : "loc")]
    #[rr::returns("(elt, γ)")]
    #[rr::observe(
        "self.ghost":
        "mk_linked_list_x
            (($# self.cur.(linked_list_elems)) ++ [PlaceGhost (rt := {rt_of T}) γ])
            (self.cur.(linked_list_locs) ++ [new_loc])
            self.cur.(linked_list_alloc)"
    )]
    pub fn push_back_mut(&mut self, elt: T) -> &mut T {
        let mut node =
            Box::into_non_null_with_allocator(Box::new_in(Node::new(elt), &self.alloc)).0;
        // SAFETY: node is a unique pointer to a node in self.alloc
        unsafe {
            self.push_back_node(node);
            &mut node.as_mut().element
        }
    }

    #[rr::returns("last self.cur.(linked_list_elems)")]
    #[rr::observe("self.ghost": "mk_linked_list_x (removelast ($# self.cur.(linked_list_elems))) (removelast self.cur.(linked_list_locs)) self.cur.(linked_list_alloc)")]
    pub fn pop_back(&mut self) -> Option<T> {
        self.pop_back_node().map(
            #[rr::params("next", "prev", "element", "a")]
            #[rr::args("((next, prev, element), a)")]
            #[rr::returns("element")]
            |node| Node::into_element(node),
        )
    }

    #[rr::params("elems", "locs", "alloc", "i" : "nat", "γ")]
    #[rr::args("(mk_linked_list_x elems locs alloc, γ)", "Z.of_nat i")]
    #[rr::returns("mk_linked_list_x (drop i elems) (drop i locs) alloc")]
    #[rr::observe("γ" : "$# (mk_linked_list_x (take i elems) (take i locs) alloc)")]
    #[rr::may_unwind_if("i > length elems")]
    pub fn split_off(&mut self, at: usize) -> LinkedList<T, A>
    where
        A: AllocatorClone,
    {
        let len = self.len();
        // TODO(verification): removed the string
        //assert!(at <= len, "Cannot split off at a nonexistent index");
        assert!(at <= len);
        if at == 0 {
            let alloc = self.alloc.clone();
            return mem::replace(self, Self::new_in(alloc));
        } else if at == len {
            return Self::new_in(self.alloc.clone());
        }

        // Below, we iterate towards the `i-1`th node, either from the start or the end,
        // depending on which would be faster.
        let split_node = if at - 1 <= len - 1 - (at - 1) {
            // SAFETY: This traversal retains raw ownership of every node.
            // Iterator steps return raw aliases and preserve that ownership.
            let mut iter = unsafe { self.iter_mut() };
            // instead of skipping using .skip() (which creates a new struct),
            // we skip manually so we can access the head field without
            // depending on implementation details of Skip
            for _ in 0..at - 1 {
                #[rr::params("list_loc" : "loc")]
                #[rr::exists("k" : "nat")]
                #[rr::inv_var("iter" : "#(locs !! k, last locs, Z.of_nat (length elems - k))")]
                #[rr::inv("Hprogress" : "{Iter}.1 = Z.of_nat k")]
                #[rr::inv("Hrange_end" : "{Iter}.2 = Z.of_nat (i - 1)")]
                #[rr::inv("Hsteps" : "k ≤ i - 1")]
                #[rr::inv(#type "list_loc" : "-[
                    #(<#>@{{option}} (head locs)); #(<#>@{{option}} (last locs));
                    #(Z.of_nat (length elems)); #($# alloc); #tt
                ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
                #[rr::inv(#iris "[∗ list] l ∈ locs, {A::FreeablePerm} alloc l (ly_size (use_struct_layout_alg' (Node_sls {st_of T})))")]
                #[rr::inv(#iris "LL
                    (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
                    (λ _ _, True) (<#> <$#> elems) locs tt")]
                #[rr::ignore] || {};
                iter.next();
            }
            iter.head
        } else {
            // better off starting from the end
            // SAFETY: As in the forward branch, node ownership is retained
            // explicitly and iterator steps return raw aliases.
            let mut back_iter = unsafe { self.iter_mut() };
            for _ in 0..len - 1 - (at - 1) {
                #[rr::params("list_loc" : "loc")]
                #[rr::exists("k" : "nat")]
                #[rr::inv_var("back_iter" : "#(head locs, last (take (length elems - k) locs), Z.of_nat (length elems - k))")]
                #[rr::inv("Hprogress" : "{Iter}.1 = Z.of_nat k")]
                #[rr::inv("Hrange_end" : "{Iter}.2 = Z.of_nat (length elems - i)")]
                #[rr::inv("Hsteps" : "k ≤ length elems - i")]
                #[rr::inv(#type "list_loc" : "-[
                    #(<#>@{{option}} (head locs)); #(<#>@{{option}} (last locs));
                    #(Z.of_nat (length elems)); #($# alloc); #tt
                ]" @ "LinkedList_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
                #[rr::inv(#iris "[∗ list] l ∈ locs, {A::FreeablePerm} alloc l (ly_size (use_struct_layout_alg' (Node_sls {st_of T})))")]
                #[rr::inv(#iris "LL
                    (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
                    (λ _ _, True) (<#> <$#> elems) locs tt")]
                #[rr::ignore] || {};
                back_iter.next_back();
            }
            back_iter.tail
        };
        unsafe { self.split_off_after_node(split_node, at) }
    }

    /*
    pub fn remove(&mut self, at: usize) -> T {
        let len = self.len();
        assert!(at < len, "Cannot remove at an index outside of the list bounds");

        // Below, we iterate towards the node at the given index, either from
        // the start or the end, depending on which would be faster.
        let offset_from_end = len - at - 1;
        if at <= offset_from_end {
            let mut cursor = self.cursor_front_mut();
            for _ in 0..at {
                cursor.move_next();
            }
            cursor.remove_current().unwrap()
        } else {
            let mut cursor = self.cursor_back_mut();
            for _ in 0..offset_from_end {
                cursor.move_prev();
            }
            cursor.remove_current().unwrap()
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let mut cursor = self.cursor_front_mut();
        while let Some(node) = cursor.current() {
            if !f(node) {
                cursor.remove_current().unwrap();
            } else {
                cursor.move_next();
            }
        }
    }

    */

    // Safety only: every predicate state and mutable element argument is callable.
    #[rr::requires(#iris "□ (∀ f args, ∃ p, {F::Pre} π p f args)")]
    #[rr::requires(#iris "li_sealed (□ (∀ p f x γ f' b,
        {F::PostMut} π p f (((x, γ) -:: -[]) : plist (RT_xt ∘ place_rfnRT) [prodRT (place_rfnRT {rt_of T}) gnameRT]) f' b -∗
        ∃ x' : {xt_of T}, gvar_pobs γ ($# x')))")]
    #[rr::requires("closure_may_unwind {F::UnwindCondition} → False")]
    #[rr::returns("tt")]
    pub fn extract_if<F>(&mut self, filter: F) -> ExtractIf<'_, T, F, A>
    where
        F: FnMut(&mut T) -> bool,
    {
        // avoid borrow issues.
        let it = self.head;
        let old_len = self.len;

        ExtractIf { list: self, it, pred: filter, idx: 0, old_len }
    }
}


// NOTE: removed #[may_dangle] on T
impl< T, A: Allocator> Drop for LinkedList<T, A> {
    #[rr::unsafe_elctx("ty_outlives_E {T} ulft_1")]
    #[rr::unsafe_elctx("ty_outlives_E {A} ulft_1")]
    #[rr::params("l", "elems", "locs", "alloc")]
    #[rr::args("l" @ "alias_ref_t")]
    #[rr::requires(#type "l" : "$# (mk_linked_list_x elems locs alloc)" @ "LinkedList_inv_t T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::ensures(#type "l" : "mk_linked_list_x [] [] alloc" @ "LinkedList_inv_t T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    #[rr::may_unwind_if("{T::DropGlueUnwind}")]
    #[rr::ensures_on_unwind(#iris "∃ remaining' locs', l ◁ₗ[π, Owned] # (mk_linked_list_x remaining' locs' alloc) @ ◁ LinkedList_inv_t T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]")]
    // TODO: currently not established because of the recursive type issue.
    //#[rr::ensures(#iris "[∗ list] x ∈ elems, ty_ghost_drop {T} π ($# x)")]
    fn drop(&mut self) {
        // The guard's alias is only a location. Ownership of the remaining list
        // is a separate conjunct of its type invariant, carried by the guard
        // into drop glue when dropping an element unwinds.
        #[rr::refined_by("(l, x)" : "(loc * directRT (RT_xt (LinkedListRT {rt_of T} {rt_of A})))%type")]
        #[rr::inv(#iris "guarded true (l ◁ₗ[π, Owned] #($# x) @ ◁ (LinkedList_inv_t T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]))")]
        #[rr::ghost_drop(#iris "l ◁ₗ[π, Owned] #(mk_linked_list_x [] [] x.(linked_list_alloc)) @ ◁ (LinkedList_inv_t T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty])")]
        #[rr::ty_lfts("ty_lfts {T} ++ ty_lfts {A} ++ [ulft_a]")]
        #[rr::ty_wf_E("ty_wf_E {T} ++ ty_wf_E {A} ++ ty_outlives_E {T} ulft_a ++ ty_outlives_E {A} ulft_a")]
        #[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind} ∨ {A::DropGlueUnwind}")]
        struct DropGuard<'a, T, A: Allocator>(#[rr::field("#(l)" @ "alias_ref_t" : "locRT")] &'a mut LinkedList<T, A>);

        impl<'a, T, A: Allocator> Drop for DropGuard<'a, T, A> {
            #[rr::unsafe_elctx("ty_outlives_E {T} ulft_a")]
            #[rr::unsafe_elctx("ty_outlives_E {A} ulft_a")]
            #[rr::params("g", "l", "remaining", "locs", "alloc")]
            #[rr::args("g" @ "alias_ref_t")]
            #[rr::requires(#type "g" : "(l, mk_linked_list_x remaining locs alloc)" @ "LinkedListTAasstd_ops_Drop_drop_DropGuard_inv_t T_rt A_rt Allocator_A_spec_attrs -[ulft_a] -[T_ty; A_ty]")]
            #[rr::ensures(#type "g" : "(l, mk_linked_list_x [] [] alloc)" @ "LinkedListTAasstd_ops_Drop_drop_DropGuard_inv_t T_rt A_rt Allocator_A_spec_attrs -[ulft_a] -[T_ty; A_ty]")]
            #[rr::may_unwind_if("{T::DropGlueUnwind}")]
            #[rr::ensures_on_unwind(#iris "∃ remaining' locs', g ◁ₗ[π, Owned] #((l, mk_linked_list_x remaining' locs' alloc)) @ (◁ LinkedListTAasstd_ops_Drop_drop_DropGuard_inv_t T_rt A_rt Allocator_A_spec_attrs -[ulft_a] -[T_ty; A_ty])")]
            fn drop(&mut self) {
                // Continue the same loop we do below. This only runs when a destructor has
                // panicked. If another one panics this will abort.
                while self.0.pop_front_node().is_some() {
                    let _ =
                    #[rr::exists("remaining'")]
                    #[rr::exists("locs'" : "list loc")]
                    #[rr::inv(#type "g" : "(l, mk_linked_list_x remaining' locs' alloc)" @ "LinkedListTAasstd_ops_Drop_drop_DropGuard_inv_t T_rt A_rt Allocator_A_spec_attrs -[ulft_a] -[T_ty; A_ty]")]
                    #[rr::ignore] || {};
                }
            }
        }

        // Wrap self so that if a destructor panics, we can try to keep looping
        let guard = DropGuard(self);
        while guard.0.pop_front_node().is_some() {
            #[rr::exists("dropped", "remaining")]
            #[rr::exists("remaining_locs" : "list loc")]
            #[rr::inv(#iris "l ◁ₗ[π, Owned] #(mk_linked_list_x ($# remaining) remaining_locs alloc) @ ◁ (LinkedList_inv_t T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty])")]
            //#[rr::inv_var("guard" : "#(l, mk_linked_list_x (remaining) alloc)")]
            //#[rr::inv(#iris "[∗ list] x ∈ dropped, ty_ghost_drop {T} π ($# x)")]
            #[rr::inv("elems = dropped ++ remaining")]
            #[rr::ignore] || {};
        }
        std::mem::forget(guard);
    }
}

#[rr::instantiate("Params" := "unit")]
#[rr::instantiate("Inv" := "λ π _ self, True%I")]
#[rr::instantiate("Next" := "λ π _ l e l2,
    (⌜if_None e (l = [] ∧ l2 = [])⌝ ∗
    ⌜if_Some e (λ e, l = e :: l2)⌝)%I")]
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            // TODO Avoid Option::map so the shared node interpretation and lifetime 'a
            // remain available directly in this function's verification context.
            match self.head {
                Some(node) => unsafe {
                    // Need an unbound lifetime to get 'a
                    let node = &*node.as_ptr();
                    self.len -= 1;
                    self.head = node.next;
                    Some(&node.element)
                },
                None => None,
            }
        }
    }

    //#[inline]
    //fn size_hint(&self) -> (usize, Option<usize>) {
        //(self.len, Some(self.len))
    //}

    //#[inline]
    //fn last(mut self) -> Option<&'a T> {
        //self.next_back()
    //}
}

#[rr::instantiate("NextBack" := "λ π _ l e l2,
    (⌜if_None e (l = [] ∧ l2 = [])⌝ ∗
    ⌜if_Some e (λ e, l = l2 ++ [e])⌝)%I")]
impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    #[rr::verify]
    fn next_back(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            return None;
        }
        // SAFETY: When `len > 0`, `head` and `tail` are guaranteed to be `Some`.
        // The lifetime of the returned reference is bound to the lifetime of the iterator,
        // which is valid because the iterator holds a reference to the list.
        Some(unsafe {
            // Need an unbound lifetime to get 'a
            let node = &*self.tail.unwrap_unchecked().as_ptr();
            self.len -= 1;
            self.tail = node.prev;
            &node.element
        })
    }
}

// Generic iterator clients cannot obtain the required invariant. Concrete
// calls use the raw ownership contract below instead.
#[rr::instantiate("Params" := "unit")]
#[rr::instantiate("Inv" := "λ π _ _, False%I")]
#[rr::instantiate("Next" := "λ π _ _ _ _, True%I")]
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    #[rr::params("locs" : "list loc", "elems" : "list {xt_of T}", "front" : "nat", "back" : "nat")]
    #[rr::requires("Hfront" : "front ≤ back")]
    #[rr::requires("Hback" : "back ≤ length elems")]
    #[rr::requires("Hlen" : "length locs = length elems")]
    #[rr::requires("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires("Hbound" : "length elems ≤ MaxInt usize")]
    #[rr::requires("Hstate" : "self.cur = (locs !! front, last (take back locs), Z.of_nat (back - front))")]
    #[rr::requires(#iris "LL
        (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ _ _, True) (<#> <$#> elems) locs tt")]
    #[rr::returns("if decide (front < back)%nat then
        (λ l, l at{{use_struct_layout_alg' (Node_sls {st_of T})}}ₗ \"element\") <$> (locs !! front)
        else None" @ "Option_ty locRT -[] -[alias_ref_t]")]
    #[rr::observe("self.ghost" : "(
        locs !! (if decide (front < back)%nat then S front else front),
        last (take back locs),
        Z.of_nat (back - (if decide (front < back)%nat then S front else front)))")]
    #[rr::ensures(#iris "LL
        (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ _ _, True) (<#> <$#> elems) locs tt")]
    fn next(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            return None;
        }
        // SAFETY: The concrete contract supplies exclusive ownership of the
        // backing list. Its head exists when len > 0. The returned reference
        // is interpreted as a raw alias while backing ownership is retained.
        Some(unsafe {
            // Need an unbound lifetime to get 'a
            let node = &mut *self.head.unwrap_unchecked().as_ptr();
            self.len -= 1;
            self.head = node.next;
            &mut node.element
        })
    }
}

#[rr::instantiate("NextBack" := "λ π _ _ _ _, True%I")]
impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    #[rr::params("locs" : "list loc", "elems" : "list {xt_of T}", "front" : "nat", "back" : "nat")]
    #[rr::requires("Hfront" : "front ≤ back")]
    #[rr::requires("Hback" : "back ≤ length elems")]
    #[rr::requires("Hlen" : "length locs = length elems")]
    #[rr::requires("Hnonnull" : "Forall (λ l, l.(loc_a) ≠ 0) locs")]
    #[rr::requires("Hbound" : "length elems ≤ MaxInt usize")]
    #[rr::requires("Hstate" : "self.cur = (locs !! front, last (take back locs), Z.of_nat (back - front))")]
    #[rr::requires(#iris "LL
        (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ _ _, True) (<#> <$#> elems) locs tt")]
    #[rr::returns("if decide (front < back)%nat then
        (λ l, l at{{use_struct_layout_alg' (Node_sls {st_of T})}}ₗ \"element\") <$> (locs !! Nat.pred back)
        else None" @ "Option_ty locRT -[] -[alias_ref_t]")]
    #[rr::observe("self.ghost" : "(
        locs !! front,
        last (take (if decide (front < back)%nat then Nat.pred back else back) locs),
        Z.of_nat ((if decide (front < back)%nat then Nat.pred back else back) - front))")]
    #[rr::ensures(#iris "LL
        (λ l next prev elem, guarded true (l ◁ₗ[π, Owned] #((next, prev, elem)) @ ◁(Node_inv_t {rt_of T} <TY> {T} <INST!>)))
        (λ _ _, True) (<#> <$#> elems) locs tt")]
    fn next_back(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            return None;
        }
        // SAFETY: The concrete contract supplies exclusive ownership of the
        // backing list. Its tail exists when len > 0. The returned reference
        // is interpreted as a raw alias while backing ownership is retained.
        Some(unsafe {
            // Need an unbound lifetime to get 'a
            let node = &mut *self.tail.unwrap_unchecked().as_ptr();
            self.len -= 1;
            self.tail = node.prev;
            &mut node.element
        })
    }
}


// The position is the length of the list when the cursor is on the ghost element.
#[rr::refined_by("c" : "CursorRT {rt_of T} {rt_of A}")]
#[rr::exists("index" : "nat")]
#[rr::inv("Hlen" : "length (c.(shared_cursor_list).(linked_list_locs)) = length (c.(shared_cursor_list).(linked_list_elems))")]
#[rr::inv("Hposition" : "c.(shared_cursor_pos) ≤ length (c.(shared_cursor_list).(linked_list_elems))")]
#[rr::inv("Hindex" : "c.(shared_cursor_pos) < length (c.(shared_cursor_list).(linked_list_elems)) → index = c.(shared_cursor_pos)")]
#[rr::inv("Hindex_bound" : "index ≤ length (c.(shared_cursor_list).(linked_list_elems))")]
#[rr::ty_lfts("ty_lfts {T} ++ ty_lfts {A} ++ [ulft_a]")]
#[rr::ty_wf_E("ty_wf_E {T} ++ ty_wf_E {A} ++ ty_outlives_E {T} ulft_a ++ ty_outlives_E {A} ulft_a")]
pub struct Cursor<
    'a,
    T: 'a,
    A: Allocator = Global,
> {
    #[rr::field("#(Z.of_nat index)")]
    index: usize,
    #[rr::field("#(<#>@{{option}} (c.(shared_cursor_list).(linked_list_locs) !! c.(shared_cursor_pos)))")]
    current: Option<NonNull<Node<T>>>,
    #[rr::field("#(PlaceIn c.(shared_cursor_list))")]
    list: &'a LinkedList<T, A>,
}

// The position is the length of the list when the cursor is on the ghost element.
#[rr::refined_by("c" : "CursorMutRT {rt_of T} {rt_of A}")]
#[rr::exists("index" : "nat")]
#[rr::inv("Hlen" : "length (c.(cursor_list).(linked_list_locs)) = length (c.(cursor_list).(linked_list_elems))")]
#[rr::inv("Hposition" : "c.(cursor_pos) ≤ length (c.(cursor_list).(linked_list_elems))")]
#[rr::inv("Hindex" : "c.(cursor_pos) < length (c.(cursor_list).(linked_list_elems)) → index = c.(cursor_pos)")]
#[rr::inv("Hindex_bound" : "index ≤ length (c.(cursor_list).(linked_list_elems))")]
#[rr::ty_lfts("ty_lfts {T} ++ ty_lfts {A} ++ [ulft_a]")]
#[rr::ty_wf_E("ty_wf_E {T} ++ ty_wf_E {A} ++ ty_outlives_E {T} ulft_a ++ ty_outlives_E {A} ulft_a")]
pub struct CursorMut<
    'a,
    T: 'a,
    A: Allocator = Global,
> {
    #[rr::field("#(Z.of_nat index)")]
    index: usize,
    #[rr::field("#(<#>@{{option}} (c.(cursor_list).(linked_list_locs) !! c.(cursor_pos)))")]
    current: Option<NonNull<Node<T>>>,
    #[rr::field("#(PlaceIn c.(cursor_list), c.(cursor_ghost))")]
    list: &'a mut LinkedList<T, A>,
}

impl<'a, T, A: Allocator> CursorMut<'a, T, A> {
    /// Returns the cursor position index within the `LinkedList`.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    #[must_use]
    #[rr::returns("if decide (self.(cursor_pos) < length (self.(cursor_list).(linked_list_elems))) then Some (Z.of_nat self.(cursor_pos)) else None")]
    pub fn index(&self) -> Option<usize> {
        let _ = self.current?;
        Some(self.index)
    }

    /// Moves the cursor to the next element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    #[rr::observe("self.ghost": "$# mk_cursor_mut_x self.cur.(cursor_list) (cursor_next self.cur.(cursor_pos) (length (self.cur.(cursor_list).(linked_list_elems)))) self.cur.(cursor_ghost)")]
    pub fn move_next(&mut self) {
        match self.current.take() {
            // We had no current element; the cursor was sitting at the start position
            // Next element should be the head of the list
            None => {
                self.current = self.list.head;
                self.index = 0;
            }
            // We had a previous element, so let's go to its next
            Some(current) => unsafe {
                // TODO For verification, to unfold the LinkedList invariant
                self.list.len;

                self.current = current.as_ref().next;
                self.index += 1;
            },
        }
    }

    /// Moves the cursor to the previous element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    #[rr::observe("self.ghost": "$# mk_cursor_mut_x self.cur.(cursor_list) (cursor_prev self.cur.(cursor_pos) (length (self.cur.(cursor_list).(linked_list_elems)))) self.cur.(cursor_ghost)")]
    pub fn move_prev(&mut self) {
        match self.current.take() {
            // No current. We're at the start of the list. Yield None and jump to the end.
            None => {
                self.current = self.list.tail;
                self.index = self.list.len().saturating_sub(1);
            }
            // Have a prev. Yield it and go to the previous element.
            Some(current) => unsafe {
                // TODO: For verification, to unfold the LinkedList invariant
                self.list.len;

                self.current = current.as_ref().prev;

                // TODO: unfolded due to closure lifetime issue
                //self.index = self.index.checked_sub(1).unwrap_or_else(#[rr::returns("length ({self.*list}.(linked_list_elems))")]|| self.list.len());
                self.index = if let Some(idx) = self.index.checked_sub(1) {
                    idx
                } else {
                    self.list.len() 
                };
            },
        }
    }

#[rr::skip]
    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    #[must_use]
    #[rr::exists("γelt")]
    #[rr::returns("match self.cur.(cursor_list).(linked_list_elems) !! self.cur.(cursor_pos) with Some x => Some (x, γelt) | None => None end")]
    #[rr::observe("self.ghost": "mk_cursor_mut_x (mk_linked_list_x (match self.cur.(cursor_list).(linked_list_elems) !! self.cur.(cursor_pos) with Some _ => <[self.cur.(cursor_pos) := PlaceGhost (rt := {rt_of T}) γelt]> ($# self.cur.(cursor_list).(linked_list_elems)) | None => $# self.cur.(cursor_list).(linked_list_elems) end) self.cur.(cursor_list).(linked_list_locs) self.cur.(cursor_list).(linked_list_alloc)) self.cur.(cursor_pos) self.cur.(cursor_ghost)")]
    pub fn current(&mut self) -> Option<&mut T> {
        unsafe { self.current.map(|current| &mut (*current.as_ptr()).element) }
    }

    #[rr::returns("self.cur.(cursor_list).(linked_list_elems) !! self.cur.(cursor_pos)")]
    #[rr::observe("self.ghost": "mk_cursor_mut_x (mk_linked_list_x (delete self.cur.(cursor_pos) ($# self.cur.(cursor_list).(linked_list_elems))) (delete self.cur.(cursor_pos) self.cur.(cursor_list).(linked_list_locs)) self.cur.(cursor_list).(linked_list_alloc)) self.cur.(cursor_pos) self.cur.(cursor_ghost)")]
    pub fn remove_current(&mut self) -> Option<T> {
        let unlinked_node = self.current?;
        // NOTE: need to open invariant of self.list here. 
        // NOTE: inserted for verification 
        self.list.len;

        unsafe {
            self.current = unlinked_node.as_ref().next;
            self.list.unlink_node(unlinked_node);
            let unlinked_node = Box::from_raw_in(unlinked_node.as_ptr(), &self.list.alloc);
            Some(unlinked_node.element)
        }
    }
}

// The public refinement deliberately carries no extraction history. The list
// borrow (including its eventual observation) remains owned by the list field.
// `pos` indexes the current list, whereas `visited` counts original nodes:
// removing a node increments `visited` without incrementing `pos`.
#[rr::refined_by("()" : "unit")]
#[rr::exists("l" : "LinkedListX {xt_of T} {xt_of A}")]
#[rr::exists("γlist" : "gname")]
#[rr::exists("f" : "{xt_of F}")]
#[rr::exists("pos" : "nat")]
#[rr::exists("visited" : "nat")]
#[rr::exists("initial_len" : "nat")]
#[rr::inv("Hposition" : "pos ≤ length l.(linked_list_elems)")]
#[rr::inv("Hvisited_position" : "pos ≤ visited")]
#[rr::inv("Hvisited_bound" : "visited ≤ initial_len")]
#[rr::inv("Hremaining" : "(length l.(linked_list_elems) - pos = initial_len - visited)%nat")]
#[rr::inv("Hinitial_bound" : "initial_len ≤ MaxInt usize")]
#[rr::ty_lfts("ty_lfts {T} ++ ty_lfts {F} ++ ty_lfts {A} ++ [ulft_a]")]
#[rr::ty_wf_E("ty_wf_E {T} ++ ty_wf_E {F} ++ ty_wf_E {A} ++ ty_outlives_E {T} ulft_a ++ ty_outlives_E {F} ulft_a ++ ty_outlives_E {A} ulft_a")]
#[rr::derive_instantiate("DropGlueUnwind" := "{F::DropGlueUnwind}")]
#[rr::ghost_drop("True")]
pub struct ExtractIf<
    'a,
    T: 'a,
    F: 'a,
    A: Allocator = Global,
> {
    #[rr::field("#(PlaceIn (RT_xrt (LinkedListRT {rt_of T} {rt_of A}) l), γlist)")]
    list: &'a mut LinkedList<T, A>,
    #[rr::field("#(<#>@{{option}} (l.(linked_list_locs) !! pos))")]
    it: Option<NonNull<Node<T>>>,
    #[rr::field("#($# f)")]
    pred: F,
    #[rr::field("#(Z.of_nat visited)")]
    idx: usize,
    #[rr::field("#(Z.of_nat initial_len)")]
    old_len: usize,
}

// No relationship between the result and the list is exposed. The iterator
// invariant permits repeated predicate calls and observes a concrete updated
// element after each call, without constraining its value or the Boolean result.
#[rr::instantiate("Params" := "unit")]
#[rr::instantiate("Inv" := "λ π _ _,
    ((□ (∀ f args, ∃ p, {G::Pre} π p f args)) ∗
     li_sealed (□ (∀ p f x γ f' b,
        {G::PostMut} π p f (((x, γ) -:: -[]) : plist (RT_xt ∘ place_rfnRT) [prodRT (place_rfnRT {rt_of T}) gnameRT]) f' b -∗
        ∃ x' : {xt_of T}, gvar_pobs γ ($# x'))) ∗
     ⌜closure_may_unwind {G::UnwindCondition} → False⌝)%I")]
#[rr::instantiate("Next" := "λ π _ _ _ _, True%I")]
impl<T, G, A: Allocator> Iterator for ExtractIf<'_, T, G, A>
where
    G: FnMut(&mut T) -> bool,
{
    type Item = T;

    // TODO: I think it would be good to specify an on_unwind_ensures for closures that gives some
    // observation. 
    #[rr::default_spec]
    fn next(&mut self) -> Option<T> {
        while let Some(mut node) = self.it {
            #[rr::params("γself" : "gname")]
            #[rr::inv_vars("self")]
            #[rr::invariant("Hself_ghost" : "self.ghost = γself")]
            #[rr::invariant("Hself_state" : "self.cur = tt")]
            #[rr::ignore] || {};
            unsafe {
                // TODO(verification): Open the list invariant before accessing the cursor node.
                self.list.len;

                self.it = node.as_ref().next;
                self.idx += 1;

                if (self.pred)(&mut node.as_mut().element) {
                    // `unlink_node` is okay with aliasing `element` references.
                    self.list.unlink_node(node);
                    return Some(Box::from_raw_in(node.as_ptr(), &self.list.alloc).element);
                }
            }
        }

        None
    }

    //fn size_hint(&self) -> (usize, Option<usize>) {
        //(0, Some(self.old_len - self.idx))
    //}
}
