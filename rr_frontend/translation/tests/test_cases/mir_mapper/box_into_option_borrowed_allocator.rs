#![feature(allocator_api)]
#![allow(dead_code)]

use std::alloc::Allocator;

struct Node<T>(T);

#[mapper::run]
#[mapper::points]
#[mapper::drop_borrows]
fn box_into_option<T, A: Allocator>(node: Box<Node<T>, &A>) -> Option<T> {
    Some(node.0)
}
