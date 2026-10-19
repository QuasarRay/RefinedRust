#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![register_tool(rr)]
#![rr::package("drop_realization_lifetimes")]

pub struct Owned<T> {
    pub value: T,
}

pub enum Maybe<T> {
    None,
    Some(T),
}

// The borrowed lifetime is embedded in Owned/Maybe's type arguments, not a formal
// lifetime parameter of their drop realizations. The unconstrained T ensures
// that rustc retains the drops even though references themselves need no drop.
#[rr::verify]
pub fn drop_owned<T>(_value: Owned<(&i32, T)>) {}

#[rr::verify]
pub fn drop_maybe<T>(_value: Maybe<Owned<(&i32, T)>>) {}

#[rr::verify]
pub fn drop_tuple<'a, T>(_value: (Owned<(&'a i32, T)>, Owned<(&'a i32, T)>)) {}

// Exercise the same specialization inside synthesized drop glue.
pub struct Wrapper<'a, T> {
    pub value: Maybe<Owned<(&'a i32, T)>>,
}

// Unlike Owned and Maybe, Wrapper really has a formal lifetime parameter.
#[rr::verify]
pub fn drop_wrapper<T>(_value: Wrapper<'_, T>) {}

pub struct Outer<'a, T> {
    pub value: Wrapper<'a, T>,
}

pub struct TupleWrapper<'a, T> {
    pub value: (Owned<(&'a i32, T)>, Owned<(&'a i32, T)>),
}
