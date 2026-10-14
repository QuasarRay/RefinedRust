#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![register_tool(rr)]
#![rr::package("drop_realization_lifetimes")]
#![rr::include("stdlib")]

// The borrowed lifetime is embedded in Box/Option's type arguments, not a formal
// lifetime parameter of their drop realizations.
#[rr::verify]
pub fn drop_box(_value: Box<&i32>) {}

#[rr::verify]
pub fn drop_option(_value: Option<Box<&i32>>) {}

#[rr::verify]
pub fn drop_tuple<'a>(_value: (Box<&'a i32>, Box<&'a i32>)) {}

// Exercise the same specialization inside synthesized drop glue.
pub struct Wrapper<'a> {
    pub value: Option<Box<&'a i32>>,
}

// Unlike Box and Option, Wrapper really has a formal lifetime parameter.
#[rr::verify]
pub fn drop_wrapper(_value: Wrapper<'_>) {}

pub struct Outer<'a> {
    pub value: Wrapper<'a>,
}

pub struct TupleWrapper<'a> {
    pub value: (Box<&'a i32>, Box<&'a i32>),
}
