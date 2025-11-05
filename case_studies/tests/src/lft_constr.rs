
/*
#[rr::verify]
fn test1(x: &i32) {

}

#[rr::verify]
fn test2<'a, 'b: 'a>(x: &'a i32, y: &'b i32) {

}

#[rr::verify]
fn test3<'a, 'b: 'a, 'c : 'b>(x: &'a i32, y: &'b i32, z: &'c i32) {

}

#[rr::verify]
fn test4<'a, 'b: 'a, 'c>(x: &'a i32, y: &'b (&'c i32)) {

}

#[rr::verify]
fn test5<'a, T>(x: &'a T) {

}

#[rr::verify]
fn test6<'a, T: 'a>(x: &'a T) {

}

#[rr::verify]
fn test7<'a>(x: &'a i32) where i32: 'a {

}

#[rr::verify]
fn test8<'a>(x: &'a i32) where (i32, &'a i32): 'a {

}


trait Bla {
    #[rr::verify]
    fn foo<'a, 'b: 'a>(x: &'a i32, y: &'b i32);
}
*/




trait Foo {
    #[rr::verify]
    fn foo();
}


impl<'a, 'b: 'a> Foo for &'b &'a i32 {
    #[rr::verify]
    fn foo() {

    }
}

//impl<'a, 'b> Foo for &'b &'a i32 where i32: 'b {
    //fn foo() {

    //}
//}


// Note: HRTBs do not support lifetime constraints
/*
trait Bar<T> {

}

fn bla<T>() where T: for<'a, 'b: 'a> Bar<&'a &'b i32> {

}
*/
