#[macro_use]
extern crate error_chain_mini_derive;
extern crate error_chain_mini;

use error_chain_mini::*;
#[test]
fn short_enum() {
    #[derive(ErrorKind)]
    enum MyError {
        #[msg(short = "error kind 1")]
        Kind1,
        #[msg(short = "error kind 2")]
        Kind2,
    }
    assert_eq!(MyError::Kind1.short(), "error kind 1");
    assert_eq!(MyError::Kind2.short(), "error kind 2");
}

#[test]
fn nomsg_enum() {
    #[derive(ErrorKind)]
    enum MyError {
        Kind1,
        Kind2,
    }
    assert_eq!(MyError::Kind1.short(), "MyError::Kind1");
    assert_eq!(MyError::Kind2.short(), "MyError::Kind2");
}

#[test]
fn detailed_enum_1() {
    #[derive(ErrorKind)]
    enum MyError {
        #[msg(short = "MyError1", detailed = "value: {}", _0)]
        Kind1(usize),
        #[msg(short = "MyError2")]
        Kind2,
    }
    assert_eq!(MyError::Kind2.short(), "MyError2");
    assert_eq!(MyError::Kind1(3).detailed(), "value: 3");
}

#[test]
fn detailed_enum_2() {
    #[derive(ErrorKind)]
    enum MyError {
        #[msg(short = "MyError1", detailed = "value: {}", idx)]
        Kind1 { idx: usize },
        #[msg(short = "MyError2", detailed = "info1: {} info2: {}", info1, info2)]
        Kind2 { info1: usize, info2: &'static str },
    }
    assert_eq!(MyError::Kind1 { idx: 3 }.detailed(), "value: 3");
    assert_eq!(
        MyError::Kind2 {
            info1: 3,
            info2: "hoge"
        }.detailed(),
        "info1: 3 info2: hoge"
    );
}

#[test]
fn detailed_enum_rev() {
    #[derive(ErrorKind)]
    enum MyError {
        #[msg(detailed = "value: {}", _0, short = "MyError1")]
        Kind1(usize),
        #[msg(short = "MyError2")]
        Kind2,
    }
    assert_eq!(MyError::Kind2.short(), "MyError2");
    assert_eq!(MyError::Kind1(3).detailed(), "value: 3");
}

#[test]
fn short_struct() {
    #[derive(ErrorKind)]
    #[msg(short = "My Error")]
    struct MyError;
    assert_eq!(MyError {}.short(), "My Error");
}

#[test]
fn detailed_struct() {
    #[derive(ErrorKind)]
    #[msg(short = "My Error", detailed = "{}", _0)]
    struct MyError(usize);
    assert_eq!(MyError(5).full(), "My Error { 5 }");
}

#[test]
fn nomsg_struct() {
    #[derive(ErrorKind)]
    struct MyError;
    assert_eq!(MyError {}.short(), "MyError");
}

#[test]
#[ignore]
fn display() {
    #[derive(ErrorKind)]
    enum MyError {
        #[msg(short = "MyError1", detailed = "value: {}", _0)]
        Kind1(usize),
        #[msg(short = "MyError2")]
        Kind2,
    }
    #[derive(ErrorKind)]
    enum MyError2 {
        #[msg(short = "MyError", detailed = "{}", _0)]
        MyError(MyError),
    }
    let chained = MyError::Kind1(5).into_with(|| "error 1 was caused");
    let chained = chained
        .convert_with(|e| MyError2::MyError(e))
        .chain(|| "error 2 was caused");
    println!("{}", chained);
}
