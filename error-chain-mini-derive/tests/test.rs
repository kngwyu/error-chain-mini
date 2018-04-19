extern crate synstructure;
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
fn detailed_enum() {
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
