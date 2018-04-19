# error-chain-mini
[![crates.io](http://meritbadge.herokuapp.com/error-chain-mini)](https://crates.io/crates/error-chain-mini)
[![documentation](https://docs.rs/error-chain-mini/badge.svg)](https://docs.rs/error-chain-mini)
[![Build Status](https://travis-ci.org/kngwyu/error-chain-mini.svg?branch=master)](https://travis-ci.org/kngwyu/error-chain-mini)


I think [error-chain](https://github.com/rust-lang-nursery/error-chain) is good, especially I love `chain_err` method.

However, sometimes I feel it too complex.
I don't want to generate `ResultExt` and `ChainedError` by macro. Isn't it confusing?

So, I made this tiny library, providing very straight forward implementation of
`ResultExt`, `ChainedError`, and some related traits.

In addition, You can use `derive` to implement your own `ErrorKind` type.

# Example
```rust
extern crate error_chain_mini;
#[macro_use]
extern crate error_chain_mini_derive;
use std::io;
use error_chain_mini::*;
#[derive(ErrorKind)]
enum MyErrorKind {
    #[msg(short = "io error", detailed = "inner: {:?}", _0)]
    IoError(io::Error),
    #[msg(short = "index error", detailed = "invalid index: {:?}", _0)]
    IndexEroor(usize),
    #[msg(short = "trivial error")]
    TrivialError,
}
type MyError = ChainedError<MyErrorKind>;
type MyResult<T> = Result<T, MyError>;
fn always_fail() -> MyResult<!> {
    Err(MyErrorKind::TrivialError.into_with("Oh my god!"))
}
fn main() {
    assert_eq!("index error invalid index: 10", MyErrorKind::IndexEroor(10).full());
    let chained = always_fail().chain_err("Error in main()");
    assert!(chained.is_err());
    if let Err(chained) = chained {
        assert_eq!(chained.context[0], "Oh my god!");
        assert_eq!(chained.context[1], "Error in main()");
    }
}
```

# Required minimum version of Rust

1.26.0 ([match_default_bindings](https://github.com/rust-lang/rust/issues/42640) is needed)

# License

This project is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.

