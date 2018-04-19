//! This library provides very simple chainable error type `ChainedError` and some related traits.
//! # Example
//! ```
//! extern crate error_chain_mini;
//! #[macro_use]
//! extern crate error_chain_mini_derive;
//! use std::io;
//! use error_chain_mini::*;
//! #[derive(ErrorKind)]
//! enum MyErrorKind {
//!     #[msg(short = "io error", detailed = "inner: {:?}", _0)]
//!     IoError(io::Error),
//!     #[msg(short = "index error", detailed = "invalid index: {:?}", _0)]
//!     IndexEroor(usize),
//!     #[msg(short = "trivial error")]
//!     TrivialError,
//! }
//! type MyError = ChainedError<MyErrorKind>;
//! type MyResult<T> = Result<T, MyError>;
//! fn always_fail() -> MyResult<!> {
//!     Err(MyErrorKind::TrivialError.into_with("Oh my god!"))
//! }
//! fn main() {
//!     assert_eq!("index error invalid index: 10", MyErrorKind::IndexEroor(10).full());
//!     let chained = always_fail().chain_err("Error in main()");
//!     assert!(chained.is_err());
//!     if let Err(chained) = chained {
//!         assert_eq!(chained.context[0], "Oh my god!");
//!         assert_eq!(chained.context[1], "Error in main()");
//!     }
//! }
//! ```

use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};

/// Error kind type.
///
/// You have to implement `short`, which is exepected to return short hand description about error kind.
///
/// In addition, you can implement detailed description by `detailed`, but it's optional.
/// # Example
/// ```
/// # extern crate error_chain_mini; fn main() {
/// use std::io;
/// use std::fs::File;
/// use error_chain_mini::{ErrorKind, ResultExt};
/// enum MyErrorKind {
///     IoError(io::Error),
///     IndexEroor(usize),
/// }
/// impl ErrorKind for MyErrorKind {
///     fn short(&self) -> &str {
///         match *self {
///             MyErrorKind::IoError(_) => "io error",
///             MyErrorKind::IndexEroor(_) => "index error"
///         }
///     }
/// }
/// impl From<io::Error> for MyErrorKind {
///     fn from(e: io::Error) -> Self {
///         MyErrorKind::IoError(e)
///     }
/// }
/// let file = File::open("not_existing_file").into_chained("In io()");
/// assert!(file.is_err());
/// if let Err(e) = file {
///     if let MyErrorKind::IoError(ioerr) = e.kind {
///         assert_eq!(format!("{}", ioerr), "No such file or directory (os error 2)");
///     } else {
///         panic!("error kind is incorrect");
///     }
///     assert_eq!(e.context, vec!["In io()".to_owned()])
/// }
/// # }
/// ```
pub trait ErrorKind {
    /// Short description of error type, compatible with `std::error::Error::description`.
    ///
    /// To avoid duplication of implement same message, we have 2 message type short/detailed.
    ///
    /// Actually, `"{} {}", ErrorKind::short(), ErrorKind::detailed()"` is used for display
    /// and you can also get full error message by `full` method.
    fn short(&self) -> &str;
    /// Detailed description of error type.
    fn detailed(&self) -> String {
        String::new()
    }
    /// Return full error message as String.
    ///
    /// Do not overrride this method.
    fn full(&self) -> String {
        format!("{} {}", self.short(), self.detailed())
    }

    /// Get [ChainedError](struct.ChainedError.html) with no context.
    ///
    /// Do not overrride this method.
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # use error_chain_mini::*; fn main() {
    /// #[derive(ErrorKind, Eq, PartialEq, Debug)]
    /// #[msg(short = "My Error")]
    /// struct MyError;
    /// let chained = MyError{}.into_err();
    /// assert_eq!(chained.kind, MyError {});
    /// assert!(chained.context.is_empty());
    /// # }
    /// ```
    fn into_err(self) -> ChainedError<Self>
    where
        Self: Sized,
    {
        ChainedError {
            kind: self,
            context: vec![],
        }
    }

    /// Get [ChainedError](struct.ChainedError.html) with a context.
    ///
    /// Do not overrride this method.
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # use error_chain_mini::*; fn main() {
    /// fn my_func() {
    ///     #[derive(ErrorKind, Eq, PartialEq, Debug)]
    ///     #[msg(short = "My Error")]
    ///     struct MyError;
    ///     let chained = MyError{}.into_with("Error in my_func");
    ///     assert_eq!(chained.kind, MyError {});
    ///     assert_eq!(chained.context[0], "Error in my_func");
    /// }
    /// # }
    /// ```
    fn into_with<C: ErrorContext>(self, cxt: C) -> ChainedError<Self>
    where
        Self: Sized,
    {
        let s = cxt.context().to_owned();
        ChainedError {
            kind: self,
            context: vec![s],
        }
    }
}

/// Error context type.
///
/// Expected usage is use string as context, like
pub trait ErrorContext: Sized {
    fn context(&self) -> &str;
}

impl<S: AsRef<str>> ErrorContext for S {
    fn context(&self) -> &str {
        self.as_ref()
    }
}

/// Chainable error type.

pub struct ChainedError<T: ErrorKind> {
    pub kind: T,
    pub context: Vec<String>,
}

impl<T: ErrorKind + Clone> Clone for ChainedError<T> {
    fn clone(&self) -> Self {
        ChainedError {
            kind: self.kind.clone(),
            context: self.context.clone(),
        }
    }
}

unsafe impl<T: ErrorKind + Sync> Sync for ChainedError<T> {}
unsafe impl<T: ErrorKind + Send> Send for ChainedError<T> {}

impl<T: ErrorKind> Debug for ChainedError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<T: ErrorKind> Error for ChainedError<T> {
    fn description(&self) -> &str {
        self.kind.short()
    }
}

impl<T: ErrorKind> Display for ChainedError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "###ChainedError: ")?;
        writeln!(f, "kind: {} {}", self.kind.short(), self.kind.detailed())?;
        for (i, s) in self.context.iter().enumerate() {
            writeln!(f, "context{:3}: {}", i, s)?;
        }
        writeln!(f, "###")
    }
}

impl<T: ErrorKind> ChainedError<T> {
    pub fn chain<C: ErrorContext>(mut self, s: C) -> Self {
        let s = s.context().to_owned();
        self.context.push(s);
        self
    }
}

pub trait ResultExt {
    type OkType;
    type ErrType;
    fn chain_err<C, K>(self, context: C) -> Result<Self::OkType, ChainedError<K>>
    where
        K: ErrorKind,
        C: ErrorContext,
        Self::ErrType: Into<ChainedError<K>>;
    fn into_chained<C, K>(self, context: C) -> Result<Self::OkType, ChainedError<K>>
    where
        K: ErrorKind + From<Self::ErrType>,
        C: ErrorContext;
}

impl<T, E> ResultExt for Result<T, E> {
    type OkType = T;
    type ErrType = E;
    fn chain_err<C, K>(self, context: C) -> Result<T, ChainedError<K>>
    where
        K: ErrorKind,
        C: ErrorContext,
        Self::ErrType: Into<ChainedError<K>>,
    {
        self.map_err(|e| e.into().chain(context))
    }
    fn into_chained<C, K>(self, context: C) -> Result<Self::OkType, ChainedError<K>>
    where
        K: ErrorKind + From<Self::ErrType>,
        C: ErrorContext,
    {
        self.map_err(|e| K::from(e).into_with(context))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::Error as IoError;
    enum MyErrorKind {
        Io(IoError),
        Index(usize),
    }
    impl ErrorKind for MyErrorKind {
        fn short(&self) -> &str {
            match self {
                MyErrorKind::Io(_) => "io error",
                MyErrorKind::Index(_) => "index error",
            }
        }
        fn detailed(&self) -> String {
            match *self {
                MyErrorKind::Io(ref io) => format!("{:?}", io),
                MyErrorKind::Index(id) => format!("{}", id),
            }
        }
    }
    type MyError = ChainedError<MyErrorKind>;
    impl From<IoError> for MyErrorKind {
        fn from(e: IoError) -> Self {
            MyErrorKind::Io(e)
        }
    }
    fn index_err(u: usize) -> Result<u32, MyError> {
        let array = vec![3, 7, 9, 20];
        if let Some(u) = array.get(u) {
            Ok(*u)
        } else {
            Err(MyErrorKind::Index(u).into_with("Invalid access in index_err()"))
        }
    }
    #[test]
    fn io() {
        use std::fs::File;
        let file = File::open("not_existing_file").into_chained("In io()");
        assert!(file.is_err());
        if let Err(e) = file {
            if let MyErrorKind::Index(_) = e.kind {
                panic!("error kind is incorrect");
            }
            assert_eq!(e.context, vec!["In io()".to_owned()])
        }
    }
    #[test]
    fn index() {
        let id = 8;
        let res = index_err(id).chain_err("In index()");
        assert!(res.is_err());
        if let Err(e) = res {
            if let MyErrorKind::Index(u) = e.kind {
                assert_eq!(u, id);
            } else {
                panic!("error kind is incorrect");
            }
            assert_eq!(
                e.context,
                vec![
                    "Invalid access in index_err()".to_owned(),
                    "In index()".to_owned(),
                ]
            );
        }
    }
}
