//! Have you ever felt that `failure` or `error-chain` is too complex?
//!
//! If so, this library is for you.
//!
//! This library provides very simple chainable error type `ChainedError` and some related traits.
//! # Example
//! ```should_panic
//! extern crate error_chain_mini;
//! use std::io;
//! use error_chain_mini::*;
//! #[derive(Debug)]
//! enum MyErrorKind {
//!     IoError(io::Error),
//!     IndexEroor(usize),
//!     TrivialError,
//! }
//! impl ErrorKind for MyErrorKind {
//!     fn short(&self) -> &str {
//!         match *self {
//!             MyErrorKind::IoError(_) => "io error",
//!             MyErrorKind::IndexEroor(_) => "index error",
//!             MyErrorKind::TrivialError => "trivial error"
//!         }
//!     }
//! }
//! type MyError = ChainedError<MyErrorKind>;
//! type MyResult<T> = Result<T, MyError>;
//! fn always_fail() -> MyResult<!> {
//!     Err(MyErrorKind::TrivialError.into_with("Oh my god!"))
//! }
//! fn main() {
//!     let chained = always_fail().chain_err("Error in main()").unwrap();
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
/// use error_chain_mini::ErrorKind;
/// #[derive(Debug)]
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
/// # }
/// ```
pub trait ErrorKind {
    fn short(&self) -> &str;
    fn detailed(&self) -> String {
        String::new()
    }
    fn into_err(self) -> ChainedError<Self>
    where
        Self: Sized,
    {
        ChainedError {
            kind: self,
            context: vec![],
        }
    }
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
    kind: T,
    context: Vec<String>,
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

impl<T: ErrorKind + Debug> Debug for ChainedError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<T: ErrorKind + Debug> Error for ChainedError<T> {
    fn description(&self) -> &str {
        self.kind.short()
    }
}

impl<T: ErrorKind> Display for ChainedError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "kind: {} {}", self.kind.short(), self.kind.detailed())?;
        for (i, s) in self.context.iter().enumerate() {
            writeln!(f, "context{:3}: {}", i, s)?;
        }
        Ok(())
    }
}

impl<T: ErrorKind> ChainedError<T> {
    fn chain<C: ErrorContext>(mut self, s: C) -> Self {
        let s = s.context().to_owned();
        self.context.push(s);
        self
    }
}

pub trait ResultExt {
    type OkType;
    type ErrType;
    fn chain_err<C, E>(self, context: C) -> Result<Self::OkType, ChainedError<E>>
    where
        E: ErrorKind,
        C: ErrorContext,
        Self::ErrType: Into<ChainedError<E>>;
}

impl<T, E> ResultExt for Result<T, E> {
    type OkType = T;
    type ErrType = E;
    fn chain_err<C, F>(self, context: C) -> Result<T, ChainedError<F>>
    where
        F: ErrorKind,
        C: ErrorContext,
        Self::ErrType: Into<ChainedError<F>>,
    {
        self.map_err(|e| {
            let chained = e.into();
            chained.chain(context)
        })
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn chain() {}
}
