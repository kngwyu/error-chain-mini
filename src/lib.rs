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
//! fn always_fail() -> MyResult<()> {
//!     Err(MyErrorKind::TrivialError.into_with("Oh my god!"))
//! }
//! fn main() {
//!     assert_eq!("index error, invalid index: 10", MyErrorKind::IndexEroor(10).full());
//!     let chained = always_fail().chain_err("Error in main()");
//!     assert!(chained.is_err());
//!     if let Err(chained) = chained {
//!         let mut cxts = chained.contexts();
//!         assert_eq!(cxts.next().unwrap(), "Oh my god!");
//!         assert_eq!(cxts.next().unwrap(), "Error in main()");
//!     }
//! }
//! ```

use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};

/// Error kind type.
///
/// You can implement `short`, which is exepected to return short hand description about error kind.
///
/// In addition, you can implement detailed description by `detailed`, but it's optional.
/// # Example
/// ```
/// # extern crate error_chain_mini; fn main() {
/// use std::io;
/// use std::fs::File;
/// use std::error::Error;
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
///     assert_eq!(e.description(), "io error");
///     if let MyErrorKind::IoError(ioerr) = e.kind() {
///         assert_eq!(format!("{}", ioerr), "No such file or directory (os error 2)");
///     } else {
///         panic!("error kind is incorrect");
///     }
///     assert_eq!(e.contexts().collect::<Vec<_>>(), vec!["In io()"])
/// }
/// # }
/// ```
///
/// Instead of implement `ErrorKind`, you can use derive.
/// In this case, if you don't write `#[msg..` attribute, full path of the variant
/// (e.g. `MyErrorKind::IndexError`) is used for the return value of `short`.
///
/// **Notes**
/// If you derive `ErrorKind` for type A, `std::fmt::Display` is automatically implemented
/// for convinience.
///
/// # Example
/// ```
/// # extern crate error_chain_mini;
/// # #[macro_use] extern crate error_chain_mini_derive;
/// # fn main() {
/// use std::io;
/// use std::fs::File;
/// use std::error::Error;
/// use error_chain_mini::{ErrorKind, ResultExt};
/// #[derive(ErrorKind)]
/// enum MyErrorKind {
///     IoError(io::Error),
///     IndexEroor(usize),
/// }
/// impl From<io::Error> for MyErrorKind {
///     fn from(e: io::Error) -> Self {
///         MyErrorKind::IoError(e)
///     }
/// }
/// let file = File::open("not_existing_file").into_chained("In io()");
/// assert!(file.is_err());
/// if let Err(e) = file {
///     assert_eq!(e.description(), "MyErrorKind::IoError");
///     assert_eq!(format!("{}", e.kind()), "MyErrorKind::IoError");
///     if let MyErrorKind::IoError(ioerr) = e.kind() {
///         assert_eq!(format!("{}", ioerr), "No such file or directory (os error 2)");
///     } else {
///         panic!("error kind is incorrect");
///     }
///     assert_eq!(e.contexts().collect::<Vec<_>>(), vec!["In io()"])
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
    /// **Notes** Do not overrride this method.
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # fn main() {
    /// use error_chain_mini::*;
    /// #[derive(ErrorKind, Eq, PartialEq, Debug)]
    /// #[msg(short = "My Error", detailed = "value: {}", value)]
    /// struct MyError {
    ///     value: usize,
    /// }
    /// let err = MyError { value: 320 };
    /// assert_eq!(format!("{}", err), err.full());
    /// # }
    /// ```
    fn full(&self) -> String {
        let detailed = self.detailed();
        if detailed.is_empty() {
            self.short().to_string()
        } else {
            format!("{}, {}", self.short(), self.detailed())
        }
    }

    /// Get [ChainedError](struct.ChainedError.html) with no context.
    ///
    /// Do not overrride this method.
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # use error_chain_mini::*; fn main() {
    /// #[derive(Clone, Copy, ErrorKind, Eq, PartialEq, Debug)]
    /// struct MyError;
    /// let chained = MyError{}.into_err();
    /// assert_eq!(*chained.kind(), MyError {});
    /// # }
    /// ```
    fn into_err(self) -> ChainedError<Self>
    where
        Self: Sized,
    {
        ChainedError::new(self, vec![])
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
    ///     #[derive(Clone, Copy, ErrorKind, Eq, PartialEq, Debug)]
    ///     struct MyError;
    ///     let chained = MyError{}.into_with("Error in my_func");
    ///     assert_eq!(*chained.kind(), MyError {});
    ///     assert_eq!(chained.contexts().nth(0).unwrap(), "Error in my_func");
    /// }
    /// # }
    /// ```
    fn into_with<C: ErrorContext>(self, cxt: C) -> ChainedError<Self>
    where
        Self: Sized,
    {
        ChainedError::new(self, vec![Box::new(cxt)])
    }
}

/// Error context type.
///
/// Expected usage is use string as context.
///
/// See module level documentation for usage.
pub trait ErrorContext: 'static {
    fn context(&self) -> &str;
}

impl<S: 'static + AsRef<str>> ErrorContext for S {
    fn context(&self) -> &str {
        self.as_ref()
    }
}

/// Chainable error type.
///
/// See module level documentation for usage.
pub struct ChainedError<T: ErrorKind> {
    inner: Box<ErrorImpl<T>>,
}

impl<T: ErrorKind> Debug for ChainedError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<T: ErrorKind> Error for ChainedError<T> {
    fn description(&self) -> &str {
        self.inner.kind.short()
    }
}

impl<T: ErrorKind> Display for ChainedError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "\nkind: {}", self.inner.kind.short())?;
        let detailed = self.inner.kind.detailed();
        if !detailed.is_empty() {
            write!(f, ", {}", detailed)?;
        }
        writeln!(f)?;
        for (i, s) in self.inner.context.iter().enumerate() {
            if i != 0 {
                writeln!(f)?;
            }
            write!(f, "context{:3}: {}", i, s.context())?;
        }
        writeln!(f)
    }
}

impl<T: ErrorKind> ChainedError<T> {
    /// Create new ChainedError.
    pub fn new(kind: T, context: Vec<Box<ErrorContext>>) -> Self {
        ChainedError {
            inner: Box::new(ErrorImpl::new(kind, context)),
        }
    }

    /// Returns a reference of Error Kind
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # use error_chain_mini::*;
    /// # fn main() {
    /// #[derive(Debug, ErrorKind, Eq, PartialEq)]
    /// enum ErrorType {
    ///     A,
    ///     B,
    ///     C
    /// }
    /// let chained = ErrorType::B.into_err();
    /// assert_eq!(*chained.kind(), ErrorType::B);
    /// # }
    /// ```
    pub fn kind(&self) -> &T {
        &self.inner.kind
    }

    /// Returns a reference of Error Contexts
    /// Returns a reference of Error Kind
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # use error_chain_mini::*;
    /// # fn main() {
    /// #[derive(Debug, ErrorKind, Eq, PartialEq)]
    /// enum ErrorType {
    ///     A,
    ///     B,
    ///     C
    /// }
    /// let chained = ErrorType::B.into_with("Error is Caused!");
    /// let chained = chained.chain("Error is Chained!");
    /// let mut cxts = chained.contexts();
    /// assert_eq!(cxts.next().unwrap(), "Error is Caused!");
    /// assert_eq!(cxts.next().unwrap(), "Error is Chained!");
    /// # }
    /// ```
    pub fn contexts(&self) -> impl Iterator<Item = &str> {
        self.inner.context.iter().map(|cxt| cxt.context())
    }

    /// Add context to ChainedError.
    ///
    /// It's more useful to use [chain_err](trait.ResultExt.html#tymethod.chain_err).
    pub fn chain<C: ErrorContext>(mut self, c: C) -> Self {
        self.inner.context.push(Box::new(c));
        self
    }

    /// Convert `ChainedError<T>` into `ChainedError<U>`.
    ///
    /// For some reason, we can't provide this type of conversion directly as a method of
    /// `ResultExt`, so you have to use `map_err` explicitly.
    /// # Usage
    ///
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # use error_chain_mini::*;
    /// mod external {
    /// #    use super::*;
    ///     #[derive(ErrorKind, Eq, PartialEq, Debug)]
    ///     #[msg(short = "error in external")]
    ///     pub struct ExtErrorKind;
    ///     pub type Error = ChainedError<ExtErrorKind>;
    ///     pub fn func() -> Result<(), Error> {
    ///         Err(ExtErrorKind{}.into_with("In external::func()"))
    ///     }
    /// }
    /// # fn main() {
    /// use external::{self, ExtErrorKind};
    /// #[derive(ErrorKind, Eq, PartialEq, Debug)]
    /// enum MyErrorKind {
    ///     Internal,
    ///     #[msg(short = "from mod 'external'", detailed = "{:?}", _0)]
    ///     External(ExtErrorKind),
    /// };
    /// impl From<ExtErrorKind> for MyErrorKind {
    ///     fn from(e: ExtErrorKind) -> MyErrorKind {
    ///         MyErrorKind::External(e)
    ///     }
    /// }
    /// type Error = ChainedError<MyErrorKind>;
    /// let chained: Result<(), Error> = external::func().map_err(|e| e.convert("In my_func()"));
    /// if let Err(chained) = chained {
    ///     assert_eq!(*chained.kind(), MyErrorKind::External(ExtErrorKind {}));
    ///     assert_eq!(chained.contexts().nth(1).unwrap(), "In my_func()");
    /// }
    /// # }
    /// ```    
    pub fn convert<U, C>(mut self, c: C) -> ChainedError<U>
    where
        U: ErrorKind + From<T>,
        C: ErrorContext,
    {
        self.inner.context.push(Box::new(c));
        ChainedError {
            inner: Box::new(self.inner.convert(U::from)),
        }
    }
}

struct ErrorImpl<T> {
    kind: T,
    context: Vec<Box<ErrorContext>>,
}

impl<T> ErrorImpl<T> {
    fn new(kind: T, context: Vec<Box<ErrorContext>>) -> Self {
        ErrorImpl { kind, context }
    }
    fn convert<F, U>(self, f: F) -> ErrorImpl<U>
    where
        F: FnOnce(T) -> U,
    {
        ErrorImpl::new(f(self.kind), self.context)
    }
}

unsafe impl<T: ErrorKind + Sync> Sync for ErrorImpl<T> {}
unsafe impl<T: ErrorKind + Send> Send for ErrorImpl<T> {}

/// `Result` extension to integrate with `ChainedError`
pub trait ResultExt {
    type OkType;
    type ErrType;
    /// Takes Result and add context, if self is Err.
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # fn main() {
    /// use error_chain_mini::*;
    /// #[derive(ErrorKind, Eq, PartialEq, Debug)]
    /// #[msg(short = "My Error")]
    /// struct MyError;
    /// fn my_func() -> Result<(), ChainedError<MyError>>{
    ///     let chained = MyError{}.into_with("Error in my_func");
    ///     Err(chained)
    /// }
    /// let chained = my_func().chain_err("Chained");
    /// assert!(chained.is_err());
    /// if let Err(e) = chained {
    ///     let msg = format!("{}", e);
    ///     assert_eq!(msg, r#"
    /// kind: My Error
    /// context  0: Error in my_func
    /// context  1: Chained
    /// "#);
    /// }
    /// # }
    /// ```
    fn chain_err<C, K>(self, context: C) -> Result<Self::OkType, ChainedError<K>>
    where
        K: ErrorKind,
        C: ErrorContext,
        Self::ErrType: Into<ChainedError<K>>;

    /// Takes Result and context then convert its error type into `ChainedError` with given context.
    /// # Usage
    /// ```
    /// # extern crate error_chain_mini;
    /// # #[macro_use] extern crate error_chain_mini_derive;
    /// # fn main() {
    /// use error_chain_mini::*;
    /// use std::io;
    /// use std::fs::File;
    /// #[derive(Debug, ErrorKind)]
    /// enum MyError {
    ///     #[msg(short = "io error", detailed = "{:?}", _0)]
    ///     Io(io::Error),
    ///     Misc
    /// }
    /// impl From<io::Error> for MyError {
    ///     fn from(e: io::Error) -> Self {
    ///         MyError::Io(e)
    ///     }
    /// }
    /// let file: Result<_, ChainedError<MyError>> = File::open("not_existing_file").into_chained("In io()");
    /// # }
    /// ```
    fn into_chained<C, K>(self, context: C) -> Result<Self::OkType, ChainedError<K>>
    where
        K: ErrorKind + From<Self::ErrType>,
        C: ErrorContext;
}

impl<T, E> ResultExt for Result<T, E> {
    type OkType = T;
    type ErrType = E;
    fn chain_err<C, K>(self, context: C) -> Result<Self::OkType, ChainedError<K>>
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
            if let MyErrorKind::Index(_) = e.kind() {
                panic!("error kind is incorrect");
            }
            assert_eq!(e.contexts().collect::<Vec<_>>(), vec!["In io()"])
        }
    }
    #[test]
    fn index() {
        let id = 8;
        let res = index_err(id).chain_err("In index()");
        assert!(res.is_err());
        if let Err(e) = res {
            if let MyErrorKind::Index(u) = e.kind() {
                assert_eq!(*u, id);
            } else {
                panic!("error kind is incorrect");
            }
            assert_eq!(
                e.contexts().collect::<Vec<_>>(),
                vec![
                    "Invalid access in index_err()".to_owned(),
                    "In index()".to_owned(),
                ]
            );
        }
    }
}
