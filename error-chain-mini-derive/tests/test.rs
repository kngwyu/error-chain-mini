#[macro_use]
extern crate synstructure;
#[macro_use]
extern crate error_chain_mini_derive;
extern crate error_chain_mini;

#[test]
fn short_only_enum() {
    #[derive(ErrorKind)]
    enum MyError {
        #[msg(short = "error kind 1")]
        Kind1,
        #[msg(short = "error kind 2")]
        Kind2,
    }
}
