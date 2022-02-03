use std::fmt;

pub mod lexer;

pub const INTEGER_LIMIT: u32 = 1 << 31;

#[derive(Clone, Debug, PartialEq)]
pub struct Location {
    pub start: usize,
    pub end: usize,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.start, self.end)
    }
}

pub struct Log {
    pub errors: Vec<Error>,
}

pub struct Error {
    pub location: Location,
    pub msg: String,
}

fn main() {
    println!("Hello, world!");
}
