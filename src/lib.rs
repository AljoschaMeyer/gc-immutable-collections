#![feature(never_type)]

mod map;
pub use map::*;
mod array;
pub use array::*;

pub mod array_test;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Find {
    Lt,
    Leq,
    Eq,
    Geq,
    Gt,
}

impl Find {
    pub fn matches_eq(&self) -> bool {
        match self {
            Find::Leq | Find::Eq | Find::Geq => true,
            _ => false,
        }
    }

    pub fn matches_less(&self) -> bool {
        match self {
            Find::Lt | Find::Leq => true,
            _ => false,
        }
    }

    pub fn matches_greater(&self) -> bool {
        match self {
            Find::Geq | Find::Gt => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
