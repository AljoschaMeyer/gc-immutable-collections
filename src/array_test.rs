use std::cmp;

pub use im::Vector;

use crate::array::*;

use arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
pub enum ArrayConstruction {
    New,
    Singleton(u8),
    Insert(Box<Self>, usize, u8),
    Remove(Box<Self>, usize),
    Update(Box<Self>, usize, u8),
    Slice(Box<Self>, usize, usize),
    SliceTo(Box<Self>, usize),
    SliceFrom(Box<Self>, usize),
    Splice(Box<Self>, usize, Box<Self>),
    SplitLeft(Box<Self>, usize),
    SplitRight(Box<Self>, usize),
    Concat(Box<Self>, Box<Self>),
    Builder(Vec<(bool, u8)>),
}

impl ArrayConstruction {
    pub fn construct_array(&self) -> Array<u8> {
        match self {
            Self::New => Array::new(),
            Self::Singleton(v) => Array::singleton(*v),
            Self::Insert(a, i, v) => {
                let a = Self::construct_array(a);
                let i = if a.count() == 0 { 0 } else { *i % a.count() };
                a.insert(i, *v)
            }
            Self::Remove(a, i) => {
                let a = Self::construct_array(a);
                let i = if a.count() == 0 { return Array::new() } else { *i % a.count() };
                a.remove(i)
            }
            Self::Update(a, i, v) => {
                let a = Self::construct_array(a);
                let i = if a.count() == 0 { return Array::new() } else { *i % a.count() };
                a.update(i, *v)
            }
            Self::Slice(a, p1, p2) => {
                let a = Self::construct_array(a);
                let p1 = *p1 % (a.count() + 1);
                let p2 = *p2 % (a.count() + 1);
                let p2 = cmp::max(p1, p2);
                a.slice(p1, p2)
            }
            Self::SliceTo(a, p) => {
                let a = Self::construct_array(a);
                let p = *p % (a.count() + 1);
                a.slice_to(p)
            }
            Self::SliceFrom(a, p) => {
                let a = Self::construct_array(a);
                let p = *p % (a.count() + 1);
                a.slice_from(p)
            }
            Self::SplitLeft(a, p) => {
                let a = Self::construct_array(a);
                let p = *p % (a.count() + 1);
                a.split(p).0
            }
            Self::SplitRight(a, p) => {
                let a = Self::construct_array(a);
                let p = *p % (a.count() + 1);
                a.split(p).1
            }
            Self::Splice(a, p, b) => {
                let a = Self::construct_array(a);
                let p = *p % (a.count() + 1);
                let b = Self::construct_array(b);
                a.splice(p, &b)
            }
            Self::Concat(a, b) => Self::construct_array(a).concat(&Self::construct_array(b)),
            Self::Builder(vs) => {
                let mut b = ArrayBuilder::new();
                for (front, v) in vs {
                    if *front {
                        b.push_front(v.clone());
                    } else {
                        b.push_back(v.clone());
                    }
                }
                b.build()
            }
        }
    }

    pub fn construct_control(&self) -> Vector<u8> {
        match self {
            Self::New => Vector::new(),
            Self::Singleton(v) => Vector::unit(*v),
            Self::Insert(a, i, v) => {
                let mut a = Self::construct_control(a);
                let i = if a.len() == 0 { 0 } else { *i % a.len() };
                a.insert(i, *v);
                a
            }
            Self::Remove(a, i) => {
                let mut a = Self::construct_control(a);
                let i = if a.len() == 0 { return Vector::new() } else { *i % a.len() };
                a.remove(i);
                a
            }
            Self::Update(a, i, v) => {
                let mut a = Self::construct_control(a);
                let i = if a.len() == 0 { return Vector::new() } else { *i % a.len() };
                a.set(i, *v);
                a
            }
            Self::Slice(a, p1, p2) => {
                let mut a = Self::construct_control(a);
                let p1 = *p1 % (a.len() + 1);
                let p2 = *p2 % (a.len() + 1);
                let p2 = cmp::max(p1, p2);
                a.slice(p1..p2)
            }
            Self::SliceTo(a, p) => {
                let mut a = Self::construct_control(a);
                let p = *p % (a.len() + 1);
                a.slice(..p)
            }
            Self::SliceFrom(a, p) => {
                let mut a = Self::construct_control(a);
                let p = *p % (a.len() + 1);
                a.slice(p..)
            }
            Self::SplitLeft(a, p) => {
                let a = Self::construct_control(a);
                let p = *p % (a.len() + 1);
                a.split_at(p).0
            }
            Self::SplitRight(a, p) => {
                let a = Self::construct_control(a);
                let p = *p % (a.len() + 1);
                a.split_at(p).1
            }
            Self::Splice(a, p, b) => {
                let a = Self::construct_control(a);
                let p = *p % (a.len() + 1);
                let b = Self::construct_control(b);
                let (mut c, d) = a.split_at(p);
                c.append(b);
                c.append(d);
                c
            }
            Self::Concat(a, b) => {
                let mut r = Self::construct_control(a);
                r.append(Self::construct_control(b));
                r
            }
            Self::Builder(vs) => {
                let mut control = Vector::new();

                for (is_front, v) in vs {
                    if *is_front {
                        control.push_front(v.clone());
                    } else {
                        control.push_back(v.clone());
                    }
                }

                control
            }
        }
    }
}

#[derive(Debug, Arbitrary)]
pub enum FocusConstruction {
    New(ArrayConstruction, usize),
}

impl FocusConstruction {
    pub fn construct_focus(&self) -> ArrayFocus<u8> {
        match self {
            Self::New(c, p) => {
                let arr = c.construct_array();
                ArrayFocus::new(&arr, p % (arr.count() + 1))
            }
        }
    }

    pub fn construct_control(&self) -> (Vector<u8>, usize) {
        match self {
            Self::New(c, p) => {
                let control = c.construct_control();
                let p = p % (control.len() + 1);
                (control, p)
            }
        }
    }
}

pub fn control_get_relative(control: &(Vector<u8>, usize), i: isize) -> Option<&u8> {
    let tmp = (control.1 as isize).saturating_add(i);
    if tmp < 0 {
        None
    } else {
        control.0.get(tmp as usize)
    }
}

pub fn control_refocus(control: &(Vector<u8>, usize), by: isize) -> ((Vector<u8>, usize), isize) {
    let control_index = if by >= 0 {
        cmp::min(control.0.len() as isize, (control.1 as isize).saturating_add(by)) as usize
    } else {
        cmp::max(0, (control.1 as isize) + by) as usize
    };
    let moved = (control_index as isize) - (control.1 as isize);

    ((control.0.clone(), control_index), moved)
}
