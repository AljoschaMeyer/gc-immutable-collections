use std::cmp;

pub use im::OrdMap;

use crate::map::*;

use arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
pub enum MapConstruction {
    New,
    Singleton(i8, u8),
    Insert(Box<Self>, i8, u8),
    Remove(Box<Self>, i8),
    Slice(Box<Self>, i8, i8),
    SliceTo(Box<Self>, i8),
    SliceFrom(Box<Self>, i8),
    Union(Box<Self>, Box<Self>),
    UnionSum(Box<Self>, Box<Self>),
    Intersection(Box<Self>, Box<Self>),
    IntersectionSum(Box<Self>, Box<Self>),
    Difference(Box<Self>, Box<Self>),
    SymmetricDifference(Box<Self>, Box<Self>),
    SplitLeft(Box<Self>, i8),
    SplitRight(Box<Self>, i8),
    SplitInclusiveLeft(Box<Self>, i8),
    SplitInclusiveRight(Box<Self>, i8),
    IndexRemove(Box<Self>, usize),
    IndexSlice(Box<Self>, usize, usize),
    IndexSplitLeft(Box<Self>, usize),
    IndexSplitRight(Box<Self>, usize),
    Builder(Vec<(bool, i8, u8)>),
}

impl MapConstruction {
    pub fn construct_map(&self) -> Map<i8, u8> {
        match self {
            Self::New => Map::new(),
            Self::Singleton(k, v) => Map::singleton(*k, *v),
            Self::Insert(a, k, v) => {
                let a = Self::construct_map(a);
                a.insert(*k, *v)
            }
            Self::Remove(a, k) => {
                let a = Self::construct_map(a);
                a.remove(k)
            }
            Self::Slice(a, p1, p2) => {
                let a = Self::construct_map(a);
                let p2 = cmp::max(p1, p2);
                a.slice(p1, p2)
            }
            Self::SliceTo(a, p) => {
                let a = Self::construct_map(a);
                a.slice_to(p)
            }
            Self::SliceFrom(a, p) => {
                let a = Self::construct_map(a);
                a.slice_from(p)
            }
            Self::Union(a, b) => {
                let a = Self::construct_map(a);
                let b = Self::construct_map(b);
                Map::union(&a, &b)
            }
            Self::UnionSum(a, b) => {
                let a = Self::construct_map(a);
                let b = Self::construct_map(b);
                Map::union_with(&a, &b, |l, r| l.wrapping_add(*r))
            }
            Self::Intersection(a, b) => {
                let a = Self::construct_map(a);
                let b = Self::construct_map(b);
                Map::intersection(&a, &b)
            }
            Self::IntersectionSum(a, b) => {
                let a = Self::construct_map(a);
                let b = Self::construct_map(b);
                Map::intersection_with(&a, &b, |l, r| l.wrapping_add(*r))
            }
            Self::Difference(a, b) => {
                let a = Self::construct_map(a);
                let b = Self::construct_map(b);
                Map::difference(&a, &b)
            }
            Self::SymmetricDifference(a, b) => {
                let a = Self::construct_map(a);
                let b = Self::construct_map(b);
                Map::symmetric_difference(&a, &b)
            }
            Self::SplitLeft(a, p) => {
                let a = Self::construct_map(a);
                a.split(p).0
            }
            Self::SplitRight(a, p) => {
                let a = Self::construct_map(a);
                a.split(p).1
            }
            Self::SplitInclusiveLeft(a, p) => {
                let a = Self::construct_map(a);
                a.split_inclusive(p).0
            }
            Self::SplitInclusiveRight(a, p) => {
                let a = Self::construct_map(a);
                a.split_inclusive(p).1
            }
            Self::IndexRemove(a, i) => {
                let a = Self::construct_map(a);
                a.remove_index(*i)
            }
            Self::IndexSlice(a, p1, p2) => {
                let a = Self::construct_map(a);
                let p1 = cmp::min(*p1, a.count());
                let p2 = cmp::min(*p2, a.count());
                let p2 = cmp::max(p1, p2);

                match a.slice_index(p1, p2) {
                    Some(m) => return m,
                    None => {
                        println!("{:?}", a);
                        println!("{:?}", (p1, p2));
                        panic!();
                    }
                }
                // a.slice_index(p1, p2).unwrap()
            }
            Self::IndexSplitLeft(a, p) => {
                let a = Self::construct_map(a);
                let p = cmp::min(*p, a.count());
                a.split_at(p).unwrap().0
            }
            Self::IndexSplitRight(a, p) => {
                let a = Self::construct_map(a);
                let p = cmp::min(*p, a.count());
                a.split_at(p).unwrap().1
            }

            // Self::Splice(a, p, b) => {
            //     let a = Self::construct_map(a);
            //     let p = *p % (a.count() + 1);
            //     let b = Self::construct_map(b);
            //     a.splice(p, &b)
            // }
            // Self::Concat(a, b) => Self::construct_map(a).concat(&Self::construct_map(b)),
            Self::Builder(vs) => {
                let mut b = MapBuilder::new();
                for (front, k, v) in vs {
                    if *front {
                        let _ = b.push_front(k.clone(), v.clone());
                    } else {
                        let _ = b.push_back(k.clone(), v.clone());
                    }
                }
                b.build()
            }
        }
    }

    pub fn construct_control(&self) -> OrdMap<i8, u8> {
        match self {
            Self::New => OrdMap::new(),
            Self::Singleton(k, v) => OrdMap::unit(*k, *v),
            Self::Insert(a, k, v) => {
                let mut a = Self::construct_control(a);
                a.insert(*k, *v);
                a
            }
            Self::Remove(a, k) => {
                let mut a = Self::construct_control(a);
                a.remove(k);
                a
            }
            Self::Slice(a, p1, p2) => {
                let a = Self::construct_control(a);
                let p2 = cmp::max(p1, p2);

                let (_, m, mut r) = a.split_lookup(p1);
                if let Some(mv) = m {
                    r.insert(*p1, mv);
                }

                r.split(p2).0
            }
            Self::SliceTo(a, p) => {
                let a = Self::construct_control(a);
                a.split(p).0
            }
            Self::SliceFrom(a, p) => {
                let a = Self::construct_control(a);

                let (_, m, mut r) = a.split_lookup(p);
                if let Some(mv) = m {
                    r.insert(*p, mv);
                }

                r
            }
            Self::Union(a, b) => {
                let a = Self::construct_control(a);
                let b = Self::construct_control(b);
                a.union(b)
            }
            Self::UnionSum(a, b) => {
                let a = Self::construct_control(a);
                let b = Self::construct_control(b);
                a.union_with(b, |l, r| l.wrapping_add(r))
            }
            Self::Intersection(a, b) => {
                let a = Self::construct_control(a);
                let b = Self::construct_control(b);
                a.intersection(b)
            }
            Self::IntersectionSum(a, b) => {
                let a = Self::construct_control(a);
                let b = Self::construct_control(b);
                a.intersection_with(b, |l, r| l.wrapping_add(r))
            }
            Self::Difference(a, b) => {
                let a = Self::construct_control(a);
                let b = Self::construct_control(b);
                a.relative_complement(b)
            }
            Self::SymmetricDifference(a, b) => {
                let a = Self::construct_control(a);
                let b = Self::construct_control(b);
                a.symmetric_difference(b)
            }
            Self::SplitLeft(a, p) => {
                let a = Self::construct_control(a);
                a.split(p).0
            }
            Self::SplitRight(a, p) => {
                let a = Self::construct_control(a);

                let (_, m, mut r) = a.split_lookup(p);
                if let Some(mv) = m {
                    r.insert(*p, mv);
                }

                r
            }
            Self::SplitInclusiveLeft(a, p) => {
                let a = Self::construct_control(a);
                let (mut l, m, _) = a.split_lookup(p);
                if let Some(mv) = m {
                    l.insert(*p, mv);
                }

                l
            }
            Self::SplitInclusiveRight(a, p) => {
                let a = Self::construct_control(a);
                a.split(p).1
            }
            Self::IndexRemove(a, i) => {
                let mut a = Self::construct_control(a);
                let b = a.skip(*i);
                let k = b.get_min();

                if let Some((k, _)) = k {
                    a.remove(k);
                }

                a
            }
            Self::IndexSlice(a, p1, p2) => {
                let a = Self::construct_control(a);
                let p1 = cmp::min(*p1, a.len());
                let p2 = cmp::min(*p2, a.len());
                let p2 = cmp::max(p1, p2);

                let b = a.skip(p1);
                return b.take(p2 - p1);
            }
            Self::IndexSplitLeft(a, p) => {
                let a = Self::construct_control(a);
                let p = cmp::min(*p, a.len());
                a.take(p)
            }
            Self::IndexSplitRight(a, p) => {
                let a = Self::construct_control(a);
                let p = cmp::min(*p, a.len());
                a.skip(p)
            }
            Self::Builder(vs) => {
                let mut control: OrdMap<i8, u8> = OrdMap::new();

                for (is_front, k, v) in vs {
                    if *is_front {
                        if control.len() == 0 || k < &control.get_min().unwrap().0 {
                            control.insert(*k, v.clone());
                        }
                    } else {
                        if control.len() == 0 || k > &control.get_max().unwrap().0 {
                            control.insert(*k, v.clone());
                        }
                    }
                }

                control
            }
        }
    }
}

#[derive(Debug, Arbitrary)]
pub enum FocusConstruction {
    New(MapConstruction, usize),
}

impl FocusConstruction {
    pub fn construct_focus(&self) -> MapFocus<i8, u8> {
        match self {
            Self::New(c, p) => {
                let map = c.construct_map();
                MapFocus::new(&map, p % (map.count() + 1))
            }
        }
    }

    pub fn construct_control(&self) -> (OrdMap<i8, u8>, usize) {
        match self {
            Self::New(c, p) => {
                let control = c.construct_control();
                let p = p % (control.len() + 1);
                (control, p)
            }
        }
    }
}

pub fn control_get_relative_entry(control: &(OrdMap<i8, u8>, usize), i: isize) -> Option<(i8, u8)> {
    let tmp = (control.1 as isize).saturating_add(i);
    if tmp < 0 || (tmp as usize) >= control.0.len() {
        None
    } else {
        let tmpmap = control.0.take((tmp as usize) + 1);
        match tmpmap.get_max() {
            Some((k, v)) => Some((*k, *v)),
            None => None,
        }
    }
}

pub fn control_get_relative_key(control: &(OrdMap<i8, u8>, usize), i: isize) -> Option<i8> {
    control_get_relative_entry(control, i).map(|(k, _)| k)
}

pub fn control_get_relative(control: &(OrdMap<i8, u8>, usize), i: isize) -> Option<u8> {
    control_get_relative_entry(control, i).map(|(_, v)| v)
}

pub fn control_refocus(control: &(OrdMap<i8, u8>, usize), by: isize) -> ((OrdMap<i8, u8>, usize), isize) {
    let control_index = if by >= 0 {
        cmp::min(control.0.len() as isize, (control.1 as isize).saturating_add(by)) as usize
    } else {
        cmp::max(0, (control.1 as isize) + by) as usize
    };
    let moved = (control_index as isize) - (control.1 as isize);

    ((control.0.clone(), control_index), moved)
}

// get_min_max, find, index_get, index_of, contains, submap
