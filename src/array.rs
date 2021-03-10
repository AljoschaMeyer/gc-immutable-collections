// Implemented as a [join-based](https://en.wikipedia.org/wiki/Join-based_tree_algorithms)
// [2-3 tree](https://en.wikipedia.org/wiki/2%E2%80%933_tree).

use std::borrow::Borrow;
use std::cmp::Ordering::{*};

use gc::{Gc, Trace, custom_trace};
use gc_derive::{Trace, Finalize};

#[derive(Debug, Finalize)]
pub struct Array<V: Trace + 'static>(Option<Gc<Node<V>>>);

unsafe impl<V: Trace + 'static> Trace for Array<V> {
    custom_trace!(this, {
        mark(&this.0);
    });
}

impl<V: Trace + 'static> Clone for Array<V> {
    fn clone(&self) -> Self {
        Array(self.0.clone())
    }
}

#[derive(Debug, Clone, Trace, Finalize)]
enum Node<V: Trace + 'static> {
    N2([(Array<V>, V); 1], Array<V>, usize /* count */),
    N3([(Array<V>, V); 2], Array<V>, usize /* count */),
}
use self::Node::*;

fn n2<V: Clone + Trace + 'static>(l: Array<V>, v: V, r: Array<V>) -> Array<V> {
    let lc = l.count();
    let rc = r.count();
    Array(Some(Gc::new(N2([(l, v)], r, lc + rc + 1))))
}

fn n3<V: Clone + Trace + 'static>(l: Array<V>, lv: V, m: Array<V>, mv: V, r: Array<V>) -> Array<V> {
    let lc = l.count();
    let mc = m.count();
    let rc = r.count();
    Array(Some(Gc::new(N3([(l, lv), (m, mv)], r, lc + mc + rc + 2))))
}

impl<V: Clone + Trace + 'static> Array<V> {
    /// Create a new, empty `Array`.
    ///
    /// Time complexity: O(log(1))
    pub fn new() -> Self {
        Array(None)
    }

    /// Create a new `Array` containing only the given entry.
    ///
    /// Time complexity: O(log(1))
    pub fn singleton(v: V) -> Self {
        n2(Array::new(), v, Array::new())
    }

    fn height_(&self) -> u8 {
        match &self.0 {
            None => 0,
            Some(n) => n.height_(),
        }
    }

    /// Return the number of entries in this `Array`.
    ///
    /// Time complexity: O(1)
    pub fn count(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(n) => n.count(),
        }
    }

    /// Return whether this `Array` contains no entries.
    ///
    /// Time complexity: O(log(1))
    pub fn is_empty(&self) -> bool {
        match &self.0 {
            None => true,
            Some(_) => false,
        }
    }

    /// Return whether this `Array` contains exactly one entry.
    ///
    /// Time complexity: O(log(1))
    pub fn is_singleton(&self) -> bool {
        match &self.0 {
            None => false,
            Some(n) => match n.borrow() {
                N2([(_, _)], _, 1) => true,
                _ => false,
            }
        }
    }
}

impl<V: Clone + Trace + 'static> Array<V> {
    pub fn get(&self, i: usize) -> &V {
        match &self.0 {
            None => panic!(),
            Some(n) => n.get(i),
        }
    }

    pub fn insert(&self, p: usize, v: V) -> Self {
        let (l, r) = self.split(p);
        l.concat(&Self::singleton(v)).concat(&r)
    }

    /// Time complexity: O(log(n))
    pub fn remove(&self, i: usize) -> Self {
        let (l, r) = self.split(i);
        let (_, r) = r.split(i + 1);
        l.concat(&r)
    }

    /// Time complexity: O(log(n))
    pub fn update(&self, i: usize, v: V) -> Self {
        let (l, r) = self.split(i);
        let (_, r) = r.split(i + 1);
        l.concat(&Self::singleton(v)).concat(&r)
    }

    pub fn slice(&self, start: usize, end: usize) -> Self {
        self.slice_to(start).slice_from(end - start)
    }

    pub fn slice_to(&self, p: usize) -> Self {
        let (l, _) = self.split(p);
        l
    }

    pub fn slice_from(&self, p: usize) -> Self {
        let (_, r) = self.split(p);
        r
    }

    pub fn splice(&self, p: usize, other: &Self) -> Self {
        let (l, r) = self.split(p);
        l.concat(other).concat(&r)
    }

    pub fn concat(&self, other: &Self) -> Self {
        if self.count() == 0 {
            other.clone()
        } else if other.count() == 0 {
            self.clone()
        } else {
            let m = other.get(0);
            let r = other.slice_from(1);
            join(self, &m, &r)
        }
    }

    pub fn split(&self, p: usize) -> (Self, Self) {
        match &self.0 {
            None => if p == 0 {
                (Self::new(), Self::new())
            } else {
                panic!("position out of bounds")
            }
            Some(n) => match n.borrow() {
                N2([(l, v)], r, _) => match p.cmp(&l.count()) {
                    Less => {
                        let (ll, lr) = l.split(p);
                        (ll, lr.concat(&Self::singleton(v.clone())).concat(r))
                    }
                    Equal => (l.clone(), Self::singleton(v.clone()).concat(r)),
                    Greater => {
                        let (rl, rr) = r.split(p - (l.count() + 1));
                        (l.concat(&Self::singleton(v.clone())).concat(&rl), rr)
                    }
                }
                N3([(l, lv), (m, mv)], r, _) => match p.cmp(&l.count()) {
                    Less => {
                        let (ll, lr) = l.split(p);
                        (ll, lr.concat(&Self::singleton(lv.clone())).concat(m).concat(&Self::singleton(mv.clone())).concat(r))
                    }
                    Equal => (l.clone(), Self::singleton(lv.clone()).concat(m).concat(&Self::singleton(mv.clone())).concat(r)),
                    Greater => match (p - (l.count() + 1)).cmp(&m.count()) {
                        Less => {
                            let (ml, mr) = m.split(p - (l.count() + 1));
                            (l.concat(&Self::singleton(lv.clone())).concat(&ml), mr.concat(&Self::singleton(mv.clone())).concat(r))
                        }
                        Equal => (l.concat(&Self::singleton(lv.clone())).concat(m), Self::singleton(mv.clone()).concat(r)),
                        Greater => {
                            let (rl, rr) = r.split(p - (l.count() + 1 + m.count() + 1));
                            (l.concat(&Self::singleton(lv.clone())).concat(m).concat(&Self::singleton(mv.clone())).concat(&rl), rr)
                        }
                    }
                }
            }
        }
    }
}

impl<V: Clone + Trace + 'static> Node<V> {
    fn height_(&self) -> u8 {
        match self {
            N2(_, r, _) | N3(_, r, _) => 1 + r.height_(),
        }
    }

    fn count(&self) -> usize {
        match self {
            N2(_, _, c) | N3(_, _, c) => *c,
        }
    }

    pub fn get(&self, i: usize) -> &V {
        match self {
            N2([(l, v)], r, _) => match i.cmp(&l.count()) {
                Less => l.get(i),
                Equal => v,
                Greater => r.get(i - (l.count() + 1)),
            }
            N3([(l, lv), (m, mv)], r, _) => match i.cmp(&l.count()) {
                Less => l.get(i),
                Equal => lv,
                Greater => match (i - (l.count() + 1)).cmp(&m.count()) {
                    Less => m.get(i - (l.count() + 1)),
                    Equal => mv,
                    Greater => r.get(i - (l.count() + 1 + m.count() + 1))
                }
            }
        }
    }
}

fn join<V: Clone + Trace + 'static>(lesser: &Array<V>, v: &V, greater: &Array<V>) -> Array<V> {
    let lesser_height = lesser.height_();
    let greater_height = greater.height_();

    match lesser_height.cmp(&greater_height) {
        Less => match join_lesser_smaller(lesser, v, greater, greater_height - lesser_height) {
            Insert::Done(done_n) => done_n,
            Insert::Up(l, v, r) => n2(
                l.clone(),
                v.clone(),
                r.clone(),
            ),
        }
        Equal => n2(
            lesser.clone(),
            v.clone(),
            greater.clone(),
        ),
        Greater => match join_greater_smaller(lesser, v, greater, lesser_height - greater_height) {
            Insert::Done(done_n) => done_n,
            Insert::Up(l, v, r) => n2(
                l.clone(),
                v.clone(),
                r.clone(),
            ),
        }
    }
}

// traverse left spine of greater node for h_diff, then merge
fn join_lesser_smaller<'a, V: Clone + Trace + 'static>(
    lesser: &Array<V>, v: &'a V, greater: &'a Array<V>, h_diff: u8
) -> Insert<'a, V> {
    if h_diff == 0 {
        Insert::Up(lesser.clone(), v, greater.clone())
    } else {
        match &greater.0 {
            None => unreachable!(),
            Some(n) => match n.borrow() {
                N2([(gl, gv)], gr, _) => {
                    n2_handle_insert_l(
                        join_lesser_smaller(lesser, v, gl, h_diff - 1), gv, gr
                    )
                }
                N3([(gl, glv), (gm, gmv)], gr, _) => {
                    n3_handle_insert_l(
                        join_lesser_smaller(
                            lesser, v, gl, h_diff - 1
                        ),
                        glv, gm, gmv, gr,
                    )
                }
            }
        }
    }
}

fn join_greater_smaller<'a, V: Clone + Trace + 'static>(
    lesser: &'a Array<V>, v: &'a V, greater: &Array<V>, h_diff: u8
) -> Insert<'a, V> {
    if h_diff == 0 {
        Insert::Up(lesser.clone(), v, greater.clone())
    } else {
        match &lesser.0 {
            None => unreachable!(),
            Some(n) => match n.borrow() {
                N2([(ll, lv)], lr, _) => {
                    n2_handle_insert_r(
                        ll, lv, join_greater_smaller(lr, v, greater, h_diff - 1)
                    )
                }
                N3([(ll, llv), (lm, lmv)], lr, _) => {
                    n3_handle_insert_r(
                        ll, llv, lm, lmv,
                        join_greater_smaller(
                            lr, v, greater, h_diff - 1
                        ),
                    )
                }
            }
        }
    }
}

enum Insert<'a, V: Trace + 'static> {
    Done(Array<V>),
    Up(Array<V>, &'a V, Array<V>),
}

fn n2_handle_insert_l<'a, V>(insert_l: Insert<V>, v: &'a V, r: &Array<V>) -> Insert<'a, V>
    where V: Clone + Trace + 'static {
    match insert_l {
        Insert::Done(done_n) => Insert::Done(n2(
            done_n,
            v.clone(),
            r.clone(),
        )),
        Insert::Up(up_l, up_v, up_r) => Insert::Done(n3(
            up_l,
            /**/ up_v.clone(),
            up_r,
            v.clone(),
            r.clone(),
        )),
    }
}

fn n2_handle_insert_r<'a, V>(l: &Array<V>, v: &'a V, insert_r: Insert<'a, V>) -> Insert<'a, V>
    where V: Clone + Trace + 'static {
    match insert_r {
        Insert::Done(done_n) => Insert::Done(n2(
            l.clone(),
            v.clone(),
            done_n,
        )),
        Insert::Up(up_l, up_v, up_r) => Insert::Done(n3(
            l.clone(),
            v.clone(),
            up_l,
            /**/ up_v.clone(),
            up_r,
        )),
    }
}

fn n3_handle_insert_l<'a, V>(
    insert_l: Insert<'a, V>, lv: &'a V, m: &Array<V>, rv: &'a V, r: &Array<V>
) -> Insert<'a, V> where V: Clone + Trace + 'static {
    match insert_l {
        Insert::Done(done_n) => Insert::Done(n3(
            done_n,
            /**/ lv.clone(),
            m.clone(),
            /**/ rv.clone(),
            r.clone(),
        )),
        Insert::Up(up_l, up_v, up_r) => Insert::Up(
                n2(up_l, up_v.clone(), up_r),
                /**/ lv,
                n2(m.clone(), rv.clone(), r.clone()),
            ),
    }
}

// fn n3_handle_insert_m<'a, V>(
//     l: &Array<V>, lv: &'a V, insert_m: Insert<'a, V>, rv: &'a V, r: &Array<V>
// ) -> Insert<'a, V> where K: Ord + Clone, V: Clone {
//     match insert_m {
//         Insert::Done(done_n) => Insert::Done(n3(
//             l.clone(),
//             /**/ lv.clone(),
//             done_n,
//             /**/ rv.clone(),
//             r.clone(),
//         )),
//         Insert::Up(up_l, up_v, up_r) => Insert::Up(
//             n2(l.clone(), lv.clone(), up_l),
//             /**/ up_v,
//             n2(up_r.clone(), rv.clone(), r.clone()),
//         ),
//     }
// }

fn n3_handle_insert_r<'a, V>(
    l: &Array<V>, lv: &'a V, m: &Array<V>, rv: &'a V, insert_r: Insert<'a, V>
) -> Insert<'a, V> where V: Clone + Trace + 'static {
    match insert_r {
        Insert::Done(done_n) => Insert::Done(n3(
            l.clone(),
            /**/ lv.clone(),
            m.clone(),
            /**/ rv.clone(),
            done_n,
        )),
        Insert::Up(up_l, up_v, up_r) => Insert::Up(
            n2(l.clone(), lv.clone(), m.clone()),
            /**/ rv,
            n2(up_l, up_v.clone(), up_r),
        ),
    }
}




// impl<K: PartialEq + Clone + Trace + 'static, V: PartialEq + Clone + Trace + 'static> PartialEq for Array<V> {
//     fn eq(&self, rhs: &Self) -> bool {
//         match (&self.0, &rhs.0) {
//             (None, None) => return true,
//             (Some(_), None) | (None, Some(_)) => return false,
//             (Some(n1), Some(n2)) if  Gc::ptr_eq(n1, n2) => return true,
//             _ => {}
//         };
//
//         let mut p1 = self.producer_min();
//         let mut p2 = rhs.producer_min();
//
//         loop {
//             match (step_next(&mut p1.0), step_next(&mut p2.0)) {
//                 (None, None) => return true,
//                 (Some(_), None) | (None, Some(_)) => return false,
//                 (Some((xk, xv)), Some((yk, yv))) => {
//                     if xk != yk || xv != yv {
//                         return false;
//                     }
//                 }
//             }
//         }
//     }
// }
//
// impl<K: PartialEq + Clone + Trace + 'static, V: PartialEq + Clone + Trace + 'static> Eq for Array<V> {}
//
// impl<K: PartialOrd + Clone + Trace + 'static, V: PartialOrd + Clone + Trace + 'static> PartialOrd for Array<V> {
//     fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
//         match (&self.0, &rhs.0) {
//             (None, None) => return Some(Ordering::Equal),
//             (Some(_), None) => return Some(Ordering::Greater),
//             (None, Some(_)) => return Some(Ordering::Less),
//             (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return Some(Ordering::Equal),
//             _ => {}
//         };
//
//         let mut p1 = self.producer_min();
//         let mut p2 = rhs.producer_min();
//
//         loop {
//             match (step_next(&mut p1.0), step_next(&mut p2.0)) {
//                 (None, None) => return Some(Ordering::Equal),
//                 (Some(_), None) => return Some(Ordering::Greater),
//                 (None, Some(_)) => return Some(Ordering::Less),
//                 (Some((xk, xv)), Some((yk, yv))) => {
//                     match xk.partial_cmp(&yk) {
//                         None => return None,
//                         Some(Ordering::Less) => return Some(Ordering::Less),
//                         Some(Ordering::Greater) => return Some(Ordering::Greater),
//                         Some(Ordering::Equal) => {
//                             match xv.partial_cmp(&yv) {
//                                 None => return None,
//                                 Some(Ordering::Less) => return Some(Ordering::Less),
//                                 Some(Ordering::Greater) => return Some(Ordering::Greater),
//                                 Some(Ordering::Equal) => {}
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
//
//     fn lt(&self, rhs: &Self) -> bool {
//         match (&self.0, &rhs.0) {
//             (None, None) => return false,
//             (Some(_), None) => return false,
//             (None, Some(_)) => return true,
//             (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return false,
//             _ => {}
//         };
//
//         let mut p1 = self.producer_min();
//         let mut p2 = rhs.producer_min();
//
//         loop {
//             match (step_next(&mut p1.0), step_next(&mut p2.0)) {
//                 (None, None) => return false,
//                 (Some(_), None) => return false,
//                 (None, Some(_)) => return true,
//                 (Some((xk, xv)), Some((yk, yv))) => {
//                     match xk.partial_cmp(&yk) {
//                         None => return false,
//                         Some(Ordering::Less) => return true,
//                         Some(Ordering::Greater) => return false,
//                         Some(Ordering::Equal) => {
//                             match xv.partial_cmp(&yv) {
//                                 None => return false,
//                                 Some(Ordering::Less) => return true,
//                                 Some(Ordering::Greater) => return false,
//                                 Some(Ordering::Equal) => {}
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
//
//     fn le(&self, rhs: &Self) -> bool {
//         match (&self.0, &rhs.0) {
//             (None, None) => return true,
//             (Some(_), None) => return false,
//             (None, Some(_)) => return true,
//             (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return true,
//             _ => {}
//         };
//
//         let mut p1 = self.producer_min();
//         let mut p2 = rhs.producer_min();
//
//         loop {
//             match (step_next(&mut p1.0), step_next(&mut p2.0)) {
//                 (None, None) => return true,
//                 (Some(_), None) => return false,
//                 (None, Some(_)) => return true,
//                 (Some((xk, xv)), Some((yk, yv))) => {
//                     match xk.partial_cmp(&yk) {
//                         None => return false,
//                         Some(Ordering::Less) => return true,
//                         Some(Ordering::Greater) => return false,
//                         Some(Ordering::Equal) => {
//                             match xv.partial_cmp(&yv) {
//                                 None => return false,
//                                 Some(Ordering::Less) => return true,
//                                 Some(Ordering::Greater) => return false,
//                                 Some(Ordering::Equal) => {}
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
//
//     fn ge(&self, rhs: &Self) -> bool {
//         match (&self.0, &rhs.0) {
//             (None, None) => return true,
//             (Some(_), None) => return true,
//             (None, Some(_)) => return false,
//             (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return true,
//             _ => {}
//         };
//
//         let mut p1 = self.producer_min();
//         let mut p2 = rhs.producer_min();
//
//         loop {
//             match (step_next(&mut p1.0), step_next(&mut p2.0)) {
//                 (None, None) => return true,
//                 (Some(_), None) => return true,
//                 (None, Some(_)) => return false,
//                 (Some((xk, xv)), Some((yk, yv))) => {
//                     match xk.partial_cmp(&yk) {
//                         None => return false,
//                         Some(Ordering::Less) => return false,
//                         Some(Ordering::Greater) => return true,
//                         Some(Ordering::Equal) => {
//                             match xv.partial_cmp(&yv) {
//                                 None => return false,
//                                 Some(Ordering::Less) => return false,
//                                 Some(Ordering::Greater) => return true,
//                                 Some(Ordering::Equal) => {}
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
//
//     fn gt(&self, rhs: &Self) -> bool {
//         match (&self.0, &rhs.0) {
//             (None, None) => return false,
//             (Some(_), None) => return true,
//             (None, Some(_)) => return false,
//             (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return false,
//             _ => {}
//         };
//
//         let mut p1 = self.producer_min();
//         let mut p2 = rhs.producer_min();
//
//         loop {
//             match (step_next(&mut p1.0), step_next(&mut p2.0)) {
//                 (None, None) => return false,
//                 (Some(_), None) => return true,
//                 (None, Some(_)) => return false,
//                 (Some((xk, xv)), Some((yk, yv))) => {
//                     match xk.partial_cmp(&yk) {
//                         None => return false,
//                         Some(Ordering::Less) => return false,
//                         Some(Ordering::Greater) => return true,
//                         Some(Ordering::Equal) => {
//                             match xv.partial_cmp(&yv) {
//                                 None => return false,
//                                 Some(Ordering::Less) => return false,
//                                 Some(Ordering::Greater) => return true,
//                                 Some(Ordering::Equal) => {}
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
// }
//
// impl<V: Ord + Clone + Trace + 'static> Ord for Array<V> {
//     fn cmp(&self, rhs: &Self) -> Ordering {
//         self.partial_cmp(rhs).unwrap()
//     }
// }
//
// pub struct Producer<V: Trace + 'static>(Vec<(Array<V>, u8)>);
//
// fn step_next<K: Clone + Trace + 'static, V: Clone + Trace + 'static>(positions: &mut Vec<(Array<V>, u8)>) -> Option<(V)> {
//     let len = positions.len();
//     let p = positions[len - 1].clone();
//
//     match &(p.0).0 {
//         None => None,
//         Some(n) => match (n.borrow(), p.1) {
//             (N2(..), 3..=5) | (N3(..), 5) if len == 1 => None,
//             (N2(..), 3..=5) | (N3(..), 5) => {
//                 positions.pop();
//                 step_next(positions)
//             }
//             (N2([(l, _, _)], _, _), 0) => {
//                 positions[len - 1].1 = 1;
//                 positions.push((l.clone(), 0));
//                 step_next(positions)
//             }
//             (N2([(_, v)], _, _), 1) => {
//                 positions[len - 1].1 = 2;
//                 Some((k.clone(), v.clone()))
//             }
//             (N2(_, r, _), 2) => {
//                 positions[len - 1].1 = 3;
//                 positions.push((r.clone(), 0));
//                 step_next(positions)
//             }
//             (N3([(l, _, _), _], _, _), 0) => {
//                 positions[len - 1].1 = 1;
//                 positions.push((l.clone(), 0));
//                 step_next(positions)
//             }
//             (N3([(_, lv), _], _, _), 1) => {
//                 positions[len - 1].1 = 2;
//                 Some((lv.clone()))
//             }
//             (N3([_, (m, _, _)], _, _), 2) => {
//                 positions[len - 1].1 = 3;
//                 positions.push((m.clone(), 0));
//                 step_next(positions)
//             }
//             (N3([_, (_, mk, mv)], _, _), 3) => {
//                 positions[len - 1].1 = 4;
//                 Some((mk.clone(), mv.clone()))
//             }
//             (N3(_, r, _), 4) => {
//                 positions[len - 1].1 = 5;
//                 positions.push((r.clone(), 0));
//                 step_next(positions)
//             }
//             (N2(..), 6..=255) | (N3(..), 6..=255) => unreachable!(),
//         }
//     }
// }
//
// // fn step_prev<K: Clone, V: Clone>(positions: &mut Vec<(Array<V>, u8)>) -> Option<(V)> {
// //     let len = positions.len();
// //     let p = positions[len - 1].clone();
// //
// //     match &(p.0).0 {
// //         None => None,
// //         Some(n) => match (n.borrow(), p.1) {
// //             (_, 0) if len == 1 => None,
// //             (_, 0) => {
// //                 positions.pop();
// //                 step_prev(positions)
// //             }
// //             (N2(_, r, _), 3..=5) => {
// //                 positions[len - 1].1 = 2;
// //                 positions.push((r.clone(), 5));
// //                 step_prev(positions)
// //             }
// //             (N2([(_, v)], _, _), 2) => {
// //                 positions[len - 1].1 = 1;
// //                 Some((k.clone(), v.clone()))
// //             }
// //             (N2([(l, _, _)], _, _), 1) => {
// //                 positions[len - 1].1 = 0;
// //                 positions.push((l.clone(), 5));
// //                 step_prev(positions)
// //             }
// //             (N3(_, r, _), 5) => {
// //                 positions[len - 1].1 = 4;
// //                 positions.push((r.clone(), 5));
// //                 step_prev(positions)
// //             }
// //             (N3([_, (_, mk, mv)], _, _), 4) => {
// //                 positions[len - 1].1 = 3;
// //                 Some((mk.clone(), mv.clone()))
// //             }
// //             (N3([_, (m, _, _)], _, _), 3) => {
// //                 positions[len - 1].1 = 2;
// //                 positions.push((m.clone(), 5));
// //                 step_prev(positions)
// //             }
// //             (N3([(_, lv), _], _, _), 2) => {
// //                 positions[len - 1].1 = 1;
// //                 Some((lv.clone()))
// //             }
// //             (N3([(l, _, _), _], _, _), 1) => {
// //                 positions[len - 1].1 = 0;
// //                 positions.push((l.clone(), 5));
// //                 step_prev(positions)
// //             }
// //             (N2(..), 6..=255) | (N3(..), 6..=255) => unreachable!(),
// //         }
// //     }
// // }
//
// // impl<K: Clone, V: Clone> Iterator for Producer<V> {
// //     type Item = (V);
// //
// //     fn next(&mut self) -> Option<Self::Item> {
// //         step_next(&mut self.0)
// //     }
// // }
//
//
//
//
//
//
//
// // //////////////////////////////////////// debug /testing stuff
// //
// // pub fn map_to_vec(m: &Array, out: &mut Vec<(Value, Foo)>) {
// //     node_to_vec(&m.0, out)
// // }
// //
// // fn node_to_vec(n: &Node, out: &mut Vec<(Value, Foo)>) {
// //     match n {
// //         Leaf => {},
// //         N2(n) => {
// //             let (ref l, ref k, ref v, ref r, _) = &(**n);
// //             node_to_vec(l, out);
// //             out.push((k.clone(), v.clone()));
// //             node_to_vec(r, out);
// //         }
// //         N3(n) => {
// //             let (ref l, ref lk, ref lv, ref m, ref ref rv, ref r, _) = &(**n);
// //             node_to_vec(l, out);
// //             out.push((lv.clone()));
// //             node_to_vec(m, out);
// //             out.push((rv.clone()));
// //             node_to_vec(r, out);
// //         }
// //     }
// // }
// //
// //
// // use std::collections::BTreeArray;
// //
// // // fn fuzzy(data: &[u8]) {
// // //     // Foo
// // //     let mut control = BTreeArray::new();
// // //     let mut m = Array::new();
// // //
// // //     for b in data {
// // //         // m = m.insert(Value::int(*b as i64), Foo);
// // //         // control.insert(Value::int(*b as i64), Foo);
// // //
// // //         match *b {
// // //             0...63 => {
// // //                 m = m.insert(Value::int((b & 0b0011_1111) as i64), Foo);
// // //                 control.insert(Value::int((b & 0b0011_1111) as i64), Foo);
// // //                 println!("insert {:?}", b & 0b0011_1111);
// // //             }
// // //             64...127 => {
// // //                 m = m.remove(&Value::int((b & 0b0011_1111) as i64));
// // //                 control.remove(&Value::int((b & 0b0011_1111) as i64));
// // //                 println!("remove {:?}", b & 0b0011_1111);
// // //             }
// // //             128...191 => {
// // //                 let key = Value::int((b & 0b0011_1111) as i64);
// // //                 let (l, _) = m.split(&key);
// // //                 println!("split-l {:?}", b & 0b0011_1111);
// // //                 println!("splitl: ({:?}, {:?}, _)", l, k);
// // //
// // //                 // m = l;
// // //                 match k {
// // //                     None => m = l,
// // //                     Some(v) => m = l.insert(k.clone(), v.clone()),
// // //                 }
// // //
// // //                 let mut new_control = BTreeArray::new();
// // //                 for v in control.iter() {
// // //                     // if k < &key {
// // //                     //     new_control.insert(k.clone(), v.clone());
// // //                     // }
// // //                     if k <= &key {
// // //                         new_control.insert(k.clone(), v.clone());
// // //                     }
// // //                 }
// // //                 control = new_control;
// // //             }
// // //             192...255 => {
// // //                 let key = Value::int((b & 0b0011_1111) as i64);
// // //                 let (_, r) = m.split(&key);
// // //                 println!("{:?}", m);
// // //                 println!("split-r {:?}", b & 0b0011_1111);
// // //                 println!("splitr: (_, {:?}, {:?})", r);
// // //
// // //                 // m = r;
// // //                 match k {
// // //                     None => m = r,
// // //                     Some(v) => m = r.insert(k.clone(), v.clone()),
// // //                 }
// // //
// // //                 let mut new_control = BTreeArray::new();
// // //                 for v in control.iter() {
// // //                     if k >= &key {
// // //                         new_control.insert(k.clone(), v.clone());
// // //                     }
// // //                     // if k > &key {
// // //                     //     new_control.insert(k.clone(), v.clone());
// // //                     // }
// // //                 }
// // //                 control = new_control;
// // //             }
// // //         }
// // //     }
// // //
// // //     let mut out = vec![];
// // //     map_to_vec(&m, &mut out);
// // //     let out_control: Vec<(Value, Foo)> = control.into_iter().collect();
// // //
// // //     if out != out_control {
// // //         println!("{:?}", "-----");
// // //         println!("{:?}", out_control);
// // //         println!("{:?}", out);
// // //     }
// // //
// // //     assert!(out == out_control);
// // // }
// //
// // fn fuzzy_cursor(data: &[u8]) {
// //     let mut control = BTreeArray::new();
// //     let mut m = Array::new();
// //     let half = data.len() / 2;
// //
// //     for b in &data[..half] {
// //         match *b {
// //             0...63 => {
// //                 m = m.insert(Value::int((b & 0b0011_1111) as i64), Foo);
// //                 control.insert(Value::int((b & 0b0011_1111) as i64), Foo);
// //             }
// //             64...127 => {
// //                 m = m.remove(&Value::int((b & 0b0011_1111) as i64));
// //                 control.remove(&Value::int((b & 0b0011_1111) as i64));
// //             }
// //             128...191 => {
// //                 let key = Value::int((b & 0b0011_1111) as i64);
// //                 let (l, _) = m.split(&key);
// //
// //                 match k {
// //                     None => m = l,
// //                     Some(v) => m = l.insert(k.clone(), v.clone()),
// //                 }
// //
// //                 let mut new_control = BTreeArray::new();
// //                 for v in control.iter() {
// //                     if k <= &key {
// //                         new_control.insert(k.clone(), v.clone());
// //                     }
// //                 }
// //                 control = new_control;
// //             }
// //             192...255 => {
// //                 let key = Value::int((b & 0b0011_1111) as i64);
// //                 let (_, r) = m.split(&key);
// //
// //                 match k {
// //                     None => m = r,
// //                     Some(v) => m = r.insert(k.clone(), v.clone()),
// //                 }
// //
// //                 let mut new_control = BTreeArray::new();
// //                 for v in control.iter() {
// //                     if k >= &key {
// //                         new_control.insert(k.clone(), v.clone());
// //                     }
// //                 }
// //                 control = new_control;
// //             }
// //         }
// //     }
// //
// //     let out_control: Vec<(Value, Foo)> = control.into_iter().collect();
// //     let len = out_control.len();
// //     if len == 0 {
// //         return;
// //     } else {
// //         let (mut cursor, mut control_index) = if data[0] % 2 == 0 {
// //             (m.cursor_min().unwrap(), 0)
// //         } else {
// //             (m.cursor_max().unwrap(), len - 1)
// //         };
// //         let mut skip = false;
// //
// //         println!("Initial: ({:?}, {:?})\n===", out_control, control_index);
// //
// //         for b in &data[half..] {
// //             println!("control_index: {:?}", control_index);
// //             println!("{:?}", cursor);
// //             println!("---");
// //             if skip {
// //                 assert!(control_index == len || control_index == 0)
// //             } else {
// //                 match cursor.current() {
// //                     None => assert!(control_index == len),
// //                     Some(v) => assert!(v == out_control[control_index]),
// //                 }
// //             }
// //
// //             if b % 2 == 0 {
// //                 skip = !cursor.next();
// //                 if control_index != len {
// //                     control_index += 1;
// //                 }
// //             } else {
// //                 skip = !cursor.prev();
// //                 if control_index != 0 {
// //                     control_index -= 1;
// //                 }
// //             }
// //         }
// //     }
// // }
// //
// // fn fuzzy_bulk(data: &[u8]) {
// //     let mut control = BTreeArray::new();
// //     let mut control2 = BTreeArray::new();
// //     let mut m = Array::new();
// //     let mut n = Array::new();
// //     let half = data.len() / 2;
// //
// //     if data.len() == 0 {
// //         return;
// //     }
// //
// //     for b in &data[..half] {
// //         match *b {
// //             0...127 => {
// //                 m = m.insert(Value::int((b & 0b0111_1111) as i64), Foo);
// //                 control.insert(Value::int((b & 0b0111_1111) as i64), Foo);
// //             }
// //             128...255 => {
// //                 m = m.remove(&Value::int((b & 0b0111_1111) as i64));
// //                 control.remove(&Value::int((b & 0b0111_1111) as i64));
// //             }
// //         }
// //     }
// //
// //     for b in &data[half..] {
// //         match *b {
// //             0...127 => {
// //                 n = n.insert(Value::int((b & 0b0111_1111) as i64), Foo);
// //                 control2.insert(Value::int((b & 0b0111_1111) as i64), Foo);
// //             }
// //             128...255 => {
// //                 n = n.remove(&Value::int((b & 0b0111_1111) as i64));
// //                 control2.remove(&Value::int((b & 0b0111_1111) as i64));
// //             }
// //         }
// //     }
// //
// //     let mut out = vec![];
// //     let out_control: Vec<(Value, Foo)>;
// //
// //     match data[0] {
// //         _ => {
// //             let union_ = m.union(&n);
// //             map_to_vec(&union_, &mut out);
// //
// //             let mut tmp = control2.clone();
// //             for v in control.into_iter() {
// //                 tmp.insertv;
// //             }
// //             out_control = tmp.into_iter().collect();
// //         }
// //     }
// //
// //     if out != out_control {
// //         println!("{:?}", out_control);
// //         println!("{:?}", out);
// //     }
// //
// //     assert!(out == out_control);
// // }
// //
// // // #[test]
// // // fn test_fuzzy_bulk() {
// // //     fuzzy_bulk(&[0, 0, 0, 1]);
// // // }
// // //
// // // #[test]
// // // fn test_fuzzy_cursor() {
// // //     fuzzy_cursor(&[0x1f,0x0,0x1,0x32,0x0,0x1d,0xff,0xff]);
// // //     fuzzy(&[0x10,0x1,0x0,0x23]);
// // //     fuzzy(&[0xca,0x31,0xd1,0x0,0x6b]);
// // //     fuzzy(&[0x3b,0x1,0x0,0x1,0x10]);
// // //     fuzzy(&[0x2a,0x2d,0xa,0x1,0x0,0x80]);
// // //     fuzzy(&[0x1,0xa,0xa]);
// // // }










#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;
    use proptest_derive::Arbitrary;
    use im::Vector;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ArrayConstruction {
        New,
        Singleton(u32),
        Insert(Box<Self>, u32),
        Remove(Box<Self>, usize),
        Update(Box<Self>, usize, u32),
        Slice(Box<Self>, usize, usize),
        SliceTo(Box<Self>, usize),
        SliceFrom(Box<Self>, usize),
        Splice(Box<Self>, usize, Box<Self>),
        Split(Box<Self>, usize),
        Concat(Box<Self>, Box<Self>),
    }

    impl ArrayConstruction {
        fn concat(a: Self, b: Self) -> Self {
            Self::Concat(Box::new(a), Box::new(b))
        }

        fn construct_array(&self) -> Array<u32> {
            match self {
                Self::New => Array::new(),
                Self::Singleton(v) => Array::singleton(*v),
                Self::Concat(a, b) => Self::construct_array(a).concat(&Self::construct_array(b)),
                _ => unimplemented!(),
            }
        }

        fn construct_control(&self) -> Vector<u32> {
            match self {
                Self::New => Vector::new(),
                Self::Singleton(v) => Vector::unit(*v),
                Self::Concat(a, b) => {
                    let mut r = Self::construct_control(a);
                    r.append(Self::construct_control(b));
                    r
                }
                _ => unimplemented!(),
            }
        }
    }

    fn arb_array_construction() -> impl Strategy<Value = ArrayConstruction> {
        let leaf = prop_oneof![
            Just(ArrayConstruction::New),
            any::<u32>().prop_map(ArrayConstruction::Singleton),
        ];
        // leaf
        leaf.prop_recursive(
            16, // 8 levels deep
            128, // Shoot for maximum size of 256 nodes
            10, // We put up to 10 items per collection
            |inner| prop_oneof![
                // (inner.clone(), any::<usize>()).prop_map(|(a, p)| ArrayConstruction::Split(Box::new(a), p /* TODO modulo count + 1 */)),
                (inner.clone(), inner).prop_map(|(a, b)| ArrayConstruction::concat(a, b)),
            ])
    }

    proptest! {
        #[test]
        fn test_count(c in arb_array_construction()) {
            let arr = c.construct_array();
            let control = c.construct_control();

            if arr.count() != control.len() {
                println!("----------------\ncount was {:?} rather than {:?}\nExpected: {:?}\n\n{:?}\n\n\n", arr.count(), control.len(), control, arr);
                panic!()
            }
        }
    }
}
