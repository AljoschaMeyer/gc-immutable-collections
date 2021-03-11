// Implemented as a [join-based](https://en.wikipedia.org/wiki/Join-based_tree_algorithms)
// [2-3 tree](https://en.wikipedia.org/wiki/2%E2%80%933_tree).

use std::borrow::Borrow;
use std::cmp::Ordering::{self, *};

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

impl<V: PartialEq + Clone + Trace + 'static> PartialEq for Array<V> {
    fn eq(&self, rhs: &Self) -> bool {
        match (&self.0, &rhs.0) {
            (None, None) => return true,
            (Some(_), None) | (None, Some(_)) => return false,
            (Some(n1), Some(n2)) if  Gc::ptr_eq(n1, n2) => return true,
            _ => {}
        };

        let mut p1 = Focus::new(self, 0);
        let mut p2 = Focus::new(rhs, 0);

        loop {
            match (p1.get_relative(0), p2.get_relative(0)) {
                (None, None) => return true,
                (Some(_), None) | (None, Some(_)) => return false,
                (Some(xv), Some(yv)) => {
                    if xv != yv {
                        return false;
                    }
                    p1.refocus(1);
                    p2.refocus(1);
                }
            }
        }
    }
}

impl<V: PartialEq + Clone + Trace + 'static> Eq for Array<V> {}

impl<V: PartialOrd + Clone + Trace + 'static> PartialOrd for Array<V> {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        match (&self.0, &rhs.0) {
            (None, None) => return Some(Ordering::Equal),
            (Some(_), None) => return Some(Ordering::Greater),
            (None, Some(_)) => return Some(Ordering::Less),
            (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return Some(Ordering::Equal),
            _ => {}
        };

        let mut p1 = Focus::new(self, 0);
        let mut p2 = Focus::new(rhs, 0);

        loop {
            match (p1.get_relative(0), p2.get_relative(0)) {
                (None, None) => return Some(Ordering::Equal),
                (Some(_), None) => return Some(Ordering::Greater),
                (None, Some(_)) => return Some(Ordering::Less),
                (Some(xv), Some(yv)) => {
                    match xv.partial_cmp(&yv) {
                        None => return None,
                        Some(Ordering::Less) => return Some(Ordering::Less),
                        Some(Ordering::Greater) => return Some(Ordering::Greater),
                        Some(Ordering::Equal) => {
                            p1.refocus(1);
                            p2.refocus(1);
                        }
                    }
                }
            }
        }
    }

    fn lt(&self, rhs: &Self) -> bool {
        match (&self.0, &rhs.0) {
            (None, None) => return false,
            (Some(_), None) => return false,
            (None, Some(_)) => return true,
            (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return false,
            _ => {}
        };

        let mut p1 = Focus::new(self, 0);
        let mut p2 = Focus::new(rhs, 0);

        loop {
            match (p1.get_relative(0), p2.get_relative(0)) {
                (None, None) => return false,
                (Some(_), None) => return false,
                (None, Some(_)) => return true,
                (Some(xv), Some(yv)) => {
                    match xv.partial_cmp(&yv) {
                        None => return false,
                        Some(Ordering::Less) => return true,
                        Some(Ordering::Greater) => return false,
                        Some(Ordering::Equal) => {
                            p1.refocus(1);
                            p2.refocus(1);
                        }
                    }
                }
            }
        }
    }

    fn le(&self, rhs: &Self) -> bool {
        match (&self.0, &rhs.0) {
            (None, None) => return true,
            (Some(_), None) => return false,
            (None, Some(_)) => return true,
            (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return true,
            _ => {}
        };

        let mut p1 = Focus::new(self, 0);
        let mut p2 = Focus::new(rhs, 0);

        loop {
            match (p1.get_relative(0), p2.get_relative(0)) {
                (None, None) => return true,
                (Some(_), None) => return false,
                (None, Some(_)) => return true,
                (Some(xv), Some(yv)) => {
                    match xv.partial_cmp(&yv) {
                        None => return false,
                        Some(Ordering::Less) => return true,
                        Some(Ordering::Greater) => return false,
                        Some(Ordering::Equal) => {
                            p1.refocus(1);
                            p2.refocus(1);
                        }
                    }
                }
            }
        }
    }

    fn ge(&self, rhs: &Self) -> bool {
        match (&self.0, &rhs.0) {
            (None, None) => return true,
            (Some(_), None) => return true,
            (None, Some(_)) => return false,
            (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return true,
            _ => {}
        };

        let mut p1 = Focus::new(self, 0);
        let mut p2 = Focus::new(rhs, 0);

        loop {
            match (p1.get_relative(0), p2.get_relative(0)) {
                (None, None) => return true,
                (Some(_), None) => return true,
                (None, Some(_)) => return false,
                (Some(xv), Some(yv)) => {
                    match xv.partial_cmp(&yv) {
                        None => return false,
                        Some(Ordering::Less) => return false,
                        Some(Ordering::Greater) => return true,
                        Some(Ordering::Equal) => {
                            p1.refocus(1);
                            p2.refocus(1);
                        }
                    }
                }
            }
        }
    }

    fn gt(&self, rhs: &Self) -> bool {
        match (&self.0, &rhs.0) {
            (None, None) => return false,
            (Some(_), None) => return true,
            (None, Some(_)) => return false,
            (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return false,
            _ => {}
        };

        let mut p1 = Focus::new(self, 0);
        let mut p2 = Focus::new(rhs, 0);

        loop {
            match (p1.get_relative(0), p2.get_relative(0)) {
                (None, None) => return false,
                (Some(_), None) => return true,
                (None, Some(_)) => return false,
                (Some(xv), Some(yv)) => {
                    match xv.partial_cmp(&yv) {
                        None => return false,
                        Some(Ordering::Less) => return false,
                        Some(Ordering::Greater) => return true,
                        Some(Ordering::Equal) => {
                            p1.refocus(1);
                            p2.refocus(1);
                        }
                    }
                }
            }
        }
    }
}

impl<V: Ord + Clone + Trace + 'static> Ord for Array<V> {
    fn cmp(&self, rhs: &Self) -> Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}

#[derive(Debug)]
pub struct Focus<V: Trace + 'static>(Vec<(Array<V>, u8)>);

impl<V: Trace + Clone +  'static> Focus<V> {
    pub fn new(arr: &Array<V>, p: usize) -> Self {
        let mut v = vec![];
        focus_new(arr, p, &mut v);
        Self(v)
    }

    pub fn get_relative(&self, i: isize) -> Option<&V> {
        let mut h = self.0.len();
        let mut subarr_p = 0;

        while h > 0 {
            let (arr, node_position) = &self.0[h - 1];
            subarr_p = subarr_position(arr, *node_position, subarr_p);

            let subarr_i = (subarr_p as isize) + i;
            if 0 <= subarr_i && subarr_i < (arr.count() as isize) {
                return Some(arr.get(subarr_i as usize));
            } else {
                h -= 1;
            }
        }

        return None;
    }

    pub fn refocus(&mut self, by: isize) -> isize {
        if self.0.is_empty() {
            return 0;
        }

        let mut subarr_p = 0;

        loop {
            let (arr, node_position) = &self.0.pop().unwrap();
            subarr_p = subarr_position(arr, *node_position, subarr_p);

            let subarr_i = (subarr_p as isize) + by;
            if 0 <= subarr_i && subarr_i < (arr.count() as isize) {
                focus_new(arr, subarr_i as usize, &mut self.0);
                return by;
            }

            if self.0.is_empty() {
                if by <= 0 {
                    focus_new(arr, 0, &mut self.0);
                    return -(subarr_p as isize);
                } else {
                    focus_new(arr, arr.count(), &mut self.0);
                    return (self.0[0].0.count() - subarr_p) as isize;
                }
            }
        }
    }

    // fn next(&mut self) -> Option<&V> {
    //     let r = self.get_relative(0);
    //     let tmp = r.clone();
    //     self.refocus(1);
    //     tmp
    // }
}

fn focus_new<V: Trace + Clone + 'static>(arr: &Array<V>, p: usize, vs: &mut Vec<(Array<V>, u8)>) {
    match &arr.0 {
        None => return,
        Some(n) => match n.borrow() {
            N2([(l, _)], r, _) => match p.cmp(&l.count()) {
                Less => {
                    vs.push((arr.clone(), 0));
                    focus_new(l, p, vs)
                }
                Equal => vs.push((arr.clone(), 1)),
                Greater => {
                    vs.push((arr.clone(), 2));
                    focus_new(r, p - (l.count() + 1), vs)
                }
            }
            N3([(l, _), (m, _)], r, _) => match p.cmp(&l.count()) {
                Less => {
                    vs.push((arr.clone(), 0));
                    focus_new(l, p, vs)
                }
                Equal => vs.push((arr.clone(), 1)),
                Greater => match (p - (l.count() + 1)).cmp(&m.count()) {
                    Less => {
                        vs.push((arr.clone(), 2));
                        focus_new(r, p - (l.count() + 1), vs)
                    }
                    Equal => vs.push((arr.clone(), 3)),
                    Greater => {
                        vs.push((arr.clone(), 4));
                        focus_new(r, p - (l.count() + 1 + m.count() + 1), vs)
                    }
                }
            }
        }
    }
}

fn subarr_position<V: Trace + Clone + 'static>(arr: &Array<V>, node_position: u8, prev: usize) -> usize {
    match &arr.0 {
        None => return 0,
        Some(n) => match n.borrow() {
            N2([(l, _)], _, _) => match node_position {
                0 => prev,
                1 => l.count(),
                2 => l.count() + 1 + prev,
                _ => unreachable!(),
            }
            N3([(l, _), (m, _)], _, _) => match node_position {
                0 => prev,
                1 => l.count(),
                2 => l.count() + 1 + prev,
                3 => l.count() + 1 + m.count(),
                4 => l.count() + 1 + m.count() + 1 + prev,
                _ => unreachable!(),
            }
        }
    }
}








#[cfg(test)]
mod tests {
    use super::*;

    use std::cmp;

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

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum FocusConstruction {
        New(ArrayConstruction, usize),
    }

    impl FocusConstruction {
        fn construct_focus(&self) -> Focus<u32> {
            match self {
                Self::New(c, p) => {
                    let arr = c.construct_array();
                    Focus::new(&arr, p % (arr.count() + 1))
                }
            }
        }

        fn construct_control(&self) -> (Vector<u32>, usize) {
            match self {
                Self::New(c, p) => {
                    let control = c.construct_control();
                    let p = p % (control.len() + 1);
                    (control, p)
                }
            }
        }
    }

    fn arb_focus_construction() -> impl Strategy<Value = FocusConstruction> {
        let leaf = (arb_array_construction(), any::<usize>()).prop_map(|(a, i)| FocusConstruction::New(a, i));
        leaf
    }

    fn control_get_relative(control: &(Vector<u32>, usize), i: isize) -> Option<&u32> {
        let tmp = (control.1 as isize) + i;
        if tmp < 0 {
            None
        } else {
            control.0.get(tmp as usize)
        }
    }

    fn control_refocus(control: &(Vector<u32>, usize), by: isize) -> ((Vector<u32>, usize), isize) {
        let control_index = if by >= 0 {
            cmp::min(control.0.len() as isize, (control.1 as isize) + by) as usize
        } else {
            cmp::max(0, (control.1 as isize) + by) as usize
        };
        let moved = (control_index as isize) - (control.1 as isize);

        ((control.0.clone(), control_index), moved)
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

        #[test]
        fn test_get(c in arb_array_construction(), i in any::<usize>()) {
            let arr = c.construct_array();
            let control = c.construct_control();
            if control.len() > 0 {
                let i = i % control.len();

                let a = arr.get(i);
                let b = control.get(i).unwrap();

                if a != b {
                    println!("----------------\ngot {:?} rather than {:?} at index {:?}\nExpected: {:?}\n\n{:?}\n\n\n", arr.count(), control.len(), i, control, arr);
                    panic!()
                }
            }
        }

        #[test]
        fn test_focus(c in arb_focus_construction(), i in any::<isize>()) {
            let focus = c.construct_focus();
            let control = c.construct_control();
            if control.0.len() > 0 {
                let i = i % ((control.0.len() + 1) as isize);

                let a = focus.get_relative(i);
                let b = control_get_relative(&control, i);

                if a != b {
                    println!("----------------\ngot {:?} rather than {:?} at index {:?}\nControl: {:?}\n\n{:?}\n\n\n", a, b, i, control, focus);
                    panic!()
                }
            }
        }

        #[test]
        fn test_refocus(c in arb_focus_construction(), i in any::<isize>(), by in any::<isize>(), by2 in any::<isize>()) {
            let mut focus = c.construct_focus();
            let control = c.construct_control();
            let initial_position = control.1;
            if control.0.len() > 0 {
                let i = i % ((control.0.len() + 1) as isize);

                let moved = focus.refocus(by);
                let (control, control_moved) = control_refocus(&control, by);

                if moved != control_moved {
                    println!("
Invalid first refocus:
expected move: {:?}, actual: {:?}
control focus: {:?}
actual focus: {:?}
refocus by: {:?}, starting at {:?}


", control_moved, moved, control, focus, by, initial_position);
                    panic!();
                }

                let a = focus.get_relative(i);
                let b = control_get_relative(&control, i);

                if a != b {
                    println!("
Invalid first relative get:
expected {:?}, actual {:?}
at index {:?} relative to {:?}
control focus: {:?}
actual focus: {:?}
refocus by: {:?}, starting at {:?}", b, a, i, control.1, control, focus, by, initial_position);


                    panic!();
                }

                let moved2 = focus.refocus(by2);
                let (control, control_moved2) = control_refocus(&control, by2);

                if moved2 != control_moved2 {
                    println!("
Invalid second refocus:
expected move: {:?}, actual: {:?}
control focus: {:?}
actual focus: {:?}
refocus by: {:?}
previously: refocus by {:?}, starting at {:?}, moving by {:?}


", control_moved2, moved2, control, focus, by2, by, initial_position, moved);
                    panic!();
                }

                let a = focus.get_relative(i);
                let b = control_get_relative(&control, i);

                if a != b {
                    println!("
Invalid second relative get:
expected {:?}, actual {:?}
at index {:?} relative to {:?}
control focus: {:?}
actual focus: {:?}
refocus by: {:?} then {:?}, starting at {:?}", b, a, i, control.1, control, focus, by, by2, initial_position);


                    panic!();
                }
            }
        }

        #[test]
        fn test_cmp(c in arb_array_construction(), d in arb_array_construction()) {
            let arr = c.construct_array();
            let control = c.construct_control();

            let arr2 = d.construct_array();
            let control2 = d.construct_control();

            assert_eq!(arr == arr2, control == control2);
            assert_eq!(arr != arr2, control != control2);
            assert_eq!(arr < arr2, control < control2);
            assert_eq!(arr <= arr2, control <= control2);
            assert_eq!(arr >= arr2, control >= control2);
            assert_eq!(arr > arr2, control > control2);
            assert_eq!(arr.partial_cmp(&arr2), control.partial_cmp(&control2));
            assert_eq!(arr.cmp(&arr2), control.cmp(&control2));
        }
    }
}
