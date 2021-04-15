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
        let (_, r) = r.split(1);
        l.concat(&r)
    }

    /// Time complexity: O(log(n))
    pub fn update(&self, i: usize, v: V) -> Self {
        let (l, r) = self.split(i);
        let (_, r) = r.split(1);
        l.concat(&Self::singleton(v)).concat(&r)
    }

    pub fn slice(&self, start: usize, end: usize) -> Self {
        let (l, _) = self.split(end);
        l.split(start).1
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

        let mut p1 = ArrayFocus::new(self, 0);
        let mut p2 = ArrayFocus::new(rhs, 0);

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

        let mut p1 = ArrayFocus::new(self, 0);
        let mut p2 = ArrayFocus::new(rhs, 0);

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

        let mut p1 = ArrayFocus::new(self, 0);
        let mut p2 = ArrayFocus::new(rhs, 0);

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

        let mut p1 = ArrayFocus::new(self, 0);
        let mut p2 = ArrayFocus::new(rhs, 0);

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

        let mut p1 = ArrayFocus::new(self, 0);
        let mut p2 = ArrayFocus::new(rhs, 0);

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

        let mut p1 = ArrayFocus::new(self, 0);
        let mut p2 = ArrayFocus::new(rhs, 0);

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

#[derive(Debug, Trace, Finalize)]
pub struct ArrayFocus<V: Trace + 'static>(Vec<(Array<V>, u8)>);

impl<V: Trace + Clone +  'static> ArrayFocus<V> {
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

            let subarr_i = (subarr_p as isize).saturating_add(by);
            if 0 <= subarr_i && subarr_i <= (arr.count() as isize) {
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
                        focus_new(m, p - (l.count() + 1), vs)
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

#[derive(Trace, Finalize)]
pub struct ArrayBuilder<V: Trace + Clone + 'static>(Vec<V>, Vec<V>);

impl<V: Trace + Clone + 'static> ArrayBuilder<V> {
    pub fn new() -> Self {
        ArrayBuilder(Vec::new(), Vec::new())
    }

    pub fn push_front(&mut self, v: V) {
        self.0.push(v)
    }

    pub fn push_back(&mut self, v: V) {
        self.1.push(v)
    }

    pub fn build(&self) -> Array<V> {
        let start = do_build_reverse(&self.0[..]);
        let end = do_build(&self.1[..]);
        start.concat(&end)
    }
}

fn do_build<V: Trace + Clone + 'static>(vs: &[V]) -> Array<V> {
    let l = vs.len();
    if l == 0 {
        Array::new()
    } else if l == 1 {
        Array::singleton(vs[0].clone())
    } else if (l - 2) % 3 == 0 {
        let recursive_length = (l - 2) / 3;
        n3(
            do_build(&vs[..recursive_length]),
            /**/ vs[recursive_length].clone(),
            do_build(&vs[recursive_length + 1..(recursive_length * 2) + 1]),
            /**/ vs[(recursive_length * 2) + 1].clone(),
            do_build(&vs[(recursive_length * 2) + 2..]),
        )
    } else if (l - 1) % 2 == 0 {
        let recursive_length = (l - 1) / 2;
        n2(
            do_build(&vs[..recursive_length]),
            /**/ vs[recursive_length].clone(),
            do_build(&vs[recursive_length + 1..]),
        )
    } else {
        do_build(&vs[1..]).insert(0, vs[0].clone())
    }
}

fn do_build_reverse<V: Trace + Clone + 'static>(vs: &[V]) -> Array<V> {
    let l = vs.len();
    if l == 0 {
        Array::new()
    } else if l == 1 {
        Array::singleton(vs[0].clone())
    } else if (l - 2) % 3 == 0 {
        let recursive_length = (l - 2) / 3;
        n3(
            do_build_reverse(&vs[(recursive_length * 2) + 2..]),
            /**/ vs[(recursive_length * 2) + 1].clone(),
            do_build_reverse(&vs[recursive_length + 1..(recursive_length * 2) + 1]),
            /**/ vs[recursive_length].clone(),
            do_build_reverse(&vs[..recursive_length]),
        )
    } else if (l - 1) % 2 == 0 {
        let recursive_length = (l - 1) / 2;
        n2(
            do_build_reverse(&vs[recursive_length + 1..]),
            /**/ vs[recursive_length].clone(),
            do_build_reverse(&vs[..recursive_length]),
        )
    } else {
        let l = vs.len();
        do_build_reverse(&vs[..l - 1]).insert(0, vs[l - 1].clone())
    }
}
