// Implemented as a [join-based](https://en.wikipedia.org/wiki/Join-based_tree_algorithms)
// [2-3 tree](https://en.wikipedia.org/wiki/2%E2%80%933_tree).

use std::borrow::Borrow;
use std::cmp::Ordering::{self, *};

use gc::{Gc, Trace, custom_trace};
use gc_derive::{Trace, Finalize};

#[derive(Debug, Finalize)]
pub struct Map<K: Trace + 'static, V: Trace + 'static>(Option<Gc<Node<K, V>>>);

unsafe impl<K: Trace + 'static, V: Trace + 'static> Trace for Map<K, V> {
    custom_trace!(this, {
        mark(&this.0);
    });
}

impl<K: Trace + 'static, V: Trace + 'static> Clone for Map<K, V> {
    fn clone(&self) -> Self {
        Map(self.0.clone())
    }
}

#[derive(Debug, Clone, Trace, Finalize)]
enum Node<K: Trace + 'static, V: Trace + 'static> {
    N2([(Map<K, V>, K, V); 1], Map<K, V>, usize /* count */),
    N3([(Map<K, V>, K, V); 2], Map<K, V>, usize /* count */),
}
use self::Node::*;

fn n2<K: Trace + 'static, V: Trace + 'static>(l: Map<K, V>, k: K, v: V, r: Map<K, V>) -> Map<K, V> {
    let lc = l.count();
    let rc = r.count();
    Map(Some(Gc::new(N2([(l, k, v)], r, lc + rc + 1))))
}

fn n3<K: Trace + 'static, V: Trace + 'static>(l: Map<K, V>, lk: K, lv: V, m: Map<K, V>, mk: K, mv: V, r: Map<K, V>) -> Map<K, V> {
    let lc = l.count();
    let mc = m.count();
    let rc = r.count();
    Map(Some(Gc::new(N3([(l, lk, lv), (m, mk, mv)], r, lc + mc + rc + 2))))
}

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

impl<K: Trace + 'static, V: Trace + 'static> Map<K, V> {
    /// Create a new, empty `Map`.
    ///
    /// Time complexity: O(log(1))
    pub fn new() -> Self {
        Map(None)
    }

    /// Create a new `Map` containing only the given entry.
    ///
    /// Time complexity: O(log(1))
    pub fn singleton(k: K, v: V) -> Self {
        n2(Map::new(), k, v, Map::new())
    }

    fn height_(&self) -> u8 {
        match &self.0 {
            None => 0,
            Some(n) => n.height_(),
        }
    }

    /// Return the number of entries in this `Map`.
    ///
    /// Time complexity: O(1)
    pub fn count(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(n) => n.count(),
        }
    }

    /// Return whether this `Map` contains no entries.
    ///
    /// Time complexity: O(log(1))
    pub fn is_empty(&self) -> bool {
        match &self.0 {
            None => true,
            Some(_) => false,
        }
    }

    /// Return whether this `Map` contains exactly one entry.
    ///
    /// Time complexity: O(log(1))
    pub fn is_singleton(&self) -> bool {
        match &self.0 {
            None => false,
            Some(n) => match n.borrow() {
                N2([(_, _, _)], _, 1) => true,
                _ => false,
            }
        }
    }

    /// Time complexity: O(log(n))
    pub fn get_entry_min(&self) -> Option<(&K, &V)> {
        match &self.0 {
            None => None,
            Some(n) => match n.borrow() {
                N2([(l, k, v)], _, _) | N3([(l, k, v), _], _, _) => match &l.0 {
                    None => Some((k, v)),
                    Some(_) => l.get_entry_min(),
                }
            }
        }
    }

    /// Time complexity: O(log(n))
    pub fn get_key_min(&self) -> Option<&K> {
        self.get_entry_min().map(|(k, _)| k)
    }

    /// Time complexity: O(log(n))
    pub fn get_value_min(&self) -> Option<&V> {
        self.get_entry_min().map(|(_, v)| v)
    }

    /// Time complexity: O(log(n))
    pub fn get_min(&self) -> Option<&V> {
        self.get_value_min()
    }

    /// Time complexity: O(log(n))
    pub fn get_entry_max(&self) -> Option<(&K, &V)> {
        match &self.0 {
            None => None,
            Some(n) => match n.borrow() {
                N2([(_, k, v)], r, _) | N3([_, (_, k, v)], r, _) => match &r.0 {
                    None => Some((k, v)),
                    Some(_) => r.get_entry_max(),
                }
            }
        }
    }

    /// Time complexity: O(log(n))
    pub fn get_key_max(&self) -> Option<&K> {
        self.get_entry_max().map(|(k, _)| k)
    }

    /// Time complexity: O(log(n))
    pub fn get_max(&self) -> Option<&V> {
        self.get_entry_max().map(|(_, v)| v)
    }

    pub fn get_entry_index(&self, at: usize) -> Option<(&K, &V)> {
        if self.count() <= at {
            return None;
        }
        match &self.0 {
            None => None,
            Some(n) => n.get_entry_index(at),
        }
    }

    pub fn get_key_index(&self, at: usize) -> Option<&K> {
        self.get_entry_index(at).map(|(k, _)| k)
    }

    pub fn get_index(&self, at: usize) -> Option<&V> {
        self.get_entry_index(at).map(|(_, v)| v)
    }

    // fn producer_min(&self) -> Producer<K, V> {
    //     let mut stack = Vec::new();
    //     self.producer_min_(&mut stack);
    //     return Producer(stack);
    // }
    //
    // fn producer_min_(&self, stack: &mut Vec<(Map<K, V>, u8)>) {
    //     stack.push((self.clone(), 0));
    //     if let Some(n) = &self.0 {
    //         match n.borrow() {
    //             N2([(l, _, _)], _, _) | N3([(l, _, _), _], _, _) => l.producer_min_(stack),
    //         }
    //     }
    // }
}

impl<K: Ord + Trace + 'static, V: Trace + 'static> Map<K, V> {
    /// Time complexity: O(log(n))
    pub fn get_entry_find<Q: ?Sized>(&self, kx: &Q, f: Find) -> Option<(&K, &V)> where K: Borrow<Q>, Q: Ord {
        match &self.0 {
            None => None,
            Some(n) => n.get_entry_find(kx, f),
        }
    }

    /// Time complexity: O(log(n))
    pub fn get_key_find<Q: ?Sized>(&self, kx: &Q, f: Find) -> Option<&K> where K: Borrow<Q>, Q: Ord {
        self.get_entry_find(kx, f).map(|(k, _)| k)
    }

    /// Time complexity: O(log(n))
    pub fn get_value_find<Q: ?Sized>(&self, kx: &Q, f: Find) -> Option<&V> where K: Borrow<Q>, Q: Ord {
        self.get_entry_find(kx, f).map(|(_, v)| v)
    }

    /// Time complexity: O(log(n))
    pub fn get_entry<Q: ?Sized>(&self, kx: &Q) -> Option<(&K, &V)> where K: Borrow<Q>, Q: Ord {
        self.get_entry_find(kx, Find::Eq)
    }

    /// Time complexity: O(log(n))
    pub fn get<Q: ?Sized>(&self, kx: &Q) -> Option<&V> where K: Borrow<Q>, Q: Ord {
        self.get_value_find(kx, Find::Eq)
    }

    /// Time complexity: O(log(n))
    pub fn contains<Q: ?Sized>(&self, kx: &Q) -> bool where K: Borrow<Q>, Q: Ord {
        self.get(kx).is_some()
    }

    /// Time complexity: O(log(n))
    pub fn index_of<Q: ?Sized>(&self, kx: &Q) -> Option<usize> where K: Borrow<Q>, Q: Ord {
        self.index_of_(kx, 0)
    }

    fn index_of_<Q: ?Sized>(&self, kx: &Q, acc: usize) -> Option<usize> where K: Borrow<Q>, Q: Ord {
        match &self.0 {
            None => None,
            Some(n) => n.index_of(kx, acc),
        }
    }
}

impl<K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static> Map<K, V> {
    /// Prefers the keys and values from the first map.
    pub fn union(a: &Self, b: &Self) -> Self {
        Self::union_with(a, b, |av, _| av.clone())
    }

    /// Prefers the keys from the first, uses the function to select the value.
    pub fn union_with<F: Clone + FnMut(&V, &V) -> V>(a: &Self, b: &Self, mut f: F) -> Self {
        if a.is_empty() {
            b.clone()
        } else {
            match &b.0 {
                None => a.clone(),
                Some(b) => {
                    let (bl, (bk, bv), br) = left_root_right(b);
                    let (al, ax, ar) = split(a, bk);
                    let nl = Self::union_with(&al, &bl, f.clone());
                    let nr = Self::union_with(&ar, &br, f.clone());
                    match ax {
                        None => join(&nl, bk, bv, &nr),
                        Some((ak, av)) => join(&nl, ak, &f(av, bv), &nr),
                    }
                }
            }
        }
    }

    /// Prefers the keys and values from the first map.
    pub fn intersection<X: Clone + Trace + 'static>(a: &Self, b: &Map<K, X>) -> Map<K, V> {
        Self::intersection_with(a, b, |va, _| va.clone())
    }

    /// Prefers the keys from the first, uses the function to select the value.
    pub fn intersection_with<X: Clone + Trace + 'static, Y: Clone + Trace + 'static, F: Clone + FnMut(&V, &X) -> Y>(a: &Self, b: &Map<K, X>, mut f: F) -> Map<K, Y> {
        if a.is_empty() {
            <Map<K, Y>>::new()
        } else {
            match &b.0 {
                None => <Map<K, Y>>::new(),
                Some(b) => {
                    let (bl, (bk, bv), br) = left_root_right(b);
                    let (al, ax, ar) = split(a, bk);
                    let nl = Self::intersection_with(&al, &bl, f.clone());
                    let nr = Self::intersection_with(&ar, &br, f.clone());
                    match ax {
                        Some((ak, av)) => join(&nl, ak, &f(av, bv), &nr),
                        None => join2(&nl, &nr),
                    }
                }
            }
        }
    }

    pub fn difference<X: Clone + Trace + 'static>(a: &Self, b: &Map<K, X>) -> Self {
        if a.is_empty() {
            a.clone()
        } else {
            match &b.0 {
                None => a.clone(),
                Some(b) => {
                    let (bl, (bk, _), br) = left_root_right(b);
                    let (al, _, ar) = split(a, bk);
                    let nl = Self::difference(&al, &bl);
                    let nr = Self::difference(&ar, &br);
                    join2(&nl, &nr)
                }
            }
        }
    }

    pub fn symmetric_difference(a: &Self, b: &Map<K, V>) -> Self {
        if a.is_empty() {
            b.clone()
        } else {
            match &b.0 {
                None => a.clone(),
                Some(b) => {
                    let (bl, (bk, bv), br) = left_root_right(b);
                    let (al, ax, ar) = split(a, bk);
                    let nl = Self::symmetric_difference(&al, &bl);
                    let nr = Self::symmetric_difference(&ar, &br);
                    match ax {
                        Some(_) => join2(&nl, &nr),
                        None => join(&nl, bk, bv, &nr)
                    }
                }
            }
        }
    }

    /// Prefers the new key and value.
    pub fn insert(&self, k: K, v: V) -> Self {
        Self::union(&Self::singleton(k, v), self)
    }

    /// Time complexity: O(log(n))
    pub fn remove<Q: ?Sized>(&self, kx: &Q) -> Self where K: Borrow<Q>, Q: Ord {
        match self.get_key_find(kx, Find::Eq) {
            None => self.clone(),
            Some(kx) => Self::difference(self, &Map::singleton(kx.clone(), ())),
        }
    }

    // /// Time complexity: O(log(n))
    // fn remove_min(&self) -> Self {
    //     match self.get_key_min() {
    //         None => self.clone(),
    //         Some(kx) => self.remove(kx),
    //     }
    // }

    /// Time complexity: O(log(n))
    fn remove_max(&self) -> Self {
        match self.get_key_max() {
            None => self.clone(),
            Some(kx) => self.remove(kx),
        }
    }

    pub fn remove_index<Q: ?Sized>(&self, at: usize) -> Self where K: Borrow<Q>, Q: Ord {
        match self.get_key_index(at) {
            None => self.clone(),
            Some(k) => self.remove(k.borrow()),
        }
    }

    pub fn slice<Q: ?Sized>(&self, start: &Q, end: &Q) -> Self where K: Borrow<Q>, Q: Ord {
        let (_, lx, lr) = split(self, start);
        let from_start = match lx {
            Some((lk, lv)) => lr.insert(lk.clone(), lv.clone()),
            None => lr,
        };
        split(&from_start, end).0
    }

    pub fn slice_index<Q: ?Sized>(&self, start: usize, end: usize) -> Option<Self> where K: Borrow<Q>, Q: Ord {
        if end < start {
            return None;
        }

        if start == self.count() && end == start {
            return Some(Self::new());
        }

        match self.get_key_index(start) {
            None => return None,
            Some(k_start) => {
                if end == self.count() {
                    return Some(self.split(k_start.borrow()).1);
                }
                match self.get_key_index(end) {
                    None => return None,
                    Some(k_end) => {
                        return Some(self.slice(k_start.borrow(), k_end.borrow()));
                    }
                }
            }
        }
    }

    pub fn slice_from<Q: ?Sized>(&self, start: &Q) -> Self where K: Borrow<Q>, Q: Ord {
        self.split(start).1
    }

    pub fn slice_to<Q: ?Sized>(&self, end: &Q) -> Self where K: Borrow<Q>, Q: Ord {
        self.split(end).0
    }

    pub fn split<Q: ?Sized>(&self, at: &Q) -> (Self, Self) where K: Borrow<Q>, Q: Ord {
        let (ll, lx, mut lr) = split(self, at);
        if let Some((lk, lv)) = lx {
            lr = lr.insert(lk.clone(), lv.clone());
        }
        return (ll, lr);
    }

    pub fn split_inclusive<Q: ?Sized>(&self, at: &Q) -> (Self, Self) where K: Borrow<Q>, Q: Ord {
        let (mut ll, lx, lr) = split(self, at);
        if let Some((lk, lv)) = lx {
            ll = ll.insert(lk.clone(), lv.clone());
        }
        return (ll, lr);
    }

    pub fn split_at<Q: ?Sized>(&self, at: usize) -> Option<(Self, Self)> where K: Borrow<Q>, Q: Ord {
        if at == self.count() {
            return Some((self.clone(), Self::new()));
        } else {
            match self.get_key_index(at) {
                None => return None,
                Some(k) => return Some(self.split(k.borrow())),
            }
        }
    }
}

impl<K: Trace + 'static, V: Trace + 'static> Node<K, V> {
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

    fn get_entry_index(&self, i: usize) -> Option<(&K, &V)> {
        match self {
            N2([(l, k, v)], r, _) => match i.cmp(&l.count()) {
                Less => l.get_entry_index(i),
                Equal => Some((k, v)),
                Greater => r.get_entry_index(i - (l.count() + 1)),
            }
            N3([(l, lk, lv), (m, mk, mv)], r, _) => match i.cmp(&l.count()) {
                Less => l.get_entry_index(i),
                Equal => Some((lk, lv)),
                Greater => match (i - (l.count() + 1)).cmp(&m.count()) {
                    Less => m.get_entry_index(i - (l.count() + 1)),
                    Equal => Some((mk, mv)),
                    Greater => r.get_entry_index(i - (l.count() + 1 + m.count() + 1))
                }
            }
        }
    }
}

impl<K: Ord + Trace + 'static, V: Trace + 'static> Node<K, V> {
    fn get_entry_find<Q: ?Sized>(&self, kx: &Q, f: Find) -> Option<(&K, &V)> where K: Borrow<Q>, Q: Ord {
        match self {
            N2([(l, k, v)], r, _) => {
                match kx.cmp(k.borrow()) {
                    Less => l.get_entry_find(kx, f).or(if f.matches_greater() { Some((k, v)) } else { None }),
                    Equal => match f {
                        Find::Lt => l.get_entry_find(kx, f),
                        Find::Gt => r.get_entry_find(kx, f),
                        _ => Some((k, v)),
                    }
                    Greater => r.get_entry_find(kx, f).or(if f.matches_less() { Some((k, v)) } else { None }),
                }
            }
            N3([(l, lk, lv), (m, mk, mv)], r, _) => {
                match kx.cmp(lk.borrow()) {
                    Less => l.get_entry_find(kx, f).or(if f.matches_greater() { Some((lk, lv)) } else { None }),
                    Equal => match f {
                        Find::Lt => l.get_entry_find(kx, f),
                        Find::Gt if m.count() == 0 => Some((mk, mv)),
                        Find::Gt => m.get_entry_find(kx, f),
                        _ => Some((lk, lv)),
                    }
                    Greater => match kx.cmp(mk.borrow()) {
                        Less => m.get_entry_find(kx, f).or(if f.matches_greater() { Some((mk, mv)) } else if f.matches_less() { Some((lk, lv)) } else { None }),
                        Equal => match f {
                            Find::Lt if m.count() == 0 => Some((lk, lv)),
                            Find::Lt => m.get_entry_find(kx, f),
                            Find::Gt => r.get_entry_find(kx, f),
                            _ => Some((mk, mv)),
                        }
                        Greater => r.get_entry_find(kx, f).or(if f.matches_less() { Some((mk, mv)) } else { None }),
                    }
                }
            }
        }
    }

    fn index_of<Q: ?Sized>(&self, kx: &Q, acc: usize) -> Option<usize> where K: Borrow<Q>, Q: Ord {
        match self {
            N2([(l, k, _v)], r, _) => {
                match kx.cmp(k.borrow()) {
                    Less => l.index_of_(kx, acc),
                    Equal => Some(acc + l.count()),
                    Greater => r.index_of_(kx, acc + l.count() + 1),
                }
            }
            N3([(l, lk, _lv), (m, mk, _mv)], r, _) => {
                match kx.cmp(lk.borrow()) {
                    Less => l.index_of_(kx, acc),
                    Equal => Some(acc + l.count()),
                    Greater => match kx.cmp(mk.borrow()) {
                        Less => m.index_of_(kx, acc + l.count() + 1),
                        Equal => Some(acc + l.count() + 1 + m.count()),
                        Greater => r.index_of_(kx, acc + l.count() + 1 + m.count() + 1),
                    }
                }
            }
        }
    }
}

//     fn is_submap<X: Clone>(a: &Self, b: &Self) -> bool {
//         unimplemented!()
//     }
//
//     fn is_proper_submap<X: Clone>(a: &Self, b: &Self) -> bool {
//         unimplemented!()
//     }
// }

fn left_root_right<K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static>(n: &Node<K, V>) -> (Map<K, V>, (&K, &V), Map<K, V>) {
    match n {
        N2([(l, k, v)], r, _) => {
            (l.clone(), (k, v), r.clone())
        }
        N3([(l, lk, lv), (m, mk, mv)], r, _) => {
            (l.clone(), (lk, lv), n2(m.clone(), mk.clone(), mv.clone(), r.clone()))
        }
    }
}

fn join<K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static>(lesser: &Map<K, V>, k: &K, v: &V, greater: &Map<K, V>) -> Map<K, V> {
    let lesser_height = lesser.height_();
    let greater_height = greater.height_();

    match lesser_height.cmp(&greater_height) {
        Less => match join_lesser_smaller(lesser, k, v, greater, greater_height - lesser_height) {
            Insert::Done(done_n) => done_n,
            Insert::Up(l, k, v, r) => n2(
                l.clone(),
                /**/ k.clone(), v.clone(),
                r.clone(),
            ),
        }
        Equal => n2(
            lesser.clone(),
            /**/ k.clone(), v.clone(),
            greater.clone(),
        ),
        Greater => match join_greater_smaller(lesser, k, v, greater, lesser_height - greater_height) {
            Insert::Done(done_n) => done_n,
            Insert::Up(l, k, v, r) => n2(
                l.clone(),
                /**/ k.clone(), v.clone(),
                r.clone(),
            ),
        }
    }
}

fn join2<K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static>(lesser: &Map<K, V>, greater: &Map<K, V>) -> Map<K, V> {
    match lesser.get_entry_max() {
        None => greater.clone(),
        Some((max_k, max_v)) => {
            join(&lesser.remove_max(), max_k, max_v, greater)
        }
    }
}

// traverse left spine of greater node for h_diff, then merge
fn join_lesser_smaller<'a, K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static>(
    lesser: &Map<K, V>, k: &'a K, v: &'a V, greater: &'a Map<K, V>, h_diff: u8
) -> Insert<'a, K, V> {
    if h_diff == 0 {
        Insert::Up(lesser.clone(), k, v, greater.clone())
    } else {
        match &greater.0 {
            None => unreachable!(),
            Some(n) => match n.borrow() {
                N2([(gl, gk, gv)], gr, _) => {
                    n2_handle_insert_l(
                        join_lesser_smaller(lesser, k, v, gl, h_diff - 1), gk, gv, gr
                    )
                }
                N3([(gl, glk, glv), (gm, gmk, gmv)], gr, _) => {
                    n3_handle_insert_l(
                        join_lesser_smaller(
                            lesser, k, v, gl, h_diff - 1
                        ),
                        glk, glv, gm, gmk, gmv, gr,
                    )
                }
            }
        }
    }
}

fn join_greater_smaller<'a, K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static>(
    lesser: &'a Map<K, V>, k: &'a K, v: &'a V, greater: &Map<K, V>, h_diff: u8
) -> Insert<'a, K, V> {
    if h_diff == 0 {
        Insert::Up(lesser.clone(), k, v, greater.clone())
    } else {
        match &lesser.0 {
            None => unreachable!(),
            Some(n) => match n.borrow() {
                N2([(ll, lk, lv)], lr, _) => {
                    n2_handle_insert_r(
                        ll, lk, lv, join_greater_smaller(lr, k, v, greater, h_diff - 1)
                    )
                }
                N3([(ll, llk, llv), (lm, lmk, lmv)], lr, _) => {
                    n3_handle_insert_r(
                        ll, llk, llv, lm, lmk, lmv,
                        join_greater_smaller(
                            lr, k, v, greater, h_diff - 1
                        ),
                    )
                }
            }
        }
    }
}

fn split<'a, K, V, Q: ?Sized>(n: &'a Map<K, V>, kx: &Q) -> (Map<K, V>, Option<(&'a K, &'a V)>, Map<K, V>)
    where K: Ord + Clone + Borrow<Q> + Trace + 'static, V: Clone + Trace + 'static, Q: Ord {
    match &n.0 {
        None => (Map::new(), None, Map::new()),
        Some(n) => match n.borrow() {
            N2([(l, k, v)], r, _) => {
                match kx.cmp(k.borrow()) {
                    Less => {
                        let (ll, lm, lr) = split(l, kx);
                        (ll, lm.clone(), join(&lr, k, v, r))
                    }
                    Equal => (l.clone(), Some((k, v)), r.clone()),
                    Greater => {
                        let (rl, rm, rr) = split(r, kx);
                        (join(l, k, v, &rl), rm.clone(), rr)
                    }
                }
            }
            N3([(l, lk, lv), (m, mk, mv)], r, _) => {
                match kx.cmp(lk.borrow()) {
                    Less => {
                        let (ll, lm, lr) = split(l, kx);
                        (
                            ll,
                            lm.clone(),
                            join(
                                &join(&lr, lk, lv, m),
                                mk, mv,
                                r
                            )
                        )
                    }
                    Equal => (l.clone(), Some((lk, lv)), n2(m.clone(), mk.clone(), mv.clone(), r.clone())),
                    Greater => match kx.cmp(mk.borrow()) {
                        Less => {
                            let (ml, mm, mr) = split(m, kx);
                            (
                                join(l, lk, lv, &ml),
                                mm.clone(),
                                join(&mr, mk, mv, r),
                            )
                        }
                        Equal => (
                            n2(l.clone(), lk.clone(), lv.clone(), m.clone()),
                            Some((mk, mv)),
                            r.clone(),
                        ),
                        Greater => {
                            let (rl, rm, rr) = split(r, kx);
                            return (
                                join(
                                    l,
                                    lk, lv,
                                    &join(m, mk, mv, &rl),
                                ),
                                rm.clone(),
                                rr,
                            );
                        }
                    }
                }
            }
        }
    }
}

enum Insert<'a, K: Trace + 'static, V: Trace + 'static> {
    Done(Map<K, V>),
    Up(Map<K, V>, &'a K, &'a V, Map<K, V>),
}

fn n2_handle_insert_l<'a, K, V>(insert_l: Insert<K, V>, k: &'a K, v: &'a V, r: &Map<K, V>) -> Insert<'a, K, V>
    where K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static {
    match insert_l {
        Insert::Done(done_n) => Insert::Done(n2(
            done_n,
            /**/ k.clone(), v.clone(),
            r.clone(),
        )),
        Insert::Up(up_l, up_k, up_v, up_r) => Insert::Done(n3(
            up_l,
            /**/ up_k.clone(), up_v.clone(),
            up_r,
            /**/ k.clone(), v.clone(),
            r.clone(),
        )),
    }
}

fn n2_handle_insert_r<'a, K, V>(l: &Map<K, V>, k: &'a K, v: &'a V, insert_r: Insert<'a, K, V>) -> Insert<'a, K, V>
    where K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static {
    match insert_r {
        Insert::Done(done_n) => Insert::Done(n2(
            l.clone(),
            /**/ k.clone(), v.clone(),
            done_n,
        )),
        Insert::Up(up_l, up_k, up_v, up_r) => Insert::Done(n3(
            l.clone(),
            /**/ k.clone(), v.clone(),
            up_l,
            /**/ up_k.clone(), up_v.clone(),
            up_r,
        )),
    }
}

fn n3_handle_insert_l<'a, K, V>(
    insert_l: Insert<'a, K, V>, lk: &'a K, lv: &'a V, m: &Map<K, V>, rk: &'a K, rv: &'a V, r: &Map<K, V>
) -> Insert<'a, K, V> where K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static {
    match insert_l {
        Insert::Done(done_n) => Insert::Done(n3(
            done_n,
            /**/ lk.clone(), lv.clone(),
            m.clone(),
            /**/ rk.clone(), rv.clone(),
            r.clone(),
        )),
        Insert::Up(up_l, up_k, up_v, up_r) => Insert::Up(
                n2(up_l, up_k.clone(), up_v.clone(), up_r),
                /**/ lk, lv,
                n2(m.clone(), rk.clone(), rv.clone(), r.clone()),
            ),
    }
}

// fn n3_handle_insert_m<'a, K, V>(
//     l: &Map<K, V>, lk: &'a K, lv: &'a V, insert_m: Insert<'a, K, V>, rk: &'a K, rv: &'a V, r: &Map<K, V>
// ) -> Insert<'a, K, V> where K: Ord + Clone, V: Clone {
//     match insert_m {
//         Insert::Done(done_n) => Insert::Done(n3(
//             l.clone(),
//             /**/ lk.clone(), lv.clone(),
//             done_n,
//             /**/ rk.clone(), rv.clone(),
//             r.clone(),
//         )),
//         Insert::Up(up_l, up_k, up_v, up_r) => Insert::Up(
//             n2(l.clone(), lk.clone(), lv.clone(), up_l),
//             /**/ up_k, up_v,
//             n2(up_r.clone(), rk.clone(), rv.clone(), r.clone()),
//         ),
//     }
// }

fn n3_handle_insert_r<'a, K, V>(
    l: &Map<K, V>, lk: &'a K, lv: &'a V, m: &Map<K, V>, rk: &'a K, rv: &'a V, insert_r: Insert<'a, K, V>
) -> Insert<'a, K, V> where K: Ord + Clone + Trace + 'static, V: Clone + Trace + 'static {
    match insert_r {
        Insert::Done(done_n) => Insert::Done(n3(
            l.clone(),
            /**/ lk.clone(), lv.clone(),
            m.clone(),
            /**/ rk.clone(), rv.clone(),
            done_n,
        )),
        Insert::Up(up_l, up_k, up_v, up_r) => Insert::Up(
            n2(l.clone(), lk.clone(), lv.clone(), m.clone()),
            /**/ rk, rv,
            n2(up_l, up_k.clone(), up_v.clone(), up_r),
        ),
    }
}

impl<K: PartialEq + Clone + Trace + 'static, V: PartialEq + Clone + Trace + 'static> PartialEq for Map<K, V> {
    fn eq(&self, rhs: &Self) -> bool {
        match (&self.0, &rhs.0) {
            (None, None) => return true,
            (Some(_), None) | (None, Some(_)) => return false,
            (Some(n1), Some(n2)) if  Gc::ptr_eq(n1, n2) => return true,
            _ => {}
        };

        let mut p1 = MapFocus::new(self, 0);
        let mut p2 = MapFocus::new(rhs, 0);

        loop {
            match (p1.get_relative_entry(0), p2.get_relative_entry(0)) {
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

impl<K: PartialEq + Clone + Trace + 'static, V: PartialEq + Clone + Trace + 'static> Eq for Map<K, V> {}

impl<K: PartialOrd + Clone + Trace + 'static, V: PartialOrd + Clone + Trace + 'static> PartialOrd for Map<K, V> {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        match (&self.0, &rhs.0) {
            (None, None) => return Some(Ordering::Equal),
            (Some(_), None) => return Some(Ordering::Greater),
            (None, Some(_)) => return Some(Ordering::Less),
            (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return Some(Ordering::Equal),
            _ => {}
        };

        let mut p1 = MapFocus::new(self, 0);
        let mut p2 = MapFocus::new(rhs, 0);

        loop {
            match (p1.get_relative_entry(0), p2.get_relative_entry(0)) {
                (None, None) => return Some(Ordering::Equal),
                (Some(_), None) => return Some(Ordering::Greater),
                (None, Some(_)) => return Some(Ordering::Less),
                (Some((xk, xv)), Some((yk, yv))) => {
                    match xk.partial_cmp(&yk) {
                        None => return None,
                        Some(Ordering::Less) => return Some(Ordering::Less),
                        Some(Ordering::Greater) => return Some(Ordering::Greater),
                        Some(Ordering::Equal) => {
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

        let mut p1 = MapFocus::new(self, 0);
        let mut p2 = MapFocus::new(rhs, 0);

        loop {
            match (p1.get_relative_entry(0), p2.get_relative_entry(0)) {
                (None, None) => return false,
                (Some(_), None) => return false,
                (None, Some(_)) => return true,
                (Some((xk, xv)), Some((yk, yv))) => {
                    match xk.partial_cmp(&yk) {
                        None => return false,
                        Some(Ordering::Less) => return true,
                        Some(Ordering::Greater) => return false,
                        Some(Ordering::Equal) => {
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

        let mut p1 = MapFocus::new(self, 0);
        let mut p2 = MapFocus::new(rhs, 0);

        loop {
            match (p1.get_relative_entry(0), p2.get_relative_entry(0)) {
                (None, None) => return true,
                (Some(_), None) => return false,
                (None, Some(_)) => return true,
                (Some((xk, xv)), Some((yk, yv))) => {
                    match xk.partial_cmp(&yk) {
                        None => return false,
                        Some(Ordering::Less) => return true,
                        Some(Ordering::Greater) => return false,
                        Some(Ordering::Equal) => {
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

        let mut p1 = MapFocus::new(self, 0);
        let mut p2 = MapFocus::new(rhs, 0);

        loop {
            match (p1.get_relative_entry(0), p2.get_relative_entry(0)) {
                (None, None) => return true,
                (Some(_), None) => return true,
                (None, Some(_)) => return false,
                (Some((xk, xv)), Some((yk, yv))) => {
                    match xk.partial_cmp(&yk) {
                        None => return false,
                        Some(Ordering::Less) => return false,
                        Some(Ordering::Greater) => return true,
                        Some(Ordering::Equal) => {
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
    }

    fn gt(&self, rhs: &Self) -> bool {
        match (&self.0, &rhs.0) {
            (None, None) => return false,
            (Some(_), None) => return true,
            (None, Some(_)) => return false,
            (Some(n1), Some(n2)) if Gc::ptr_eq(n1, n2) => return false,
            _ => {}
        };

        let mut p1 = MapFocus::new(self, 0);
        let mut p2 = MapFocus::new(rhs, 0);

        loop {
            match (p1.get_relative_entry(0), p2.get_relative_entry(0)) {
                (None, None) => return false,
                (Some(_), None) => return true,
                (None, Some(_)) => return false,
                (Some((xk, xv)), Some((yk, yv))) => {
                    match xk.partial_cmp(&yk) {
                        None => return false,
                        Some(Ordering::Less) => return false,
                        Some(Ordering::Greater) => return true,
                        Some(Ordering::Equal) => {
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
    }
}

impl<K: Ord + Clone + Trace + 'static, V: Ord + Clone + Trace + 'static> Ord for Map<K, V> {
    fn cmp(&self, rhs: &Self) -> Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}

#[derive(Debug, Trace, Finalize)]
pub struct MapFocus<K: Trace + 'static, V: Trace + 'static>(Vec<(Map<K, V>, u8)>);

impl<K: Trace + 'static, V: Trace + 'static> MapFocus<K, V> {
    pub fn new(map: &Map<K, V>, p: usize) -> Self {
        let mut v = vec![];
        focus_new(map, p, &mut v);
        Self(v)
    }

    pub fn get_relative_entry(&self, i: isize) -> Option<(&K, &V)> {
        let mut h = self.0.len();
        let mut submap_p = 0;

        while h > 0 {
            let (map, node_position) = &self.0[h - 1];
            submap_p = submap_position(map, *node_position, submap_p);

            let submap_i = (submap_p as isize) + i;
            if 0 <= submap_i && submap_i < (map.count() as isize) {
                return Some(map.get_entry_index(submap_i as usize).unwrap());
            } else {
                h -= 1;
            }
        }

        return None;
    }

    pub fn get_relative_key(&self, i: isize) -> Option<&K> {
        self.get_relative_entry(i).map(|(k, _)| k)
    }

    pub fn get_relative(&self, i: isize) -> Option<&V> {
        self.get_relative_entry(i).map(|(_, v)| v)
    }

    pub fn refocus(&mut self, by: isize) -> isize {
        if self.0.is_empty() {
            return 0;
        }

        let mut submap_p = 0;

        loop {
            let (map, node_position) = &self.0.pop().unwrap();
            submap_p = submap_position(map, *node_position, submap_p);

            let submap_i = (submap_p as isize).saturating_add(by);
            if 0 <= submap_i && submap_i <= (map.count() as isize) {
                focus_new(map, submap_i as usize, &mut self.0);
                return by;
            }

            if self.0.is_empty() {
                if by <= 0 {
                    focus_new(map, 0, &mut self.0);
                    return -(submap_p as isize);
                } else {
                    focus_new(map, map.count(), &mut self.0);
                    return (self.0[0].0.count() - submap_p) as isize;
                }
            }
        }
    }
}

fn focus_new<K: Trace + 'static, V: Trace + 'static>(map: &Map<K, V>, p: usize, vs: &mut Vec<(Map<K, V>, u8)>) {
    match &map.0 {
        None => return,
        Some(n) => match n.borrow() {
            N2([(l, _, _)], r, _) => match p.cmp(&l.count()) {
                Less => {
                    vs.push((map.clone(), 0));
                    focus_new(l, p, vs)
                }
                Equal => vs.push((map.clone(), 1)),
                Greater => {
                    vs.push((map.clone(), 2));
                    focus_new(r, p - (l.count() + 1), vs)
                }
            }
            N3([(l, _, _), (m, _, _)], r, _) => match p.cmp(&l.count()) {
                Less => {
                    vs.push((map.clone(), 0));
                    focus_new(l, p, vs)
                }
                Equal => vs.push((map.clone(), 1)),
                Greater => match (p - (l.count() + 1)).cmp(&m.count()) {
                    Less => {
                        vs.push((map.clone(), 2));
                        focus_new(m, p - (l.count() + 1), vs)
                    }
                    Equal => vs.push((map.clone(), 3)),
                    Greater => {
                        vs.push((map.clone(), 4));
                        focus_new(r, p - (l.count() + 1 + m.count() + 1), vs)
                    }
                }
            }
        }
    }
}

fn submap_position<K: Trace + 'static, V: Trace + 'static>(map: &Map<K, V>, node_position: u8, prev: usize) -> usize {
    match &map.0 {
        None => return 0,
        Some(n) => match n.borrow() {
            N2([(l, _, _)], _, _) => match node_position {
                0 => prev,
                1 => l.count(),
                2 => l.count() + 1 + prev,
                _ => unreachable!(),
            }
            N3([(l, _, _), (m, _, _)], _, _) => match node_position {
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
pub struct MapBuilder<K: Trace + Clone + 'static, V: Trace + Clone + 'static>(Vec<(K, V)>, Vec<(K, V)>);

impl<K: Trace + Clone + Ord + 'static, V: Trace + Clone + 'static> MapBuilder<K, V> {
    pub fn new() -> Self {
        MapBuilder(Vec::new(), Vec::new())
    }

    pub fn push_front(&mut self, k: K, v: V) -> Result<(), ()> {
        match self.0.last() {
            Some(l) => {
                if k < l.0 {
                    self.0.push((k, v));
                    Ok(())
                } else {
                    Err(())
                }
            }
            None => {
                match self.1.get(0) {
                    Some(f) => {
                        if k < f.0 {
                            self.0.push((k, v));
                            Ok(())
                        } else {
                            Err(())
                        }
                    }
                    None => {
                        self.0.push((k, v));
                        Ok(())
                    }
                }
            }
        }
    }

    pub fn push_back(&mut self, k: K, v: V) -> Result<(), ()> {
        match self.1.last() {
            Some(l) => {
                if k > l.0 {
                    self.1.push((k, v));
                    Ok(())
                } else {
                    Err(())
                }
            }
            None => {
                match self.0.get(0) {
                    Some(f) => {
                        if k > f.0 {
                            self.1.push((k, v));
                            Ok(())
                        } else {
                            Err(())
                        }
                    }
                    None => {
                        self.1.push((k, v));
                        Ok(())
                    }
                }
            }
        }
    }

    pub fn build(&self) -> Map<K, V> {
        let start = do_build_reverse(&self.0[..]);
        let end = do_build(&self.1[..]);
        Map::union(&start, &end)
    }
}

fn do_build<K: Trace + Clone + Ord + 'static, V: Trace + Clone + 'static>(vs: &[(K, V)]) -> Map<K, V> {
    let l = vs.len();
    if l == 0 {
        Map::new()
    } else if l == 1 {
        Map::singleton(vs[0].0.clone(), vs[0].1.clone())
    } else if (l - 2) % 3 == 0 {
        let recursive_length = (l - 2) / 3;
        n3(
            do_build(&vs[..recursive_length]),
            /**/ vs[recursive_length].0.clone(),
            /**/ vs[recursive_length].1.clone(),
            do_build(&vs[recursive_length + 1..(recursive_length * 2) + 1]),
            /**/ vs[(recursive_length * 2) + 1].0.clone(),
            /**/ vs[(recursive_length * 2) + 1].1.clone(),
            do_build(&vs[(recursive_length * 2) + 2..]),
        )
    } else if (l - 1) % 2 == 0 {
        let recursive_length = (l - 1) / 2;
        n2(
            do_build(&vs[..recursive_length]),
            /**/ vs[recursive_length].0.clone(),
            /**/ vs[recursive_length].1.clone(),
            do_build(&vs[recursive_length + 1..]),
        )
    } else {
        do_build(&vs[1..]).insert(vs[0].0.clone(), vs[0].1.clone())
    }
}

fn do_build_reverse<K: Trace + Clone + Ord + 'static, V: Trace + Clone + 'static>(vs: &[(K, V)]) -> Map<K, V> {
    let l = vs.len();
    if l == 0 {
        Map::new()
    } else if l == 1 {
        Map::singleton(vs[0].0.clone(), vs[0].1.clone())
    } else if (l - 2) % 3 == 0 {
        let recursive_length = (l - 2) / 3;
        n3(
            do_build_reverse(&vs[(recursive_length * 2) + 2..]),
            /**/ vs[(recursive_length * 2) + 1].0.clone(),
            /**/ vs[(recursive_length * 2) + 1].1.clone(),
            do_build_reverse(&vs[recursive_length + 1..(recursive_length * 2) + 1]),
            /**/ vs[recursive_length].0.clone(),
            /**/ vs[recursive_length].1.clone(),
            do_build_reverse(&vs[..recursive_length]),
        )
    } else if (l - 1) % 2 == 0 {
        let recursive_length = (l - 1) / 2;
        n2(
            do_build_reverse(&vs[recursive_length + 1..]),
            /**/ vs[recursive_length].0.clone(),
            /**/ vs[recursive_length].1.clone(),
            do_build_reverse(&vs[..recursive_length]),
        )
    } else {
        let l = vs.len();
        do_build_reverse(&vs[..l - 1]).insert(vs[l - 1].clone().0, vs[l - 1].clone().1)
    }
}







// //////////////////////////////////////// debug /testing stuff
//
// pub fn map_to_vec(m: &Map, out: &mut Vec<(Value, Foo)>) {
//     node_to_vec(&m.0, out)
// }
//
// fn node_to_vec(n: &Node, out: &mut Vec<(Value, Foo)>) {
//     match n {
//         Leaf => {},
//         N2(n) => {
//             let (ref l, ref k, ref v, ref r, _) = &(**n);
//             node_to_vec(l, out);
//             out.push((k.clone(), v.clone()));
//             node_to_vec(r, out);
//         }
//         N3(n) => {
//             let (ref l, ref lk, ref lv, ref m, ref rk, ref rv, ref r, _) = &(**n);
//             node_to_vec(l, out);
//             out.push((lk.clone(), lv.clone()));
//             node_to_vec(m, out);
//             out.push((rk.clone(), rv.clone()));
//             node_to_vec(r, out);
//         }
//     }
// }
//
//
// use std::collections::BTreeMap;
//
// // fn fuzzy(data: &[u8]) {
// //     // Foo
// //     let mut control = BTreeMap::new();
// //     let mut m = Map::new();
// //
// //     for b in data {
// //         // m = m.insert(Value::int(*b as i64), Foo);
// //         // control.insert(Value::int(*b as i64), Foo);
// //
// //         match *b {
// //             0...63 => {
// //                 m = m.insert(Value::int((b & 0b0011_1111) as i64), Foo);
// //                 control.insert(Value::int((b & 0b0011_1111) as i64), Foo);
// //                 println!("insert {:?}", b & 0b0011_1111);
// //             }
// //             64...127 => {
// //                 m = m.remove(&Value::int((b & 0b0011_1111) as i64));
// //                 control.remove(&Value::int((b & 0b0011_1111) as i64));
// //                 println!("remove {:?}", b & 0b0011_1111);
// //             }
// //             128...191 => {
// //                 let key = Value::int((b & 0b0011_1111) as i64);
// //                 let (l, k, _) = m.split(&key);
// //                 println!("split-l {:?}", b & 0b0011_1111);
// //                 println!("splitl: ({:?}, {:?}, _)", l, k);
// //
// //                 // m = l;
// //                 match k {
// //                     None => m = l,
// //                     Some((k, v)) => m = l.insert(k.clone(), v.clone()),
// //                 }
// //
// //                 let mut new_control = BTreeMap::new();
// //                 for (k, v) in control.iter() {
// //                     // if k < &key {
// //                     //     new_control.insert(k.clone(), v.clone());
// //                     // }
// //                     if k <= &key {
// //                         new_control.insert(k.clone(), v.clone());
// //                     }
// //                 }
// //                 control = new_control;
// //             }
// //             192...255 => {
// //                 let key = Value::int((b & 0b0011_1111) as i64);
// //                 let (_, k, r) = m.split(&key);
// //                 println!("{:?}", m);
// //                 println!("split-r {:?}", b & 0b0011_1111);
// //                 println!("splitr: (_, {:?}, {:?})", k, r);
// //
// //                 // m = r;
// //                 match k {
// //                     None => m = r,
// //                     Some((k, v)) => m = r.insert(k.clone(), v.clone()),
// //                 }
// //
// //                 let mut new_control = BTreeMap::new();
// //                 for (k, v) in control.iter() {
// //                     if k >= &key {
// //                         new_control.insert(k.clone(), v.clone());
// //                     }
// //                     // if k > &key {
// //                     //     new_control.insert(k.clone(), v.clone());
// //                     // }
// //                 }
// //                 control = new_control;
// //             }
// //         }
// //     }
// //
// //     let mut out = vec![];
// //     map_to_vec(&m, &mut out);
// //     let out_control: Vec<(Value, Foo)> = control.into_iter().collect();
// //
// //     if out != out_control {
// //         println!("{:?}", "-----");
// //         println!("{:?}", out_control);
// //         println!("{:?}", out);
// //     }
// //
// //     assert!(out == out_control);
// // }
//
// fn fuzzy_cursor(data: &[u8]) {
//     let mut control = BTreeMap::new();
//     let mut m = Map::new();
//     let half = data.len() / 2;
//
//     for b in &data[..half] {
//         match *b {
//             0...63 => {
//                 m = m.insert(Value::int((b & 0b0011_1111) as i64), Foo);
//                 control.insert(Value::int((b & 0b0011_1111) as i64), Foo);
//             }
//             64...127 => {
//                 m = m.remove(&Value::int((b & 0b0011_1111) as i64));
//                 control.remove(&Value::int((b & 0b0011_1111) as i64));
//             }
//             128...191 => {
//                 let key = Value::int((b & 0b0011_1111) as i64);
//                 let (l, k, _) = m.split(&key);
//
//                 match k {
//                     None => m = l,
//                     Some((k, v)) => m = l.insert(k.clone(), v.clone()),
//                 }
//
//                 let mut new_control = BTreeMap::new();
//                 for (k, v) in control.iter() {
//                     if k <= &key {
//                         new_control.insert(k.clone(), v.clone());
//                     }
//                 }
//                 control = new_control;
//             }
//             192...255 => {
//                 let key = Value::int((b & 0b0011_1111) as i64);
//                 let (_, k, r) = m.split(&key);
//
//                 match k {
//                     None => m = r,
//                     Some((k, v)) => m = r.insert(k.clone(), v.clone()),
//                 }
//
//                 let mut new_control = BTreeMap::new();
//                 for (k, v) in control.iter() {
//                     if k >= &key {
//                         new_control.insert(k.clone(), v.clone());
//                     }
//                 }
//                 control = new_control;
//             }
//         }
//     }
//
//     let out_control: Vec<(Value, Foo)> = control.into_iter().collect();
//     let len = out_control.len();
//     if len == 0 {
//         return;
//     } else {
//         let (mut cursor, mut control_index) = if data[0] % 2 == 0 {
//             (m.cursor_min().unwrap(), 0)
//         } else {
//             (m.cursor_max().unwrap(), len - 1)
//         };
//         let mut skip = false;
//
//         println!("Initial: ({:?}, {:?})\n===", out_control, control_index);
//
//         for b in &data[half..] {
//             println!("control_index: {:?}", control_index);
//             println!("{:?}", cursor);
//             println!("---");
//             if skip {
//                 assert!(control_index == len || control_index == 0)
//             } else {
//                 match cursor.current() {
//                     None => assert!(control_index == len),
//                     Some((k, v)) => assert!((k, v) == out_control[control_index]),
//                 }
//             }
//
//             if b % 2 == 0 {
//                 skip = !cursor.next();
//                 if control_index != len {
//                     control_index += 1;
//                 }
//             } else {
//                 skip = !cursor.prev();
//                 if control_index != 0 {
//                     control_index -= 1;
//                 }
//             }
//         }
//     }
// }
//
// fn fuzzy_bulk(data: &[u8]) {
//     let mut control = BTreeMap::new();
//     let mut control2 = BTreeMap::new();
//     let mut m = Map::new();
//     let mut n = Map::new();
//     let half = data.len() / 2;
//
//     if data.len() == 0 {
//         return;
//     }
//
//     for b in &data[..half] {
//         match *b {
//             0...127 => {
//                 m = m.insert(Value::int((b & 0b0111_1111) as i64), Foo);
//                 control.insert(Value::int((b & 0b0111_1111) as i64), Foo);
//             }
//             128...255 => {
//                 m = m.remove(&Value::int((b & 0b0111_1111) as i64));
//                 control.remove(&Value::int((b & 0b0111_1111) as i64));
//             }
//         }
//     }
//
//     for b in &data[half..] {
//         match *b {
//             0...127 => {
//                 n = n.insert(Value::int((b & 0b0111_1111) as i64), Foo);
//                 control2.insert(Value::int((b & 0b0111_1111) as i64), Foo);
//             }
//             128...255 => {
//                 n = n.remove(&Value::int((b & 0b0111_1111) as i64));
//                 control2.remove(&Value::int((b & 0b0111_1111) as i64));
//             }
//         }
//     }
//
//     let mut out = vec![];
//     let out_control: Vec<(Value, Foo)>;
//
//     match data[0] {
//         _ => {
//             let union_ = m.union(&n);
//             map_to_vec(&union_, &mut out);
//
//             let mut tmp = control2.clone();
//             for (k, v) in control.into_iter() {
//                 tmp.insert(k, v);
//             }
//             out_control = tmp.into_iter().collect();
//         }
//     }
//
//     if out != out_control {
//         println!("{:?}", out_control);
//         println!("{:?}", out);
//     }
//
//     assert!(out == out_control);
// }
//
// // #[test]
// // fn test_fuzzy_bulk() {
// //     fuzzy_bulk(&[0, 0, 0, 1]);
// // }
// //
// // #[test]
// // fn test_fuzzy_cursor() {
// //     fuzzy_cursor(&[0x1f,0x0,0x1,0x32,0x0,0x1d,0xff,0xff]);
// //     fuzzy(&[0x10,0x1,0x0,0x23]);
// //     fuzzy(&[0xca,0x31,0xd1,0x0,0x6b]);
// //     fuzzy(&[0x3b,0x1,0x0,0x1,0x10]);
// //     fuzzy(&[0x2a,0x2d,0xa,0x1,0x0,0x80]);
// //     fuzzy(&[0x1,0xa,0xa]);
// // }
