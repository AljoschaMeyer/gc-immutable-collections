#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::*;
use gc_immutable_collections::map_test::*;

fuzz_target!(|data: &[u8]| {
    match <(MapConstruction, i8, usize)>::arbitrary(&mut Unstructured::new(data)) {
        Ok((c, k, i)) => {
            let map = c.construct_map();
            let control = c.construct_control();

            // println!("{:?}", c);

            if map.count() != control.len() {
                println!("----------------\ncount was {:?} rather than {:?}\nExpected: {:?}\n\n{:?}\n\n\n", map.count(), control.len(), control, map);
                panic!()
            }

            let a = map.get(&k);
            let b = control.get(&k);

            if a != b {
                println!("----------------\ngot {:?} rather than {:?} at key {:?}\nExpected: {:?}\n\n{:?}\n\n\n", a, b, k, control, map);
                panic!()
            }

            let has_k = map.contains(&k);
            let has_k_control = control.contains_key(&k);
            if has_k != has_k_control {
                println!("---------------\nmap says it contains entry for key {:?}, should be {:?}\nExpected: {:?}\n\n{:?}\n\n\n", has_k, has_k_control, control, map);
                panic!()
            }

            let k_index = map.index_of(&k);
            let k_index_control = match control.split_lookup(&k) {
                (_, None, _) => None,
                (l, Some(_), _) => Some(l.len()),
            };
            if k_index != k_index_control {
                println!("---------------\nmap says index_of({:?}) == {:?}, should be {:?}\nControl: {:?}\n\nMap: {:?}\n\n\n", k, k_index, k_index_control, control, map);
                panic!()
            }

            let get_at = map.get_entry_index(i);
            let tmp = control.take(i.saturating_add(1));
            let get_at_control = if i >= control.len() { None } else { tmp.get_max() };
            if get_at.map(|e| (*e.0, *e.1)) != get_at_control.map(|e| (e.0, e.1)) {
                println!("---------------\nmap says get_at({:?}) == {:?}, should be {:?}\nControl: {:?}\n\nMap: {:?}\n\n\n", k, get_at, get_at_control, control, map);
                panic!()
            }

            let find_leq = map.get_entry_find(&k, Find::Leq);
            let find_leq_control = control.get_prev(&k);
            if find_leq != find_leq_control {
                println!("---------------\nmap says find_leq({:?}) == {:?}, should be {:?}\nControl: {:?}\n\nMap: {:?}\n\n\n", k, find_leq, find_leq_control, control, map);
                panic!()
            }

            let find_geq = map.get_entry_find(&k, Find::Geq);
            let find_geq_control = control.get_next(&k);
            if find_geq != find_geq_control {
                println!("---------------\nmap says find_geq({:?}) == {:?}, should be {:?}\nControl: {:?}\n\nMap: {:?}\n\n\n", k, find_geq, find_geq_control, control, map);
                panic!()
            }

            let find_lt = map.get_entry_find(&k, Find::Lt);
            let (tmp, _) = control.split(&k);
            let find_lt_control = tmp.get_max();
            if find_lt.map(|e| (*e.0, *e.1)) != find_lt_control.map(|e| (e.0, e.1)) {
                println!("---------------\nmap says find_lt({:?}) == {:?}, should be {:?}\nControl: {:?}\n\nMap: {:?}\n\n\n", k, find_lt, find_lt_control, control, map);
                panic!()
            }

            let find_gt = map.get_entry_find(&k, Find::Gt);
            let (_, tmp) = control.split(&k);
            let find_gt_control = tmp.get_min();
            if find_gt.map(|e| (*e.0, *e.1)) != find_gt_control.map(|e| (e.0, e.1)) {
                println!("---------------\nmap says find_gt({:?}) == {:?}, should be {:?}\nControl: {:?}\n\nMap: {:?}\n\n\n", k, find_gt, find_gt_control, control, map);
                panic!()
            }
        }
        _ => {}
    }
});
