#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::map_test::*;

fuzz_target!(|data: &[u8]| {
    match MapConstruction::arbitrary(&mut Unstructured::new(data)) {
        Ok(c) => {
            let map = c.construct_map();
            let control = c.construct_control();

            if map.count() != control.len() {
                println!("----------------\ncount was {:?} rather than {:?}\nExpected: {:?}\n\n{:?}\n\n\n", map.count(), control.len(), control, map);
                panic!()
            }
        }
        _ => {}
    }
});
