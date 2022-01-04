#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::map_test::*;

fuzz_target!(|data: &[u8]| {
    match <(MapConstruction, i8)>::arbitrary(&mut Unstructured::new(data)) {
        Ok((c, i)) => {
            let map = c.construct_map();
            let control = c.construct_control();
            if control.len() > 0 {
                let a = map.get(&i);
                let b = control.get(&i);

                if a != b {
                    println!("----------------\ngot {:?} rather than {:?} at key {:?}\nExpected: {:?}\n\n{:?}\n\n\n", a, b, i, control, map);
                    panic!()
                }
            }
        }
        _ => {}
    }
});
