#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::*;
use gc_immutable_collections::array_test::*;

fuzz_target!(|data: &[u8]| {
    match ArrayConstruction::arbitrary(&mut Unstructured::new(data)) {
        Ok(c) => {
            let arr = c.construct_array();
            let control = c.construct_control();

            if arr.count() != control.len() {
                println!("----------------\ncount was {:?} rather than {:?}\nExpected: {:?}\n\n{:?}\n\n\n", arr.count(), control.len(), control, arr);
                panic!()
            }
        }
        _ => {}
    }
});
