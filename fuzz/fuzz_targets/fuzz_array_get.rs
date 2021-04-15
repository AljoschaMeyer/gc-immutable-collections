#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::array_test::*;

fuzz_target!(|data: &[u8]| {
    match <(ArrayConstruction, usize)>::arbitrary(&mut Unstructured::new(data)) {
        Ok((c, i)) => {
            let arr = c.construct_array();
            let control = c.construct_control();
            if control.len() > 0 {
                let i = i % control.len();

                let a = arr.get(i);
                let b = control.get(i).unwrap();

                if a != b {
                    println!("----------------\ngot {:?} rather than {:?} at index {:?}\nExpected: {:?}\n\n{:?}\n\n\n", a, b, i, control, arr);
                    panic!()
                }
            }
        }
        _ => {}
    }
});
