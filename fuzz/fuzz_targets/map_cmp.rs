#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::map_test::*;

fuzz_target!(|data: &[u8]| {
    match <(MapConstruction, MapConstruction)>::arbitrary(&mut Unstructured::new(data)) {
        Ok((c, d)) => {
            let arr = c.construct_map();
            let control = c.construct_control();

            let arr2 = d.construct_map();
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
        _ => {}
    }
});
