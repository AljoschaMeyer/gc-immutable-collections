#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::array_test::*;

fuzz_target!(|data: &[u8]| {
    match <(FocusConstruction, isize)>::arbitrary(&mut Unstructured::new(data)) {
        Ok((c, i)) => {
            let focus = c.construct_focus();
            let control = c.construct_control();
            if control.0.len() > 0 {
                let i = i % ((control.0.len() + 1) as isize);

                let a = focus.get_relative(i);
                let b = control_get_relative(&control, i);

                if a != b {
                    println!("----------------\ngot {:?} rather than {:?} at index {:?}\nControl: {:?}\n\n{:?}\n\n\n", a, b, i, control, focus);
                    println!("FocusConstruction: {:?}\n\nget_offset: {:?}\n\n\n\n", c, i);
                    panic!()
                }
            }
        }
        _ => {}
    }
});
