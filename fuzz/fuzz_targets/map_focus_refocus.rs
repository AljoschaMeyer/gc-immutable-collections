#![no_main]
use libfuzzer_sys::fuzz_target;

use arbitrary::{Arbitrary, Unstructured};

use gc_immutable_collections::map_test::*;

fuzz_target!(|data: &[u8]| {
    match <(FocusConstruction, isize, isize, isize)>::arbitrary(&mut Unstructured::new(data)) {
        Ok((c, i, by, by2)) => {
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
construction: {:?}


", control_moved, moved, control, focus, by, initial_position, c);
                    panic!();
                }

                let a = focus.get_relative_entry(i).map(|(k, v)| (*k, *v));
                let b = control_get_relative_entry(&control, i);

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

                let a = focus.get_relative_entry(i).map(|(k, v)| (*k, *v));
                let b = control_get_relative_entry(&control, i);

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
        _ => {}
    }
});
