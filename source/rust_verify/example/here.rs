// rust_verify/tests/example.rs expect-failures
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    fn fail_a_post_expr() -> (r: u64)
        ensures r == 1
    {
        // run with --here "rust_verify/example/here.rs:11:9"

        0
    }

    fn fail_a_post_stmt(r: &mut u64)
        ensures *r == 1
    {
        here>();

        *r = 0;
    }

    proof fn external_span(s: Seq<nat>) {
        assert(s[0] == 0);
    }

    #[allow(non_camel_case_types)]
    type here = u32;
    exec fn here(here: here) -> here {
        let here = here;
        here>();
        here
    }
}
