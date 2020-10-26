#![warn(clippy::suspicious_operation_groupings)]

struct Vec3 {
    x: f64,
    y: f64,
    z: f64,
}

impl Eq for Vec3 {}

impl PartialEq for Vec3 {
    fn eq(&self, other: &Self) -> bool {
        // This should trigger the lint because `self.x` is compared to `other.y`
        self.x == other.y && self.y == other.y && self.z == other.z
    }
}

struct S {
    a: i32,
    b: i32,
    c: i32,
    d: i32,
}

fn buggy_ab_cmp(s1: &S, s2: &S) -> bool {
    // There's no `s1.b`
    s1.a < s2.a && s1.a < s2.b
}

struct SAOnly {
    a: i32,
}

impl S {
    fn a(&self) -> i32 { 0 }
}

fn do_not_give_bad_suggestions_for_this_unusual_expr(s1: &S, s2: &SAOnly) -> bool {
    // This is superficially similar to `buggy_ab_cmp`, but we should not suggest
    // `s2.b` since that is invalid.
    s1.a < s2.a && s1.a() < s1.b
}

fn do_not_give_bad_suggestions_for_this_macro_expr(s1: &S, s2: &SAOnly) -> bool {
    macro_rules! s1 {
        () => {
            S {
                a: 1,
                b: 1,
                c: 1,
                d: 1,
            }
        }
    }

    // This is superficially similar to `buggy_ab_cmp`, but we should not suggest
    // `s2.b` since that is invalid.
    s1.a < s2.a && s1!().a < s1.b
}

fn do_not_give_bad_suggestions_for_this_incorrect_expr(s1: &S, s2: &SAOnly) -> bool {
    // There's two `s1.b`, but we should not suggest `s2.b` since that is invalid
    s1.a < s2.a && s1.b < s1.b
}

fn permissable(s1: &S, s2: &S) -> bool {
    // Something like this seems like it might actually be what is desired.
    s1.a == s2.b
}

fn non_boolean_operators(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    s1.a * s2.a + s1.b * s2.b + s1.c * s2.b + s1.d * s2.d
}

fn odd_number_of_pairs(s1: &S, s2: &S) -> i32 {
    // There's no `s2.b`
    s1.a * s2.a + s1.b * s2.c + s1.c * s2.c
}

fn not_caught_by_eq_op_middle_change_left(s1: &S, s2: &S) -> i32 {
    // There's no `s1.b`
    s1.a * s2.a + s2.b * s2.b + s1.c * s2.c
}

fn not_caught_by_eq_op_middle_change_right(s1: &S, s2: &S) -> i32 {
    // There's no `s2.b`
    s1.a * s2.a + s1.b * s1.b + s1.c * s2.c
}

fn not_caught_by_eq_op_start(s1: &S, s2: &S) -> i32 {
    // There's no `s2.a`
    s1.a * s1.a + s1.b * s2.b + s1.c * s2.c
}

fn not_caught_by_eq_op_end(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    s1.a * s2.a + s1.b * s2.b + s1.c * s1.c
}

fn the_cross_product_should_not_lint(s1: &S, s2: &S) -> (i32, i32, i32) {
    (
        s1.b * s2.c - s1.c * s2.b,
        s1.c * s2.a - s1.a * s2.c,
        s1.a * s2.b - s1.b * s2.a,
    )
}

fn outer_parens_simple(s1: &S, s2: &S) -> i32 {
    // There's no `s2.b`
    (s1.a * s2.a + s1.b * s1.b)
}

fn outer_parens(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    (s1.a * s2.a + s1.b * s2.b + s1.c * s2.b + s1.d * s2.d)
}

fn inner_parens(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    (s1.a * s2.a) + (s1.b * s2.b) + (s1.c * s2.b) + (s1.d * s2.d)
}

fn outer_and_some_inner_parens(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    ((s1.a * s2.a) + (s1.b * s2.b) + (s1.c * s2.b) + (s1.d * s2.d))
}

fn all_parens_balanced_tree(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    (((s1.a * s2.a) + (s1.b * s2.b)) + ((s1.c * s2.b) + (s1.d * s2.d)))
}

fn all_parens_left_tree(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    (((s1.a * s2.a) + (s1.b * s2.b) + (s1.c * s2.b)) + (s1.d * s2.d))
}

fn all_parens_right_tree(s1: &S, s2: &S) -> i32 {
    // There's no `s2.c`
    ((s1.a * s2.a) + ((s1.b * s2.b) + (s1.c * s2.b) + (s1.d * s2.d)))
}

fn inside_other_binop_expression(s1: &S, s2: &S) -> i32 {
    // There's no `s1.b`
    (s1.a * s2.a + s2.b * s2.b) / 2
}

fn inside_function_call(s1: &S, s2: &S) -> i32 {
    // There's no `s1.b`
    i32::swap_bytes(s1.a * s2.a + s2.b * s2.b)
}

fn inside_larger_boolean_expression(s1: &S, s2: &S) -> bool {
    // There's no `s1.c`
    s1.a > 0 && s1.b > 0 && s1.d == s2.c && s1.d == s2.d
}

fn inside_larger_boolean_expression_with_unsorted_ops(s1: &S, s2: &S) -> bool {
    // There's no `s1.c`
    s1.a > 0 && s1.d == s2.c && s1.b > 0 && s1.d == s2.d
}

struct Nested {
    inner: ((i32,), (i32,), (i32,))
}

fn changed_middle_ident(n1: &Nested, n2: &Nested) -> bool {
    // There's no `n2.inner.2.0`
    n1.inner.0.0 == n2.inner.0.0
    && n1.inner.1.0 == n2.inner.1.0
    && n1.inner.2.0 == n2.inner.1.0
}

// `eq_op` should catch this one.
fn changed_initial_ident(n1: &Nested, n2: &Nested) -> bool {
    // There's no `n2.inner.0.0`
    n1.inner.0.0 == n1.inner.0.0
    && n1.inner.1.0 == n2.inner.1.0
    && n1.inner.2.0 == n2.inner.2.0
}

fn inside_fn_with_similar_expression(s1: &S, s2: &S, strict: bool) -> bool {
    if strict {
        s1.a < s2.a && s1.b < s2.b
    } else {
        // There's no `s1.b` in this subexpression
        s1.a <= s2.a && s1.a <= s2.b
    }
}

fn inside_an_if_statement(s1: &S, s2: &S) {
    // There's no `s1.b`
    if s1.a < s2.a && s1.a < s2.b {
        s1.c = s2.c;
    }
}

fn multiple_comparison_types_and_unary_minus(s: &S) -> bool {
    s.a > s.c
    && s.a < -s.c
    && s.b > s.c // `s.c` should be `s.d` here.
    && s.b < -s.d
}

/* TODO re-enable these
fn across_if_statements(s: &mut S) {
    if s.a > s.c {
        s.a = s.c;
    }
    if s.a < -s.c {
        s.a = -s.c;
    }
    if s.b > s.c { // `s.c` should be `s.d` here.
        s.b = s.d;
    }
    if s.b < -s.d {
        s.b = -s.d;
    }
}
*/
fn main() {}
