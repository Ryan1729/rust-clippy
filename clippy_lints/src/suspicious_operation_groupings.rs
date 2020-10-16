use crate::utils::{snippet_with_applicability, span_lint_and_sugg};
use crate::utils::ast_utils::{eq_id, IdentIter};
use core::ops::{Add, AddAssign};
use if_chain::if_chain;
use rustc_ast::ast::*;
use rustc_ast::ptr::P;
use rustc_data_structures::fx::FxHashSet;
use rustc_errors::Applicability;
use rustc_lint::{EarlyContext, EarlyLintPass};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::symbol::Ident;
use rustc_span::Span;

declare_clippy_lint! {
    /// **What it does:**
    ///
    /// **Why is this bad?**
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    ///
    /// ```rust
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code which does not raise clippy warning
    /// ```
    pub SUSPICIOUS_OPERATION_GROUPINGS,
    correctness,
    "default lint description"
}

declare_lint_pass!(SuspiciousOperationGroupings => [SUSPICIOUS_OPERATION_GROUPINGS]);

impl EarlyLintPass for SuspiciousOperationGroupings {
    fn check_expr(&mut self, cx: &EarlyContext<'_>, expr: &Expr) {
        if expr.span.from_expansion() {
            return;
        }

        if let Some(binops) = chained_binops(&expr.kind) {
            let binop_count = binops.len();
            if binop_count < 2 {
                // Single binary operation expressions would likely be false
                // positives.
                return;
            }

            let mut one_ident_difference_count = 0;
            let mut double_difference_info = None;
            let mut expected_ident_loc = None;

            let mut paired_identifiers = FxHashSet::default();

            for (i, BinaryOp { left, right, .. }) in binops.iter().enumerate() {
                match ident_difference_expr(left, right) {
                    IdentDifference::NoDifference => {
                        // The `eq_op` lint should catch this if it's an issue.
                        return;
                    },
                    IdentDifference::Single(ident_loc, ident) => {
                        one_ident_difference_count += 1;
                        if let Some(previous_expected) = expected_ident_loc {
                            if previous_expected != ident_loc {
                                // This expression doesn't match the form we're
                                // looking for.
                                return;
                            }
                        } else {
                            expected_ident_loc = Some(ident_loc);
                        }

                        paired_identifiers.insert(ident);
                    },
                    IdentDifference::Double(ident_loc1, ident_loc2) => {
                        double_difference_info = Some((i, ident_loc1, ident_loc2));
                    },
                    IdentDifference::Multiple | IdentDifference::NonIdentDifference => {
                        // It's too hard to know whether this is a bug or not.
                        // TODO: Do we need to recurse in order to find known
                        // buggy expressions inside complicated ones?
                        return;
                    },
                }
            }

            if_chain! {
                if one_ident_difference_count == binop_count - 1;
                if let Some(expected_loc) = expected_ident_loc;
                if let Some((
                        double_difference_index,
                        ident_loc1,
                        ident_loc2
                )) = double_difference_info;
                if let Some(binop) = binops.get(double_difference_index);
                then {
                    let changed_loc = if ident_loc1 == expected_loc {
                        ident_loc2
                    } else if ident_loc2 == expected_loc {
                        ident_loc1
                    } else {
                        // This expression doesn't match the form we're
                        // looking for.
                        return;
                    };

                    let mut applicability = Applicability::MachineApplicable;

                    if let Some(sugg) = ident_swap_sugg(
                        cx,
                        &paired_identifiers,
                        binop,
                        changed_loc,
                        &mut applicability,
                    ) {
                        span_lint_and_sugg(
                            cx,
                            SUSPICIOUS_OPERATION_GROUPINGS,
                            binop.span,
                            "This sequence of operators looks suspiciously like a bug.",
                            "Did you mean",
                            sugg,
                            applicability,
                        )
                    }
                }
            }
        }
    }
}

fn ident_swap_sugg(
    cx: &EarlyContext<'_>,
    paired_identifiers: &FxHashSet<Ident>,
    binop: &BinaryOp,
    location: IdentLocation,
    applicability: &mut Applicability,
) -> Option<String> {
    let left_ident = get_ident(&binop.left, location)?;
    let right_ident = get_ident(&binop.right, location)?;

    let sugg = match (
        paired_identifiers.contains(&left_ident),
        paired_identifiers.contains(&right_ident),
    ) {
        (true, true) | (false, false) => {
            // We don't have a good guess of what ident should be
            // used instead, in these cases.
            *applicability = Applicability::MaybeIncorrect;

            // We arbitraily choose one side to suggest changing,
            // since we don't have a better guess. If the user
            // ends up duplicating a clause, the `logic_bug` lint
            // should catch it.

            let right_suggestion =
                suggestion_with_swapped_ident(cx, &binop.right, location, left_ident, applicability)?;

            format!(
                "{} {} {}",
                snippet_with_applicability(cx, binop.left.span, "..", applicability),
                binop.op.to_string(),
                right_suggestion,
            )
        },
        (false, true) => {
            // We haven't seen a pair involving the left one, so
            // it's probably what is wanted.

            let right_suggestion =
                suggestion_with_swapped_ident(cx, &binop.right, location, left_ident, applicability)?;

            format!(
                "{} {} {}",
                snippet_with_applicability(cx, binop.left.span, "..", applicability),
                binop.op.to_string(),
                right_suggestion,
            )
        },
        (true, false) => {
            // We haven't seen a pair involving the right one, so
            // it's probably what is wanted.
            let left_suggestion = suggestion_with_swapped_ident(cx, &binop.left, location, right_ident, applicability)?;

            format!(
                "{} {} {}",
                left_suggestion,
                binop.op.to_string(),
                snippet_with_applicability(cx, binop.right.span, "..", applicability),
            )
        },
    };

    Some(sugg)
}

struct BinaryOp {
    op: BinOpKind,
    span: Span,
    left: P<Expr>,
    right: P<Expr>,
}

// TODO make this collect expr pairs in (for example) if expressions, and rename it.
// Also, include enough info to make a coherent suggestion in those cases.
fn chained_binops(kind: &ExprKind) -> Option<Vec<BinaryOp>> {
    todo!()
}

#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
struct IdentLocation {
    index: usize,
}

impl Add for IdentLocation {
    type Output = IdentLocation;

    fn add(self, other: Self) -> Self::Output {
        Self {
            index: self.index + other.index
        }
    }
}

impl AddAssign for IdentLocation {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other
    }
}

#[derive(Clone, Copy, Debug)]
enum IdentDifference {
    NoDifference,
    Single(IdentLocation, Ident),
    Double(IdentLocation, IdentLocation),
    Multiple,
    NonIdentDifference,
}

impl Add for IdentDifference {
    type Output = IdentDifference;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (Self::NoDifference, output)|(output, Self::NoDifference) => output,
            (Self::Multiple, _)
            | (_, Self::Multiple)
            | (Self::Single(_, _), Self::Double(_, _))
            | (Self::Double(_, _), Self::Single(_, _))
            | (Self::Double(_, _), Self::Double(_, _)) => 
                Self::Multiple,
            (Self::NonIdentDifference, _)|(_, Self::NonIdentDifference) => 
                Self::NonIdentDifference,
            (Self::Single(il1, _), Self::Single(il2, _)) => Self::Double(il1, il2),
        }
    }
}

impl AddAssign for IdentDifference {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other
    }
}

impl IdentDifference {
    /// Returns true if learning about more differences will not change the value
    /// of this `IdentDifference`, and false otherwise.
    fn is_complete(&self) -> bool {
        match self {
            Self::NoDifference | Self::Single(_, _) | Self::Double(_, _) => false,
            Self::Multiple | Self::NonIdentDifference => true,
        }
    }
}

fn ident_difference_expr(left: &Expr, right: &Expr) -> IdentDifference {
    ident_difference_expr_with_base_location(left, right, IdentLocation::default()).0
}

fn ident_difference_expr_with_base_location(
    left: &Expr,
    right: &Expr,
    mut base: IdentLocation,
) -> (IdentDifference, IdentLocation) {
    // Ideally, this function should not use IdentIter because it should return
    // early if the expressions have any non-ident differences.
    //
    // But, we cannot (easily?) use a `rustc_ast::visit::Visitor`, since we need
    // the two expressions to be walked in lockstep. And without a `Visitor`, we'd
    // have to do all the AST traversal ourselves, which is a lot of work, since to
    // do it properly we'd need to be able to handle more or less every possible
    // AST node since `Item`s can be written inside `Expr`s.
    //
    // In practice, it seems likely that expressions, above a certain size, that
    // happen to use the exact same idents in the exact same order, and which are
    // not structured the same, would be rare. Therefore it seems likely that if
    // we do only the first layer of matching ourselves and eventually fallback on
    // IdentIter, then the output of this function will be almost always be correct
    // in practice.
    //
    // If it turns out that problematic cases are more prelavent than we assume,
    // then we should be able to change this function to do the correct traversal,
    // without needing to change the rest of the code.
    let mut difference = IdentDifference::NoDifference;

    for (left_attr, right_attr) in left.attrs.iter().zip(right.attrs.iter()) {
        let (new_difference, new_base) =
            ident_difference_via_ident_iter_with_base_location(left_attr, right_attr, base);
        base = new_base;
        difference += new_difference;
        if difference.is_complete() {
            return (difference, base);
        }
    }

    match (&left.kind, &right.kind) {
        _ => todo!(),
    }
}

fn ident_difference_via_ident_iter_with_base_location<Iterable: Into<IdentIter>>(
    left: Iterable,
    right: Iterable,
    mut base: IdentLocation,
) -> (IdentDifference, IdentLocation) {
    // See the note in `ident_difference_expr_with_base_location` about `IdentIter`
    let mut difference = IdentDifference::NoDifference;

    let mut left_iterator = left.into();
    let mut right_iterator = right.into();

    loop {
        base += IdentLocation { index: 1 };
        match (left_iterator.next(), right_iterator.next()) {
            (Some(left_ident), Some(right_ident)) => {
                if eq_id(left_ident, right_ident) {
                    continue;
                }

                difference += IdentDifference::Single(base, right_ident);
                if difference.is_complete() {
                    return (difference, base);
                }
            },
            (Some(_), None) | (None, Some(_)) => {
                return (IdentDifference::NonIdentDifference, base);
            },
            (None, None) => {
                return (difference, base);
            },
        }
    }
}

fn get_ident(expr: &Expr, location: IdentLocation) -> Option<Ident> {
    IdentIter::from(expr).nth(location.index)
}

fn suggestion_with_swapped_ident(
    cx: &EarlyContext<'_>,
    expr: &Expr,
    location: IdentLocation,
    new_ident: Ident,
    applicability: &mut Applicability,
) -> Option<String> {
    get_ident(expr, location).and_then(|current_ident| {
        format!(
            "{}{}{}",
            snippet_with_applicability(cx, expr.span.with_hi(current_ident.span.lo()), "..", applicability),
            new_ident.to_string(),
            snippet_with_applicability(cx, expr.span.with_lo(current_ident.span.hi()), "..", applicability),
        )
    })
}

