use crate::utils::{span_lint_and_sugg};
use rustc_data_structures::fx::FxHashSet;
use rustc_lint::{EarlyLintPass, EarlyContext};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_ast::ast::*;

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
    pub SUSPICIOUS_CHAINED_OPERATORS,
    correctness,
    "default lint description"
}

declare_lint_pass!(SuspiciousChainedOperators => [SUSPICIOUS_CHAINED_OPERATORS]);

impl EarlyLintPass for SuspiciousChainedOperators {
    fn check_expr(&mut self, cx: &EarlyContext<'_>, expr: &Expr) {
        if expr.span.from_expansion() {
            return;
        }

        if let Some(binops) = chained_binops(expr.kind) {
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

            for (i, BinaryOp{ left, right, .. }) in binops.iter().enumerate() {
                match ident_differnce(left, right) {
                    NoDifference => {
                        // The `logic_bug` lint should catch this.
                        return;
                    }
                    Single(ident_loc, ident) => {
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
                    }
                    Double(ident_loc1, ident_loc2) => {
                        double_difference_info = Some((i, ident_loc1, ident_loc2));
                    }
                    Multiple => {
                        // It's too hard to know whether this is a bug or not.
                        // TODO: Do we need to recurse in order to find known
                        // buggy expressions inside complicated ones?
                        return;
                    }
                }
            }

            if_chain! {
                if one_ident_difference_count == pair_count - 1;
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

                    let left_ident = get_ident(binop.left, changed_loc);
                    let right_ident = get_ident(binop.right, changed_loc);

                    let (left_span, right_span) = match (
                        paired_identifiers.contains(&left_ident),
                        paired_identifiers.contains(&right_ident),
                    ) {
                        (true, true)|(false, false) {
                            // We don't have a good guess of what ident should be 
                            // used instead, in these cases.
                            applicability = Applicability::MaybeIncorrect;

                            // We arbitraily choose one side to suggest changing,
                            // since we don't have a better guess. If the user 
                            // ends up duplicating a clause, the `logic_bug` lint
                            // should catch it.
                            (
                                binop.left.span,
                                set_ident_in_span(
                                    binop.right.span,
                                    changed_loc,
                                    left_ident
                                )
                            )
                        },
                        (false, true) => {
                            // We haven't seen a pair involving the left one, so 
                            // it's probably what is wanted.
                            (
                                binop.left.span,
                                set_ident_in_span(
                                    binop.right.span,
                                    changed_loc,
                                    left_ident
                                )
                            )
                        },
                        (true, false) => {
                            // We haven't seen a pair involving the right one, so 
                            // it's probably what is wanted.
                            (
                                set_ident_in_span(
                                    binop.left.span,
                                    changed_loc,
                                    right_ident
                                )
                                binop.right.span,
                            )
                        },
                    };

                    let sugg = format!(
                        "{} {} {}",
                        snippet_with_applicability(cx, left_span, "..", &mut applicability),
                        op.op.to_string(),
                        snippet_with_applicability(cx, right_span, "..", &mut applicability)
                    );

                    span_lint_and_sugg<'a, T: LintContext>(
                        cx,
                        SUSPICIOUS_CHAINED_OPERATORS,
                        incorrect_expr_span,
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

struct BinaryOp {
    op: BinOpKind,
    span: Span,
    left: P<Expr>,
    right: P<Expr>,
}

fn chained_binops(kind: ExprKind) -> Option<&[BinaryOp]> {
    todo!()
}