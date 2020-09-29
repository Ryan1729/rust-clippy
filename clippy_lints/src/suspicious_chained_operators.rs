use core::iter::FusedIterator;
use if_chain::if_chain;
use crate::utils::{span_lint_and_sugg, snippet_with_applicability};
use rustc_data_structures::fx::FxHashSet;
use rustc_errors::Applicability;
use rustc_lint::{EarlyLintPass, EarlyContext};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::{Span};
use rustc_span::symbol::Ident;
use rustc_ast::ast::*;
use rustc_ast::ptr::P;

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

            for (i, BinaryOp{ left, right, .. }) in binops.iter().enumerate() {
                match ident_difference(left, right) {
                    IdentDifference::NoDifference => {
                        // The `eq_op` lint should catch this if it's an issue.
                        return;
                    }
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
                    }
                    IdentDifference::Double(ident_loc1, ident_loc2) => {
                        double_difference_info = Some((i, ident_loc1, ident_loc2));
                    }
                    IdentDifference::Multiple | IdentDifference::NonIdentDifference => {
                        // It's too hard to know whether this is a bug or not.
                        // TODO: Do we need to recurse in order to find known
                        // buggy expressions inside complicated ones?
                        return;
                    }
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
                            SUSPICIOUS_CHAINED_OPERATORS,
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
        (true, true)|(false, false) => {
            // We don't have a good guess of what ident should be 
            // used instead, in these cases.
            *applicability = Applicability::MaybeIncorrect;

            // We arbitraily choose one side to suggest changing,
            // since we don't have a better guess. If the user 
            // ends up duplicating a clause, the `logic_bug` lint
            // should catch it.

            let right_suggestion = suggestion_with_swapped_ident(
                cx,
                &binop.right,
                location,
                left_ident,
                applicability,
            )?;

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

            let right_suggestion = suggestion_with_swapped_ident(
                cx,
                &binop.right,
                location,
                left_ident,
                applicability,
            )?;

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
            let left_suggestion = suggestion_with_swapped_ident(
                cx,
                &binop.left,
                location,
                right_ident,
                applicability,
            )?;

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

fn chained_binops(kind: &ExprKind) -> Option<Vec<BinaryOp>> {
    todo!()
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct IdentLocation {
    index: usize,
}

enum IdentDifference {
    NoDifference,
    Single(IdentLocation, Ident),
    Double(IdentLocation, IdentLocation),
    Multiple,
    NonIdentDifference,
}

fn ident_difference(left: &Expr, right: &Expr) -> IdentDifference {
    // This function cannot use IdentIter because it should return early
    // if the expressions have any non-ident differences.
    todo!()
}

fn get_ident(expr: &Expr, location: IdentLocation) -> Option<Ident> {
    IdentIter::new(expr)
        .nth(location.index)
        .map(|(ident, _)| ident)
}

fn suggestion_with_swapped_ident(
    cx: &EarlyContext<'_>,
    expr: &Expr,
    location: IdentLocation,
    ident: Ident,
    applicability: &mut Applicability,
) -> Option<String> {
    IdentIter::new(expr)
        .nth(location.index)
        .map(|(current_ident, current_expr)| {
            format!(
                "{}{}{}",
                snippet_with_applicability(
                    cx,
                    current_expr.span
                        .with_hi(current_ident.span.lo()),
                    "..",
                    applicability
                ),
                current_ident.to_string(),
                snippet_with_applicability(
                    cx,
                    current_expr.span
                        .with_lo(current_ident.span.hi()),
                    "..",
                    applicability
                ),
            )
        })
}

type Inner<'a> = Box<dyn Iterator<Item = Ident> + 'a>;

struct IdentIter<'expr> {
    expr: Option<&'expr Expr>,
    inner: Option<Inner<'expr>>,
}

impl <'expr> IdentIter<'expr> {
    fn new(expr: &'expr Expr) -> Self {
        Self {
            expr: Some(expr),
            inner: None,
        }
    }
}

impl <'expr> Iterator for IdentIter<'expr> {
    type Item = (Ident, &'expr Expr);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(current_expr) = self.expr.take() {
            let (ident_opt, next_expr) = next_option_pair(
                &current_expr,
                &mut self.inner,
            );

            self.expr = next_expr;

            ident_opt.map(move |ident| (ident, current_expr))
        } else {
            None
        }
    }
}

fn next_option_pair<'expr>(
    current_expr: &'expr Expr,
    inner_opt: &mut Option<Inner<'expr>>,
) -> (Option<Ident>, Option<&'expr Expr>) {
    if let Some(mut inner) = inner_opt.take() {
        let output = inner.next();

        if output.is_some() {
            *inner_opt = Some(inner);
            return (output, Some(current_expr));
        }
    }

    match current_expr.kind {
        ExprKind::Lit(_)|ExprKind::Err => (None, None),
        ExprKind::Path(_, ref path)
        | ExprKind::MacCall(MacCall{ ref path, ..}) => {
            let mut p_iter = path.segments.iter().map(|s| s.ident);
            let next_ident = p_iter.next();

            *inner_opt = Some(Box::new(p_iter));

            (next_ident, Some(current_expr))
        },
        ExprKind::Box(ref expr) => {
            let mut e_iter = IdentIter::new(expr)
                // TODO: should I actually be passing this _expr back up each time?
                .map(|(ident, _expr)| ident);
            let next_ident = e_iter.next();

            *inner_opt = Some(Box::new(e_iter));

            (next_ident, Some(expr))
        },
        _ => todo!(),
    }
}

impl <'expr> FusedIterator for IdentIter<'expr> {}