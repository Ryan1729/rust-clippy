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

impl EarlyLintPass for SuspiciousChainedOperators {}
