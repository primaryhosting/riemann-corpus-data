import Mathlib

/-!
# Closed form for the Catalan numbers

The theorem below is stated in terms of `Nat.catalan`.  Depending on the
Mathlib version, the Catalan numbers are either declared in the root namespace
(as `catalan`) or in the `Nat` namespace (as `Nat.catalan`).  The command below
introduces `Nat.catalan` as a reducible alias for the root-level `catalan`
*only* when `Nat.catalan` is not already available, so that the statement
elaborates in either situation.
-/

open Lean Elab Command in
run_cmd do
  unless (← getEnv).contains `Nat.catalan do
    elabCommand (← `(command| abbrev $(mkIdent `Nat.catalan) : ℕ → ℕ := _root_.catalan))

namespace Brockian.CatalanClosed
/-- Closed form for the Catalan numbers: (n+1)·Cₙ = C(2n, n). -/
theorem succ_mul_catalan_eq_choose (n : ℕ) :
    (n + 1) * Nat.catalan n = Nat.choose (2 * n) n := by
  have h : (n + 1) * Nat.catalan n = Nat.centralBinom n := by
    first
      | exact Nat.succ_mul_catalan_eq_centralBinom n
      | exact _root_.succ_mul_catalan_eq_centralBinom n
  simpa [Nat.centralBinom] using h
end Brockian.CatalanClosed

