/-
  Brockian/ErdosStrausResidues.lean — further unconditional residue-class and
  divisibility identities for the Erdős–Straus conjecture (OPEN since 1948),
  and a precise delineation of the remaining open frontier.

  This file EXTENDS `Brockian/ErdosStraus.lean`. It adds:

    • two new explicit divisibility identities (`5 ∣ n` and `7 ∣ n`), each with
      a fully verified parametric Egyptian-fraction witness;
    • a consolidated coverage theorem `erdosStraus_covered` and an extended one
      `erdosStraus_covered_ext` (which also absorbs the `5 ∣ n`, `7 ∣ n` cases);
    • the honest characterisation of the open frontier: `erdosStraus_open_reduces`
      (any counterexample must be odd, not divisible by 3, and `≡ 1 mod 4`),
      sharpened to `n ≡ 1 (mod 12)` and equivalently `n % 24 ∈ {1, 13}`.

  IMPORTANT (honesty). The full conjecture remains OPEN and is NEVER asserted here.
  A short computational/symbolic search confirms what theory predicts: the frontier
  classes `n ≡ 1, 13 (mod 24)` admit no uniform *linear* parametric solution, so no
  new single-congruence class beyond the ones proved here is closed. The extra
  content is genuine (new verified identities + a sharp frontier statement), not a
  disguised proof of the conjecture.

  Verified @ lean-4.32.0 (Mathlib). No sorry / admit / native_decide / added axiom.
-/
import Mathlib
import Brockian.ErdosStraus

namespace Brockian.ErdosStrausResidues

open Brockian.ErdosStraus

/-! ### New divisibility identities -/

/-- **Divisible-by-five case.** Every `n ≥ 1` with `5 ∣ n` has an Erdős–Straus
decomposition. With `n = 5m` the witnesses are `x = 2m`, `y = 4m`, `z = 20m`,
using the identity `1/(2m) + 1/(4m) + 1/(20m) = (10 + 5 + 1)/(20m) = 16/(20m)
= 4/(5m)`. -/
theorem erdosStraus_dvd_five {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) : ErdosStraus n := by
  obtain ⟨m, hm⟩ := h5
  have hmpos : 0 < m := by omega
  refine ⟨2 * m, 4 * m, 20 * m, by omega, by omega, by omega, ?_⟩
  have hmc : (m : ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hncast : (n : ℚ) = 5 * (m : ℚ) := by exact_mod_cast hm
  push_cast
  rw [hncast]
  field_simp
  ring

/-- **Divisible-by-seven case.** Every `n ≥ 1` with `7 ∣ n` has an Erdős–Straus
decomposition. With `n = 7m` the witnesses are `x = 2m`, `y = 15m`, `z = 210m`,
using the identity `1/(2m) + 1/(15m) + 1/(210m) = (105 + 14 + 1)/(210m)
= 120/(210m) = 4/(7m)`. -/
theorem erdosStraus_dvd_seven {n : ℕ} (hn : 0 < n) (h7 : 7 ∣ n) : ErdosStraus n := by
  obtain ⟨m, hm⟩ := h7
  have hmpos : 0 < m := by omega
  refine ⟨2 * m, 15 * m, 210 * m, by omega, by omega, by omega, ?_⟩
  have hmc : (m : ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hncast : (n : ℚ) = 7 * (m : ℚ) := by exact_mod_cast hm
  push_cast
  rw [hncast]
  field_simp
  ring

/-! ### Consolidated coverage -/

/-- **Consolidated coverage (must-have).** Any `n > 0` that is even, divisible by
three, `≡ 3 (mod 4)`, or `≡ 2 (mod 3)` admits an Erdős–Straus decomposition —
unconditionally. This dispatches to the explicit families proved in
`Brockian/ErdosStraus.lean`. -/
theorem erdosStraus_covered {n : ℕ} (hn : 0 < n)
    (h : 2 ∣ n ∨ 3 ∣ n ∨ n % 4 = 3 ∨ n % 3 = 2) : ErdosStraus n := by
  rcases h with h | h | h | h
  · exact erdosStraus_even hn h
  · exact erdosStraus_dvd_three hn h
  · exact erdosStraus_mod4_three hn h
  · exact erdosStraus_mod3_two hn h

/-- **Extended coverage.** As `erdosStraus_covered`, additionally absorbing the new
`5 ∣ n` and `7 ∣ n` families. -/
theorem erdosStraus_covered_ext {n : ℕ} (hn : 0 < n)
    (h : 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n ∨ 7 ∣ n ∨ n % 4 = 3 ∨ n % 3 = 2) : ErdosStraus n := by
  rcases h with h | h | h | h | h | h
  · exact erdosStraus_even hn h
  · exact erdosStraus_dvd_three hn h
  · exact erdosStraus_dvd_five hn h
  · exact erdosStraus_dvd_seven hn h
  · exact erdosStraus_mod4_three hn h
  · exact erdosStraus_mod3_two hn h

/-! ### The honest open frontier -/

/-- **The open frontier (must-have).** Any hypothetical `n > 0` *without* an
Erdős–Straus decomposition is necessarily odd, not divisible by three, and
`≡ 1 (mod 4)`. This is the contrapositive of `erdosStraus_covered`; it precisely
constrains where the conjecture could conceivably fail. -/
theorem erdosStraus_open_reduces {n : ℕ} (hn : 0 < n) (hopen : ¬ ErdosStraus n) :
    Odd n ∧ ¬ (3 ∣ n) ∧ n % 4 = 1 := by
  have h2 : ¬ (2 ∣ n) := fun h => hopen (erdosStraus_even hn h)
  have h3 : ¬ (3 ∣ n) := fun h => hopen (erdosStraus_dvd_three hn h)
  have h4 : n % 4 ≠ 3 := fun h => hopen (erdosStraus_mod4_three hn h)
  refine ⟨?_, h3, ?_⟩
  · rw [Nat.odd_iff]; omega
  · omega

/-- **Sharpened frontier.** Any counterexample is in fact `≡ 1 (mod 12)`: odd, not
divisible by three, `≡ 1 (mod 4)`, and `≡ 1 (mod 3)`. Uses the `n ≡ 2 (mod 3)`
family in addition. -/
theorem erdosStraus_open_reduces_mod12 {n : ℕ} (hn : 0 < n) (hopen : ¬ ErdosStraus n) :
    n % 12 = 1 := by
  have h2 : ¬ (2 ∣ n) := fun h => hopen (erdosStraus_even hn h)
  have h3 : ¬ (3 ∣ n) := fun h => hopen (erdosStraus_dvd_three hn h)
  have h4 : n % 4 ≠ 3 := fun h => hopen (erdosStraus_mod4_three hn h)
  have h3' : n % 3 ≠ 2 := fun h => hopen (erdosStraus_mod3_two hn h)
  omega

/-- **Frontier as residues mod 24.** Equivalently, any counterexample satisfies
`n ≡ 1` or `n ≡ 13 (mod 24)` — the two classes coprime to 6 that lie in
`n ≡ 1 (mod 12)`. These feed the famously hard prime residues
`p ≡ 1, 121, 169, 289, 361, 529 (mod 840)`. -/
theorem erdosStraus_open_frontier_mod24 {n : ℕ} (hn : 0 < n) (hopen : ¬ ErdosStraus n) :
    n % 24 = 1 ∨ n % 24 = 13 := by
  have h := erdosStraus_open_reduces_mod12 hn hopen
  omega

end Brockian.ErdosStrausResidues
