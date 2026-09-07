import Mathlib

/-! # Phase-Depth Transfer: block-cyclic cycle-structure (the dynamical KEY toward the determinant identity, which is deferred)

For a fiber `A` (an `AddCommGroup`, `Fintype`, `DecidableEq`) and a roof `c : ZMod 5 → A`,
the **transfer permutation** on the state space `S = ZMod 5 × A` is
`σ_c(j, a) = (j + 1, a + c j)`.  Writing `H = ∑ j, c j` for the *total holonomy* and
`ρ(H) : A → A := (· + H)`, the block-cyclic transfer determinant identity is
`det(I − z·T_c) = det(I − z⁵·ρ(H))`, where `T_c`, `ρ(H)` are the permutation matrices of
`σ_c`, `ρ(H)`.

**What this file proves (AXLE-clean, env `lean-4.32.2`).** The *dynamical heart* of that
determinant identity — the exact orbit/period structure that forces the two characteristic
determinants to coincide:

* `sigma_iterate` — the closed form `σ_c^[n](j,a) = (j + n, a + ∑_{i<n} c(j+i))`.
* `sigma_five` / `sigma_5k` — `σ_c^[5k](j,a) = (j, a + k•H)`: a residue lap adds one `H`.
* `sigma_period` — **THE KEY**: `σ_c^[m](j,a) = (j,a) ↔ 5·ord(H) ∣ m`.
* `sigma_minimalPeriod` — every point has minimal period *exactly* `5·ord(H)`.
* `sigma_bijective` / `sigmaPerm` — `σ_c` is a genuine permutation of `S`
  (so `T_c` is a permutation matrix); `sigma_no_fixedPoints` — it moves every point.
* `rho_period` / `rho_minimalPeriod` — the fiber map `ρ(H)` has minimal period `ord(H)`.
* `cycle_length_bridge` — every `σ_c`-cycle is *exactly five times* the length of the
  corresponding `ρ(H)`-cycle: `minimalPeriod σ_c = 5 · minimalPeriod ρ(H)`.

Together these give: `σ_c` is a disjoint union of `|A|/ord(H)` cycles of length `5·ord(H)`,
while `ρ(H)` is `|A|/ord(H)` cycles of length `ord(H)` — so both determinants equal
`(1 − z^{5·ord(H)})^{|A|/ord(H)}`.  Turning the *equal cycle-length multisets* into the
matrix determinant equality is the one link **not** carried out here — see the note at the
end of the file for the precise Mathlib gap. -/

namespace Brockian.PhaseDepthCycles

open Finset

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Total holonomy `H = ∑ j, c j`. -/
def Htot (c : ZMod 5 → A) : A := ∑ r : ZMod 5, c r

/-- The transfer permutation `σ_c(j,a) = (j+1, a + c j)` on `S = ZMod 5 × A`. -/
def sigmaMap (c : ZMod 5 → A) (x : ZMod 5 × A) : ZMod 5 × A := (x.1 + 1, x.2 + c x.1)

/-- The fiber roof map `ρ(H)(a) = a + H`. -/
def rhoMap (H : A) : A → A := fun a => a + H

/-! ## Iteration closed form for `σ_c` -/

/-- Closed form: `σ_c^[n](j,a) = (j + n, a + ∑_{i<n} c(j+i))`. -/
theorem sigma_iterate (c : ZMod 5 → A) (n : ℕ) (x : ZMod 5 × A) :
    (sigmaMap c)^[n] x = (x.1 + n, x.2 + ∑ i ∈ Finset.range n, c (x.1 + i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [sigmaMap, Finset.sum_range_succ]
    refine Prod.ext ?_ ?_
    · push_cast; ring
    · push_cast; abel

/-- A full residue lap sums the roof over all residues, independent of the start point. -/
theorem sum_shift (c : ZMod 5 → A) (j : ZMod 5) :
    ∑ i ∈ Finset.range 5, c (j + i) = Htot c := by
  have hB : ∑ r : ZMod 5, c (j + r) = ∑ r : ZMod 5, c r :=
    Equiv.sum_comp (Equiv.addLeft j) c
  have hA : ∑ i ∈ Finset.range 5, c (j + (i : ZMod 5)) = ∑ r : ZMod 5, c (j + r) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => c (j + (i : ZMod 5))) 5]
    rfl
  rw [hA, hB]
  rfl

/-- Five steps advance the depth by the total holonomy, fixing the residue. -/
theorem sigma_five (c : ZMod 5 → A) (x : ZMod 5 × A) :
    (sigmaMap c)^[5] x = (x.1, x.2 + Htot c) := by
  rw [sigma_iterate]
  refine Prod.ext ?_ ?_
  · show x.1 + ((5 : ℕ) : ZMod 5) = x.1
    rw [ZMod.natCast_self]; ring
  · show x.2 + ∑ i ∈ Finset.range 5, c (x.1 + i) = x.2 + Htot c
    rw [sum_shift]

/-- `σ_c^{5k}(j,a) = (j, a + k•H)`. -/
theorem sigma_5k (c : ZMod 5 → A) (k : ℕ) :
    ∀ x : ZMod 5 × A, (sigmaMap c)^[5 * k] x = (x.1, x.2 + k • Htot c) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have h1 : 5 * (k + 1) = 5 + 5 * k := by ring
    rw [h1, Function.iterate_add_apply, ih, sigma_five]
    refine Prod.ext rfl ?_
    show (x.2 + k • Htot c) + Htot c = x.2 + (k + 1) • Htot c
    rw [succ_nsmul]; abel

/-! ## The period lemma — the mathematical KEY -/

/-- **The period lemma.** Every point of `S` returns under `σ_c` exactly at the multiples
    of `5 · ord(H)`. -/
theorem sigma_period (c : ZMod 5 → A) (x : ZMod 5 × A) (m : ℕ) :
    (sigmaMap c)^[m] x = x ↔ 5 * addOrderOf (Htot c) ∣ m := by
  constructor
  · intro h
    have hiter : (x.1 + (m : ZMod 5), x.2 + ∑ i ∈ Finset.range m, c (x.1 + i)) = x := by
      rw [← sigma_iterate]; exact h
    have hfst : x.1 + (m : ZMod 5) = x.1 := congrArg Prod.fst hiter
    have hm5 : (m : ZMod 5) = 0 := by
      have h2 : x.1 + (m : ZMod 5) = x.1 + 0 := by rw [add_zero]; exact hfst
      exact add_left_cancel h2
    have hdvd5 : (5 : ℕ) ∣ m := by
      rwa [CharP.cast_eq_zero_iff (ZMod 5) 5] at hm5
    obtain ⟨k, rfl⟩ := hdvd5
    have hk := sigma_5k c k x
    rw [hk] at h
    have hsnd : x.2 + k • Htot c = x.2 := congrArg Prod.snd h
    have hz : k • Htot c = 0 := by
      have h2 : x.2 + k • Htot c = x.2 + 0 := by rw [add_zero]; exact hsnd
      exact add_left_cancel h2
    have hordk : addOrderOf (Htot c) ∣ k := addOrderOf_dvd_of_nsmul_eq_zero hz
    exact mul_dvd_mul_left 5 hordk
  · intro h
    obtain ⟨t, ht⟩ := h
    have hm : m = 5 * (addOrderOf (Htot c) * t) := by rw [ht]; ring
    rw [hm, sigma_5k]
    refine Prod.ext rfl ?_
    show x.2 + (addOrderOf (Htot c) * t) • Htot c = x.2
    have hz : (addOrderOf (Htot c) * t) • Htot c = 0 := by
      rw [mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero]
    rw [hz, add_zero]

/-- The minimal period of every point of `S` is exactly `5 · ord(H)`. -/
theorem sigma_minimalPeriod (c : ZMod 5 → A) (x : ZMod 5 × A) :
    Function.minimalPeriod (sigmaMap c) x = 5 * addOrderOf (Htot c) := by
  apply Nat.dvd_antisymm
  · rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    show (sigmaMap c)^[5 * addOrderOf (Htot c)] x = x
    rw [sigma_period]
  · have hp : (sigmaMap c)^[Function.minimalPeriod (sigmaMap c) x] x = x :=
      Function.isPeriodicPt_minimalPeriod (sigmaMap c) x
    rwa [sigma_period] at hp

/-! ## `σ_c` is a genuine permutation of `S` (so `T_c` is a permutation matrix) -/

theorem sigma_injective (c : ZMod 5 → A) : Function.Injective (sigmaMap c) := by
  intro x y h
  simp only [sigmaMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hx1 : x.1 = y.1 := add_right_cancel h1
  have hx2 : x.2 = y.2 := by
    rw [hx1] at h2
    exact add_right_cancel h2
  exact Prod.ext hx1 hx2

theorem sigma_bijective (c : ZMod 5 → A) : Function.Bijective (sigmaMap c) :=
  (Finite.injective_iff_bijective).mp (sigma_injective c)

/-- `σ_c` bundled as a permutation of `S`; its permutation matrix is `T_c`. -/
noncomputable def sigmaPerm (c : ZMod 5 → A) : Equiv.Perm (ZMod 5 × A) :=
  Equiv.ofBijective (sigmaMap c) (sigma_bijective c)

/-- `σ_c` has no fixed points (the residue always advances), so `ord(H) ≥ 1` cycles all
    have length `5·ord(H) ≥ 5 > 1`. -/
theorem sigma_no_fixedPoints (c : ZMod 5 → A) (x : ZMod 5 × A) : sigmaMap c x ≠ x := by
  intro h
  have hfst : x.1 + 1 = x.1 := congrArg Prod.fst h
  have h0 : (1 : ZMod 5) = 0 := by
    have h2 : x.1 + 1 = x.1 + 0 := by rw [add_zero]; exact hfst
    exact add_left_cancel h2
  exact absurd h0 (by decide)

/-! ## The fiber map `ρ(H)` and the cycle-length correspondence -/

/-- Closed form for the fiber roof map: `ρ(H)^[m](a) = a + m•H`. -/
theorem rho_iterate (H : A) (m : ℕ) (a : A) : (rhoMap H)^[m] a = a + m • H := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [rhoMap, succ_nsmul]
    abel

/-- `ρ(H)^[m](a) = a ↔ ord(H) ∣ m`. -/
theorem rho_period (H : A) (a : A) (m : ℕ) : (rhoMap H)^[m] a = a ↔ addOrderOf H ∣ m := by
  rw [rho_iterate]
  constructor
  · intro h
    have hz : m • H = 0 := by
      have h2 : a + m • H = a + 0 := by rw [add_zero]; exact h
      exact add_left_cancel h2
    exact addOrderOf_dvd_of_nsmul_eq_zero hz
  · intro h
    obtain ⟨t, rfl⟩ := h
    have hz : (addOrderOf H * t) • H = 0 := by
      rw [mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero]
    rw [hz, add_zero]

/-- The minimal period of every fiber point under `ρ(H)` is exactly `ord(H)`. -/
theorem rho_minimalPeriod (H : A) (a : A) :
    Function.minimalPeriod (rhoMap H) a = addOrderOf H := by
  apply Nat.dvd_antisymm
  · rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    show (rhoMap H)^[addOrderOf H] a = a
    rw [rho_period]
  · have hp : (rhoMap H)^[Function.minimalPeriod (rhoMap H) a] a = a :=
      Function.isPeriodicPt_minimalPeriod (rhoMap H) a
    rwa [rho_period] at hp

/-- **Cycle-length correspondence.** Every `σ_c`-cycle on `S` is exactly *five times* as
    long as the corresponding `ρ(H)`-cycle on `A`. This is the dynamical content that makes
    `det(I − z·T_c) = ∏ (1 − z^{5·ord}) = (1 − z^{5·ord})^{|A|/ord}` coincide with
    `det(I − z⁵·ρ(H)) = ∏ (1 − (z⁵)^{ord}) = (1 − z^{5·ord})^{|A|/ord}`. -/
theorem cycle_length_bridge (c : ZMod 5 → A) (x : ZMod 5 × A) (a : A) :
    Function.minimalPeriod (sigmaMap c) x = 5 * Function.minimalPeriod (rhoMap (Htot c)) a := by
  rw [sigma_minimalPeriod, rho_minimalPeriod]

/-- Bundled summary of the verified dynamical KEY behind the determinant identity. -/
theorem phase_depth_key (c : ZMod 5 → A) (x : ZMod 5 × A) (a : A) :
    (∀ m, (sigmaMap c)^[m] x = x ↔ 5 * addOrderOf (Htot c) ∣ m) ∧
    Function.minimalPeriod (sigmaMap c) x = 5 * addOrderOf (Htot c) ∧
    Function.minimalPeriod (rhoMap (Htot c)) a = addOrderOf (Htot c) ∧
    Function.minimalPeriod (sigmaMap c) x
      = 5 * Function.minimalPeriod (rhoMap (Htot c)) a ∧
    Function.Bijective (sigmaMap c) ∧
    sigmaMap c x ≠ x :=
  ⟨fun m => sigma_period c x m, sigma_minimalPeriod c x, rho_minimalPeriod (Htot c) a,
    cycle_length_bridge c x a, sigma_bijective c, sigma_no_fixedPoints c x⟩

/-!
## Determinant assembly — the remaining link and its precise Mathlib gap

The results above establish, fully and AXLE-cleanly, that `σ_c` and `ρ(H)` have matching
cycle *structure*: `|A|/ord(H)` cycles each, of respective lengths `5·ord(H)` and `ord(H)`.
For a permutation matrix `P` of a permutation with `cycleType = {ℓ₁, …, ℓ_r}`, one has the
characteristic-determinant factorization
  `det(1 − z • P) = ∏_{k} (1 − z^{ℓ_k})`,
whence both sides of the target reduce to `(1 − z^{5·ord(H)})^{|A|/ord(H)}` and are equal.

Mathlib (as of `lean-4.32.2` / current) does **not** provide that factorization lemma:
there is `Matrix.det_permutation` (`det P = sign σ`) and the full `Equiv.Perm.cycleType`
API (`Equiv.Perm.sum_cycleType`, `mem_cycleType_iff`, …), but no
`det (1 − z • permMatrix σ) = ∏_{ℓ ∈ σ.cycleType} (1 − z^ℓ)` (nor a `charpoly`-of-a-
permutation-matrix result stated by cycle type). Supplying it requires a genuine new
development (block/cycle change-of-basis to circulant form, then the cyclic
`det(1 − z·shift) = 1 − z^n`), which is exactly "the hardest link" of the program.

A *concrete* witness (Step 4) is likewise blocked at the kernel level: the smallest
nontrivial fiber `A = ZMod 2` gives a `10×10` matrix `T_c` over `Polynomial ℤ`, and Lean's
`decide`/`Matrix.det` cannot evaluate it — there is no `Matrix.det_fin_ten` unfolding lemma,
`det` over `Polynomial ℤ` is not `Decidable`, and `native_decide` is disallowed by the AXLE
axiom policy. Evaluating even a fixed-`z` integer instance would require summing over
`10! ≈ 3.6·10⁶` permutations in the kernel, which is infeasible.

Hence the honest status: the orbit/period KEY and the cycle-length correspondence are
proved; the passage to the matrix determinant is deferred to the missing factorization
lemma.
-/

end Brockian.PhaseDepthCycles
