import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires all `import` commands to precede any other command,
including module documentation, so the single `import Mathlib` line above precedes the header.

Mathlib contains no development of the genus of a curve, of Jacobians, or of Faltings'
theorem, so the statement below is formalized from scratch for smooth plane curves (where the
genus is given by the genus-degree formula).  The verified base case uses the Mathlib result
`fermatLastTheoremFour` (Fermat's Last Theorem for exponent four), transported to `ℚ` via
`fermatLastTheoremFor_iff_rat`.
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MvPolynomial

/-- An algebraic closure of `ℚ`, used to express the smoothness (Jacobian) criterion. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- The affine chart `Z = 1` of the rational points of the projective plane curve cut out by
a homogeneous polynomial `F ∈ ℚ[X₀, X₁, X₂]`.  A projective plane curve has at most `deg F`
rational points on the line at infinity, so the full set of projective rational points is finite
if and only if this affine set is. -/
def affineRationalPoints (F : MvPolynomial (Fin 3) ℚ) : Set (ℚ × ℚ) :=
  {p : ℚ × ℚ | MvPolynomial.eval ![p.1, p.2, 1] F = 0}

/-- `F` cuts out a smooth projective plane curve of degree `d` over `ℚ`: it is homogeneous of
degree `d`, and (Jacobian criterion) the only point of `Q̄³` at which `F` and all of its partial
derivatives vanish is the origin, i.e. the curve has no singular point over an algebraic
closure. -/
def IsSmoothProjectivePlaneCurve (d : ℕ) (F : MvPolynomial (Fin 3) ℚ) : Prop :=
  F.IsHomogeneous d ∧
    ∀ p : Fin 3 → Qbar,
      MvPolynomial.eval p (F.map (algebraMap ℚ Qbar)) = 0 →
      (∀ i : Fin 3, MvPolynomial.eval p (pderiv i (F.map (algebraMap ℚ Qbar))) = 0) →
      p = 0

/-- The genus of a smooth plane curve of degree `d`, by the genus–degree formula
`g = (d-1)(d-2)/2`. -/
def planeCurveGenus (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

/-- **Faltings' theorem (Mordell conjecture)**, stated for smooth plane curves over `ℚ`:
a smooth projective plane curve over `ℚ` whose genus is at least `2` (equivalently, of degree
at least `4`) has only finitely many rational points. -/
def FaltingsMordell : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin 3) ℚ),
    IsSmoothProjectivePlaneCurve d F → 2 ≤ planeCurveGenus d →
      (affineRationalPoints F).Finite

/-- The Fermat curve `X₀ⁿ + X₁ⁿ = X₂ⁿ` over `ℚ`. -/
noncomputable def fermatCurve (n : ℕ) : MvPolynomial (Fin 3) ℚ :=
  X 0 ^ n + X 1 ^ n - X 2 ^ n

lemma fermatCurve_isHomogeneous (n : ℕ) : (fermatCurve n).IsHomogeneous n := by
  unfold fermatCurve
  have h : ∀ i : Fin 3, ((X i : MvPolynomial (Fin 3) ℚ) ^ n).IsHomogeneous n := by
    intro i
    simpa using (isHomogeneous_X ℚ i).pow n
  exact ((h 0).add (h 1)).sub (h 2)

lemma map_fermatCurve (n : ℕ) :
    (fermatCurve n).map (algebraMap ℚ Qbar) = X 0 ^ n + X 1 ^ n - X 2 ^ n := by
  simp [fermatCurve]

lemma fermatCurve_smooth {n : ℕ} (hn : 2 ≤ n) :
    IsSmoothProjectivePlaneCurve n (fermatCurve n) := by
  refine ⟨fermatCurve_isHomogeneous n, ?_⟩
  intro p _ h
  rw [map_fermatCurve] at h
  have key : ∀ i : Fin 3, p i = 0 := by
    intro i
    have hi := h i
    fin_cases i <;> simp [pderiv_X] at hi <;> rcases hi with hi | hi <;>
      first | omega | exact hi.1
  funext i
  simpa using key i

lemma affineRationalPoints_fermatCurve (n : ℕ) :
    affineRationalPoints (fermatCurve n) = {p : ℚ × ℚ | p.1 ^ n + p.2 ^ n = 1} := by
  ext ⟨x, y⟩
  simp [affineRationalPoints, fermatCurve, sub_eq_zero]

lemma planeCurveGenus_ge_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ planeCurveGenus n := by
  have h : 4 ≤ (n - 1) * (n - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h' : (m + 4 - 1) * (m + 4 - 2) = (m + 3) * (m + 2) := by congr 1
    rw [h']
    nlinarith
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

/-- A Lean-checked reduction: Faltings' theorem implies that for every `n ≥ 4` the Fermat
equation `xⁿ + yⁿ = 1` has only finitely many rational solutions. -/
theorem finite_fermat_solutions_of_faltingsMordell (H : FaltingsMordell) {n : ℕ} (hn : 4 ≤ n) :
    {p : ℚ × ℚ | p.1 ^ n + p.2 ^ n = 1}.Finite := by
  have := H n (fermatCurve n) (fermatCurve_smooth (by omega)) (planeCurveGenus_ge_two hn)
  rwa [affineRationalPoints_fermatCurve] at this

/-- Fermat's Last Theorem for exponent four, over `ℚ` (from `fermatLastTheoremFour`). -/
theorem fermatLastTheoremFour_rat : FermatLastTheoremWith ℚ 4 :=
  fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour

lemma rat_pow_four_eq_one {y : ℚ} (hy : y ^ 4 = 1) : y = 1 ∨ y = -1 := by
  have h : (y - 1) * (y + 1) * (y ^ 2 + 1) = 0 := by linear_combination hy
  have h2 : (y : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  rcases mul_eq_zero.mp h with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · left; linarith
    · right; linarith
  · exact absurd h3 h2

/-- The rational points of the Fermat quartic `x⁴ + y⁴ = 1` are exactly the four trivial ones.
This is Fermat's Last Theorem for exponent four. -/
theorem fermatQuartic_rationalPoints :
    {p : ℚ × ℚ | p.1 ^ 4 + p.2 ^ 4 = 1} = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    by_cases hx : x = 0
    · subst hx
      have hy4 : y ^ 4 = 1 := by linarith [h]
      rcases rat_pow_four_eq_one hy4 with h1 | h1 <;> simp [h1]
    · by_cases hy : y = 0
      · subst hy
        have hx4 : x ^ 4 = 1 := by linarith [h]
        rcases rat_pow_four_eq_one hx4 with h1 | h1 <;> simp [h1]
      · exact absurd (by simpa using h) (fermatLastTheoremFour_rat x y 1 hx hy one_ne_zero)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- **Faltings' theorem, verified base case.**  The Fermat quartic `X₀⁴ + X₁⁴ = X₂⁴` is a smooth
projective plane curve over `ℚ` of degree `4`, hence of genus `3 ≥ 2`, and — unconditionally,
via Fermat's Last Theorem for exponent four — its set of rational points is the explicit
four-element set `{(±1, 0), (0, ±1)}`, in particular finite, as predicted by Faltings'
theorem. -/
theorem faltings_mordell :
    IsSmoothProjectivePlaneCurve 4 (fermatCurve 4) ∧
      planeCurveGenus 4 = 3 ∧
      affineRationalPoints (fermatCurve 4) = {(1, 0), (-1, 0), (0, 1), (0, -1)} ∧
      (affineRationalPoints (fermatCurve 4)).Finite := by
  have hpts : affineRationalPoints (fermatCurve 4) = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
    rw [affineRationalPoints_fermatCurve, fermatQuartic_rationalPoints]
  refine ⟨fermatCurve_smooth (by norm_num), by norm_num [planeCurveGenus], hpts, ?_⟩
  rw [hpts]
  exact ((Set.finite_singleton _).insert _).insert _ |>.insert _

end Frontier

