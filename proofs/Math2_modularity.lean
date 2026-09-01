/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the statement of the modularity theorem (Taniyama–Shimura–Wiles)
for elliptic curves over `ℚ`, given by integral Weierstrass models, together with a
fully kernel-checked numerical verification of the modularity prediction for the
elliptic curve `11a1 : y² + y = x³ - x² - 10x - 20`, whose associated newform is the
eta product `η(z)² η(11z)²`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Math2

open WeierstrassCurve CongruenceSubgroup MatrixGroups ModularFormClass UpperHalfPlane

/-! ## Point counts of the reductions of a Weierstrass model -/

/-- The number of points of the reduction mod `p` of an integral Weierstrass model `W`:
the affine solutions of the Weierstrass equation over `ℤ/p`, plus the point at infinity.
(For `p = 0` this is junk, and it is only used for primes of good reduction.) -/
noncomputable def cardPoints (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card {q : ZMod p × ZMod p //
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation q.1 q.2} + 1

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` of an integral Weierstrass model. -/
noncomputable def ap (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ := (p : ℤ) + 1 - cardPoints W p

/-! ## The statement of modularity -/

/-- An integral Weierstrass model `W` is *modular* if there is a level `N ≥ 1` and a
weight-two cusp form `f` for `Γ₀(N)`, normalised so that its first `q`-expansion
coefficient is `1`, whose `p`-th `q`-expansion coefficient equals the trace of Frobenius
`a_p(W)` for every prime `p` not dividing `N` and of good reduction.

Equivalently, the `L`-series of the curve is the Mellin transform of a weight-two cusp
form of level `N`; by strong multiplicity one, prescribing the coefficients at the
primes away from `N` and from the discriminant determines the situation. -/
def IsModular (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2,
    (qExpansion 1 (f : ℍ → ℂ)).coeff 1 = 1 ∧
      ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ (N : ℤ) * W.Δ) →
        (qExpansion 1 (f : ℍ → ℂ)).coeff p = (ap W p : ℂ)

/-- **The modularity theorem** (Taniyama–Shimura–Wiles), as a statement: every elliptic
curve over `ℚ` — equivalently, every nonsingular integral Weierstrass model, i.e. one with
nonvanishing discriminant — is modular. -/
def modularity : Prop := ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → IsModular W

/-! ## The curve `11a1` and its newform -/

/-- The elliptic curve `11a1 : y² + y = x³ - x² - 10x - 20`, of conductor `11`. -/
def W11a1 : WeierstrassCurve ℤ := ⟨0, -1, 1, -10, -20⟩

/-- Multiplication of a truncated power series (given by its list of coefficients)
by `1 - qᵏ`. -/
def mulOneSub (k : ℕ) (c : List ℤ) : List ℤ :=
  (List.range c.length).map fun n => c.getD n 0 - if k ≤ n then c.getD (n - k) 0 else 0

/-- The coefficients of `q * ∏_{n=1}^{M} (1 - qⁿ)² (1 - q^{11n})²`, i.e. of the eta
product `η(z)² η(11z)²`, truncated: this list has length `M + 2` and its entries in
positions `0, …, M + 1` are the true coefficients of the eta product. -/
def etaList (M : ℕ) : List ℤ :=
  (List.range' 1 M).foldl
    (fun c n => mulOneSub n (mulOneSub n (mulOneSub (11 * n) (mulOneSub (11 * n) c))))
    (0 :: 1 :: List.replicate M 0)

/-- The `n`-th `q`-expansion coefficient of the weight-two level-eleven newform
`η(z)² η(11z)² = q ∏_{n ≥ 1} (1 - qⁿ)² (1 - q^{11n})²`. -/
def newform11Coeff (n : ℕ) : ℤ := (etaList n).getD n 0

/-! ## Basic lemmas -/

/-- The Weierstrass equation over `ℤ/p`, written out explicitly. -/
lemma equation_map_iff (W : WeierstrassCurve ℤ) (p : ℕ) (x y : ZMod p) :
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ZMod p) * x * y + (W.a₃ : ZMod p) * y
        = x ^ 3 + (W.a₂ : ZMod p) * x ^ 2 + (W.a₄ : ZMod p) * x + (W.a₆ : ZMod p) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Int.coe_castRingHom, WeierstrassCurve.toAffine,
    Int.cast_id]
  constructor <;> intro h <;> linear_combination h

/-- The point count as an explicit, decidable `Finset` cardinality. -/
lemma cardPoints_eq_filter_card (W : WeierstrassCurve ℤ) (p : ℕ) [NeZero p] :
    cardPoints W p =
      (Finset.univ.filter fun q : ZMod p × ZMod p =>
        q.2 ^ 2 + (W.a₁ : ZMod p) * q.1 * q.2 + (W.a₃ : ZMod p) * q.2
          = q.1 ^ 3 + (W.a₂ : ZMod p) * q.1 ^ 2 + (W.a₄ : ZMod p) * q.1
            + (W.a₆ : ZMod p)).card + 1 := by
  classical
  rw [cardPoints]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro q _
  simpa using equation_map_iff W p q.1 q.2

/-! ## Numerical verification of modularity for `11a1` -/

/-- The trace of Frobenius of `11a1` at a prime `p`, as an explicitly computable quantity. -/
lemma ap_11a1_eq (p : ℕ) [NeZero p] :
    ap W11a1 p = (p : ℤ) + 1 -
      ((Finset.univ.filter fun q : ZMod p × ZMod p =>
        q.2 ^ 2 + q.2 = q.1 ^ 3 + (-1 : ZMod p) * q.1 ^ 2 + (-10 : ZMod p) * q.1
          + (-20 : ZMod p)).card + 1) := by
  rw [ap, cardPoints_eq_filter_card]
  norm_num [W11a1]

end Math2

section Test
open Math2
example : newform11Coeff 13 = ap W11a1 13 := by
  rw [ap_11a1_eq]
  decide
end Test

