/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

/-!
## The Coffman–Kundu–Wootters monogamy inequality for three qubits

A pure state of three qubits `A`, `B`, `C` is given by its amplitudes
`ψ i j k` (`i` the `A`-index, `j` the `B`-index, `k` the `C`-index).

* The *tangle* of the bipartition `A|BC` is `τ_{A(BC)} = 4 · det ρ_A`
  (equivalently `2(1 - Tr ρ_A²)` for a normalized state, see `QI.tangleA_eq_purity`).
* The two-qubit tangles `τ_{AB}`, `τ_{AC}` are the squared Wootters concurrences of the
  reduced states `ρ_{AB} = Tr_C |ψ⟩⟨ψ|` and `ρ_{AC} = Tr_B |ψ⟩⟨ψ|`.  Both reduced states
  have rank at most two, so their Wootters concurrence is `max (0, s₁ - s₂)` where
  `s₁ ≥ s₂ ≥ 0` are the singular values of the symmetric `2 × 2` matrix
  `S_{kl} = ⟨χ_k| σ_y ⊗ σ_y |χ_l^*⟩` built from the (unnormalized) conditional states
  `|χ_k⟩ = ⟨k|_C ψ`.  Since `s₁² + s₂² = ‖S‖_F²` and `s₁ s₂ = |det S|`, this gives
  `τ_{AB} = ‖S‖_F² - 2 |det S|`, which is the formula we take as the definition
  (`QI.tangleAB`, `QI.tangleAC`); the lemma `QI.tangle_of_singular_values` records that this
  is indeed `(s₁ - s₂)²`.
* The residual three-tangle is `τ_{ABC} = 4 |det S|` (four times the modulus of Cayley's
  hyperdeterminant), `QI.tangle3`.

The main results are the exact CKW identity `QI.ckw_identity`
`τ_{A(BC)} = τ_{AB} + τ_{AC} + τ_{ABC}` and the monogamy inequality
`QI.monogamy_ckw` : `τ_{AB} + τ_{AC} ≤ τ_{A(BC)}`.
-/

namespace QI

open Complex Matrix

/-- Amplitudes of a (not necessarily normalized) pure state of three qubits:
`ψ i j k` with `i` the `A`-index, `j` the `B`-index and `k` the `C`-index. -/
abbrev Amp := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The reduced density matrix of qubit `A`, `ρ_A = Tr_{BC} |ψ⟩⟨ψ|`. -/
noncomputable def rhoA (ψ : Amp) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => ∑ j, ∑ k, ψ i j k * (starRingEnd ℂ) (ψ i' j k)

/-- The complex symmetric `2 × 2` matrix `S_{kl} = ⟨χ_k| σ_y ⊗ σ_y |χ_l^*⟩` attached to the
reduced state `ρ_{AB} = Tr_C |ψ⟩⟨ψ|`, where `|χ_k⟩ = ⟨k|_C ψ`. -/
def SAB (ψ : Amp) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun k l =>
    -(ψ 0 0 k * ψ 1 1 l + ψ 0 0 l * ψ 1 1 k - ψ 0 1 k * ψ 1 0 l - ψ 0 1 l * ψ 1 0 k)

/-- The analogous matrix for the reduced state `ρ_{AC} = Tr_B |ψ⟩⟨ψ|`. -/
def SAC (ψ : Amp) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun j l =>
    -(ψ 0 j 0 * ψ 1 l 1 + ψ 0 l 0 * ψ 1 j 1 - ψ 0 j 1 * ψ 1 l 0 - ψ 0 l 1 * ψ 1 j 0)

/-- Squared Frobenius norm of a `2 × 2` complex matrix. -/
noncomputable def fro (S : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∑ i, ∑ j, normSq (S i j)

/-- The tangle of the bipartition `A|BC`, i.e. the squared concurrence
`τ_{A(BC)} = 4 det ρ_A`. -/
noncomputable def tangleA (ψ : Amp) : ℝ := 4 * ((rhoA ψ).det).re

/-- The tangle (squared Wootters concurrence) of the pair `AB`. -/
noncomputable def tangleAB (ψ : Amp) : ℝ := fro (SAB ψ) - 2 * ‖(SAB ψ).det‖

/-- The tangle (squared Wootters concurrence) of the pair `AC`. -/
noncomputable def tangleAC (ψ : Amp) : ℝ := fro (SAC ψ) - 2 * ‖(SAC ψ).det‖

/-- The residual three-tangle, four times the modulus of Cayley's hyperdeterminant. -/
noncomputable def tangle3 (ψ : Amp) : ℝ := 4 * ‖(SAB ψ).det‖

/-- Justification of the formula used for the two-qubit tangles: if `s ≥ t ≥ 0` are the
singular values of `S` (characterized by `s² + t² = ‖S‖_F²` and `s t = |det S|`), then the
squared Wootters concurrence `(s - t)²` equals `‖S‖_F² - 2 |det S|`. -/
theorem tangle_of_singular_values (S : Matrix (Fin 2) (Fin 2) ℂ) (s t : ℝ)
    (h₁ : s ^ 2 + t ^ 2 = fro S) (h₂ : s * t = ‖S.det‖) :
    (s - t) ^ 2 = fro S - 2 * ‖S.det‖ := by
  rw [← h₁, ← h₂]; ring

/-- The core algebraic identity: `4 det ρ_A = ‖S_{AB}‖_F² + ‖S_{AC}‖_F²`.  Both sides are the
sum of the squared moduli of the six `2 × 2` minors of the `2 × 4` amplitude matrix. -/
theorem four_det_rhoA (ψ : Amp) :
    (4 : ℂ) * (rhoA ψ).det = ((fro (SAB ψ) + fro (SAC ψ) : ℝ) : ℂ) := by
  simp only [rhoA, SAB, SAC, fro, Matrix.det_fin_two, Matrix.of_apply, Fin.sum_univ_two,
    Complex.ofReal_add, ← Complex.mul_conj, map_neg, map_add, map_sub, map_mul]
  ring

/-- Real form of `QI.four_det_rhoA`. -/
theorem tangleA_eq_fro (ψ : Amp) : tangleA ψ = fro (SAB ψ) + fro (SAC ψ) := by
  have h := congrArg Complex.re (four_det_rhoA ψ)
  simpa [tangleA] using h

/-- The two matrices `S_{AB}` and `S_{AC}` have the same determinant (both equal minus Cayley's
hyperdeterminant); this is a consequence of the Plücker relation. -/
theorem det_SAC_eq_det_SAB (ψ : Amp) : (SAC ψ).det = (SAB ψ).det := by
  simp only [SAB, SAC, Matrix.det_fin_two, Matrix.of_apply]
  ring

/-- For a `2 × 2` complex matrix, `2 |det S| ≤ ‖S‖_F²`. -/
theorem two_norm_det_le_fro (S : Matrix (Fin 2) (Fin 2) ℂ) : 2 * ‖S.det‖ ≤ fro S := by
  have h : ‖S.det‖ ≤ ‖S 0 0‖ * ‖S 1 1‖ + ‖S 0 1‖ * ‖S 1 0‖ := by
    rw [Matrix.det_fin_two]
    calc ‖S 0 0 * S 1 1 - S 0 1 * S 1 0‖ ≤ ‖S 0 0 * S 1 1‖ + ‖S 0 1 * S 1 0‖ :=
          norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have e : fro S = ‖S 0 0‖ ^ 2 + ‖S 0 1‖ ^ 2 + ‖S 1 0‖ ^ 2 + ‖S 1 1‖ ^ 2 := by
    simp [fro, Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
    ring
  nlinarith [sq_nonneg (‖S 0 0‖ - ‖S 1 1‖), sq_nonneg (‖S 0 1‖ - ‖S 1 0‖)]

/-- The two-qubit tangles are nonnegative. -/
theorem tangleAB_nonneg (ψ : Amp) : 0 ≤ tangleAB ψ := by
  have := two_norm_det_le_fro (SAB ψ); simp only [tangleAB]; linarith

theorem tangleAC_nonneg (ψ : Amp) : 0 ≤ tangleAC ψ := by
  have := two_norm_det_le_fro (SAC ψ); simp only [tangleAC]; linarith

/-- The residual tangle is nonnegative. -/
theorem tangle3_nonneg (ψ : Amp) : 0 ≤ tangle3 ψ := by
  simp only [tangle3]; positivity

/-- **The CKW identity.**  For every pure state of three qubits,
`τ_{A(BC)} = τ_{AB} + τ_{AC} + τ_{ABC}`. -/
theorem ckw_identity (ψ : Amp) : tangleA ψ = tangleAB ψ + tangleAC ψ + tangle3 ψ := by
  rw [tangleA_eq_fro, tangleAB, tangleAC, tangle3, det_SAC_eq_det_SAB]
  ring

/-- **Monogamy of entanglement (Coffman–Kundu–Wootters).**  For every pure state of three
qubits, the tangles of the pairs `AB` and `AC` cannot together exceed the tangle of the
bipartition `A|BC`:  `τ_{AB} + τ_{AC} ≤ τ_{A(BC)}`. -/
theorem monogamy_ckw (ψ : Amp) : tangleAB ψ + tangleAC ψ ≤ tangleA ψ := by
  have h := ckw_identity ψ
  have h3 := tangle3_nonneg ψ
  linarith

/-- For a normalized state, `τ_{A(BC)} = 2 (1 - Tr ρ_A²)`, the usual expression of the
tangle in terms of the purity of the reduced state. -/
theorem tangleA_eq_purity (ψ : Amp) (hψ : ∑ i, ∑ j, ∑ k, normSq (ψ i j k) = 1) :
    tangleA ψ = 2 * (1 - ((rhoA ψ * rhoA ψ).trace).re) := by
  have htr : (rhoA ψ) 0 0 + (rhoA ψ) 1 1 = 1 := by
    have : ((∑ i, ∑ j, ∑ k, normSq (ψ i j k) : ℝ) : ℂ) = 1 := by rw [hψ]; norm_num
    simpa [rhoA, Fin.sum_univ_two, ← Complex.mul_conj] using this
  have hc : (4 : ℂ) * (rhoA ψ).det = 2 * (1 - (rhoA ψ * rhoA ψ).trace) := by
    have h1 : (rhoA ψ) 1 1 = 1 - (rhoA ψ) 0 0 := by linear_combination htr
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h1]
    ring
  have := congrArg Complex.re hc
  simpa [tangleA] using this

/-!
### Sanity checks on the standard examples

(Unnormalized) GHZ state `|000⟩ + |111⟩`: all two-qubit tangles vanish and the whole
entanglement sits in the residual three-tangle.  (Unnormalized) W state
`|001⟩ + |010⟩ + |100⟩`: the three-tangle vanishes and the CKW inequality is saturated.
-/

/-- The unnormalized GHZ state `|000⟩ + |111⟩`. -/
def ghz : Amp := fun i j k => if i = j ∧ j = k then 1 else 0

/-- The unnormalized W state `|001⟩ + |010⟩ + |100⟩`. -/
def wState : Amp := fun i j k => if (i : ℕ) + j + k = 1 then 1 else 0

example : tangleA ghz = 4 := by
  simp [tangleA, rhoA, ghz, Fin.sum_univ_two, Matrix.det_fin_two]

example : tangleAB ghz = 0 := by
  simp [tangleAB, fro, SAB, ghz, Matrix.det_fin_two]
  norm_num

example : tangle3 ghz = 4 := by
  simp [tangle3, SAB, ghz, Matrix.det_fin_two]

example : tangleA wState = 8 := by
  simp [tangleA, rhoA, wState, Fin.sum_univ_two, Matrix.det_fin_two]
  norm_num

example : tangleAB wState = 4 := by
  simp [tangleAB, fro, SAB, wState, Matrix.det_fin_two]
  norm_num

example : tangle3 wState = 0 := by
  simp [tangle3, SAB, wState, Matrix.det_fin_two]

end QI

