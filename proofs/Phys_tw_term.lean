import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/
noncomputable def qf (H : α → α → ℂ) (ψ : α → ℂ) : ℝ :=
  (∑ c, ∑ c', (starRingEnd ℂ) (ψ c) * H c c' * ψ c').re

/-- The hermitian inner product `⟪ψ, φ⟫`. -/
noncomputable def ip (ψ φ : α → ℂ) : ℂ := ∑ c, (starRingEnd ℂ) (ψ c) * φ c

/-- The squared norm `‖ψ‖²`. -/
noncomputable def nrm2 (ψ : α → ℂ) : ℝ := ∑ c, ‖ψ c‖ ^ 2

/-- The twisted state `(e^{iθ} ψ)`. -/
noncomputable def tw (θ : α → ℝ) (ψ : α → ℂ) : α → ℂ :=
  fun c => Complex.exp ((θ c : ℂ) * Complex.I) * ψ c

omit [Fintype α] in
@[simp] lemma norm_tw (θ : α → ℝ) (ψ : α → ℂ) (c : α) : ‖tw θ ψ c‖ = ‖ψ c‖ := by
  simp [tw, Complex.norm_exp]

lemma tw_term (a b z : ℂ) (x y : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I) * a) * z *
        (Complex.exp ((y : ℂ) * Complex.I) * b)
      = Complex.exp ((((y - x : ℝ)) : ℂ) * Complex.I) * ((starRingEnd ℂ) a * z * b) := by
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  rw [mul_comm (Complex.exp _) b, ← mul_assoc]
  rw [show ((y : ℂ) - x) * Complex.I = (x : ℂ) * -Complex.I + (y : ℂ) * Complex.I by ring,
    Complex.exp_add]
  ring

lemma two_cos (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (((-x : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.cos x : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- Averaging the twist `θ` with the opposite twist `-θ` kills the term linear in the twist. -/
lemma qf_tw_identity (H : α → α → ℂ) (θ : α → ℝ) (ψ : α → ℂ) :
    qf H (tw θ ψ) + qf H (tw (fun c => -θ c) ψ)
      = 2 * qf H ψ + (∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
          * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')).re := by
  have hsum : (∑ c, ∑ c', (starRingEnd ℂ) (tw θ ψ c) * H c c' * tw θ ψ c')
      + (∑ c, ∑ c', (starRingEnd ℂ) (tw (fun c => -θ c) ψ c) * H c c' * tw (fun c => -θ c) ψ c')
      = 2 * (∑ c, ∑ c', (starRingEnd ℂ) (ψ c) * H c c' * ψ c')
        + ∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c') := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    show (starRingEnd ℂ) (Complex.exp ((θ c : ℂ) * Complex.I) * ψ c) * H c c' *
        (Complex.exp ((θ c' : ℂ) * Complex.I) * ψ c')
      + (starRingEnd ℂ) (Complex.exp (((-θ c : ℝ) : ℂ) * Complex.I) * ψ c) * H c c' *
        (Complex.exp (((-θ c' : ℝ) : ℂ) * Complex.I) * ψ c') = _
    rw [tw_term, tw_term, show ((-θ c' : ℝ) - (-θ c : ℝ)) = -(θ c' - θ c) by ring, ← add_mul,
      two_cos]
    push_cast
    ring
  calc qf H (tw θ ψ) + qf H (tw (fun c => -θ c) ψ) = _ := by
        rw [qf, qf, ← Complex.add_re, hsum]
    _ = _ := by rw [Complex.add_re, Complex.mul_re]; simp [qf]

lemma cos_bound {y δ : ℝ} {k : ℤ} (h : |y - 2 * Real.pi * k| ≤ δ) :
    |2 * Real.cos y - 2| ≤ δ ^ 2 := by
  set x := y - 2 * Real.pi * k with hx
  have hcos : Real.cos y = Real.cos x := by
    rw [hx, show y - 2 * Real.pi * k = y - k * (2 * Real.pi) by ring, Real.cos_sub_int_mul_two_pi]
  rw [hcos]
  have h1 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have h2 : Real.cos x ≤ 1 := Real.cos_le_one x
  have h3 : x ^ 2 ≤ δ ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, h]
  rw [abs_le]
  constructor <;> nlinarith

/-- Off-diagonal matrix elements are controlled by the row sums. -/
lemma sum_norm_A_le (H : α → α → ℂ) (ψ : α → ℂ) (M : ℝ)
    (hH : ∀ c c', H c' c = (starRingEnd ℂ) (H c c'))
    (hM : ∀ c, ∑ c', ‖H c c'‖ ≤ M) :
    ∑ c, ∑ c', ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖ ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by
  have hsymm : ∀ c c' : α, ‖H c c'‖ = ‖H c' c‖ := by
    intro c c'; rw [hH c' c]; simp
  have b1 : ∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c‖ ^ 2 ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hM c) (sq_nonneg _)
  have b2 : ∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c'‖ ^ 2 ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun c' _ => ?_
    have h : ∑ c : α, ‖H c c'‖ * ‖ψ c'‖ ^ 2 = (∑ c : α, ‖H c' c‖) * ‖ψ c'‖ ^ 2 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by rw [hsymm c c']
    rw [h]
    exact mul_le_mul_of_nonneg_right (hM c') (sq_nonneg _)
  have key : ∀ c c' : α, ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖
      ≤ (‖H c c'‖ * ‖ψ c‖ ^ 2) / 2 + (‖H c c'‖ * ‖ψ c'‖ ^ 2) / 2 := by
    intro c c'
    nlinarith [norm_nonneg (H c c'), sq_nonneg (‖ψ c‖ - ‖ψ c'‖)]
  calc ∑ c, ∑ c', ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖
      ≤ ∑ c, ∑ c' : α, ((‖H c c'‖ * ‖ψ c‖ ^ 2) / 2 + (‖H c c'‖ * ‖ψ c'‖ ^ 2) / 2) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => key c c'
    _ = (∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c‖ ^ 2) / 2
          + (∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c'‖ ^ 2) / 2 := by
        simp [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by linarith

/-- **Twist estimate.**  If every nonzero matrix element of `H` connects configurations whose
twist phases differ (modulo `2π`) by at most `δ`, then the average of the energies of the two
twisted states `e^{±iθ}ψ` exceeds the energy of `ψ` by at most `δ² M ‖ψ‖² / 2`, where `M` bounds
the row sums of `H`. -/
lemma qf_tw_add_le (H : α → α → ℂ) (θ : α → ℝ) (ψ : α → ℂ) (δ M : ℝ)
    (hH : ∀ c c', H c' c = (starRingEnd ℂ) (H c c'))
    (hflux : ∀ c c', H c c' ≠ 0 → ∃ k : ℤ, |θ c' - θ c - 2 * Real.pi * k| ≤ δ)
    (hM : ∀ c, ∑ c', ‖H c c'‖ ≤ M) :
    qf H (tw θ ψ) + qf H (tw (fun c => -θ c) ψ)
      ≤ 2 * qf H ψ + δ ^ 2 * (M * ∑ c, ‖ψ c‖ ^ 2) := by
  rw [qf_tw_identity]
  have hre : (∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
      * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')).re
      ≤ δ ^ 2 * (M * ∑ c, ‖ψ c‖ ^ 2) := by
    calc (∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')).re
        ≤ ‖∑ c, ∑ c' : α, ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')‖ := Complex.re_le_norm _
      _ ≤ ∑ c, ∑ c' : α, ‖((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')‖ :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun c _ => norm_sum_le _ _)
      _ ≤ ∑ c, ∑ c' : α, δ ^ 2 * (‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖) := by
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
          by_cases hz : H c c' = 0
          · simp [hz]
          · obtain ⟨k, hk⟩ := hflux c c' hz
            have hb : |2 * Real.cos (θ c' - θ c) - 2| ≤ δ ^ 2 := cos_bound hk
            rw [norm_mul]
            have h1 : ‖(((2 * Real.cos (θ c' - θ c) - 2 : ℝ)) : ℂ)‖ ≤ δ ^ 2 := by
              rw [Complex.norm_real]; exact hb
            have h2 : ‖(starRingEnd ℂ) (ψ c) * H c c' * ψ c'‖ = ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖ := by
              simp
            rw [h2]
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = δ ^ 2 * ∑ c, ∑ c' : α, ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
      _ ≤ δ ^ 2 * (M * ∑ c, ‖ψ c‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_norm_A_le H ψ M hH hM) (sq_nonneg _)
  linarith

lemma nrm2_nonneg (ψ : α → ℂ) : 0 ≤ nrm2 ψ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma qf_of_eigen (H : α → α → ℂ) (ψ : α → ℂ) (E0 : ℝ)
    (heig : ∀ c, ∑ c', H c c' * ψ c' = (E0 : ℂ) * ψ c) :
    qf H ψ = E0 * nrm2 ψ := by
  have h : ∑ c, ∑ c', (starRingEnd ℂ) (ψ c) * H c c' * ψ c'
      = ((E0 : ℂ) * ((nrm2 ψ : ℝ) : ℂ)) := by
    rw [nrm2]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ∑ c', (starRingEnd ℂ) (ψ c) * H c c' * ψ c'
        = (starRingEnd ℂ) (ψ c) * ∑ c', H c c' * ψ c' := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c' _ => by ring
    rw [h1, heig c, show (starRingEnd ℂ) (ψ c) * ((E0 : ℂ) * ψ c)
      = (E0 : ℂ) * ((starRingEnd ℂ) (ψ c) * ψ c) by ring, Complex.conj_mul']
  rw [qf, h]
  simp

lemma nrm2_smul (t : ℝ) (φ : α → ℂ) : nrm2 (fun c => (t : ℂ) * φ c) = t ^ 2 * nrm2 φ := by
  rw [nrm2, nrm2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- From a nonzero eigenvector orthogonal to `ψ` we obtain a *unit* eigenvector orthogonal
to `ψ`, whose energy is the eigenvalue. -/
lemma exists_unit_eigen (H : α → α → ℂ) (ψ φ : α → ℂ) (E0 : ℝ) (hφ : nrm2 φ ≠ 0)
    (heig : ∀ c, ∑ c', H c c' * φ c' = (E0 : ℂ) * φ c) (horth : ip ψ φ = 0) :
    ∃ χ : α → ℂ, nrm2 χ = 1 ∧ ip ψ χ = 0 ∧ qf H χ = E0 := by
  have hpos : 0 < nrm2 φ := lt_of_le_of_ne (nrm2_nonneg φ) (Ne.symm hφ)
  set t : ℝ := (Real.sqrt (nrm2 φ))⁻¹ with ht
  have htsq : t ^ 2 = (nrm2 φ)⁻¹ := by
    rw [ht, inv_pow, Real.sq_sqrt hpos.le]
  have hnrm : nrm2 (fun c => (t : ℂ) * φ c) = 1 := by
    rw [nrm2_smul, htsq, inv_mul_cancel₀ hφ]
  refine ⟨fun c => (t : ℂ) * φ c, hnrm, ?_, ?_⟩
  · rw [ip] at horth ⊢
    have : ∑ c, (starRingEnd ℂ) (ψ c) * ((t : ℂ) * φ c)
        = (t : ℂ) * ∑ c, (starRingEnd ℂ) (ψ c) * φ c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [this, horth, mul_zero]
  · have heig' : ∀ c, ∑ c', H c c' * ((t : ℂ) * φ c') = (E0 : ℂ) * ((t : ℂ) * φ c) := by
      intro c
      have h2 : ∑ c', H c c' * ((t : ℂ) * φ c') = (t : ℂ) * ∑ c', H c c' * φ c' := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c' _ => by ring
      rw [h2, heig c]; ring
    rw [qf_of_eigen H _ E0 heig', hnrm, mul_one]

end Abstract

/-! ## Part II: the half-integer spin chain

Sites are labelled by `ZMod L` (a periodic chain of `L` sites), each site carrying `n = 2S+1`
states.  Half-integral spin `S` means exactly that `n` is even.  Configurations `Conf n L`
form a basis of the Hilbert space, so states are functions `Conf n L → ℂ`.
-/

section Chain

/-- Spin configurations of a periodic chain of `L` sites with `n` states per site. -/
abbrev Conf (n L : ℕ) := ZMod L → Fin n

variable {n L : ℕ} [NeZero L]

/-- Twice the `z`-component of the spin of a site in state `k`, for local dimension `n = 2S+1`;
the spin `S = (n-1)/2` is half-integral exactly when `n` is even. -/
def w (n : ℕ) (k : Fin n) : ℤ := (n : ℤ) - 1 - 2 * (k : ℕ)

/-- Twice the total magnetization of a configuration. -/
def M2 (c : Conf n L) : ℤ := ∑ j : ZMod L, w n (c j)

/-- The Lieb-Schultz-Mattis twist phase: the spin at site `j` is rotated by `2π j / L`. -/
noncomputable def theta (c : Conf n L) : ℝ :=
  (Real.pi / L) * ∑ j : ZMod L, (j.val : ℝ) * (w n (c j) : ℝ)

/-- Lattice translation acting on configurations. -/
def sh (c : Conf n L) : Conf n L := fun j => c (j + 1)

/-- The Hamiltonian of a translation invariant nearest neighbour chain with bond matrix `b`:
the matrix element between two configurations is the sum over bonds `(j, j+1)` of the bond
matrix element, provided the two configurations agree away from the bond. -/
noncomputable def Hchain (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (c c' : Conf n L) : ℂ :=
  ∑ j : ZMod L, if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
    then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0

omit [NeZero L] in
lemma sh_bijective : Function.Bijective (sh : Conf n L → Conf n L) := by
  refine ⟨fun c c' h => ?_, fun c => ⟨fun j => c (j - 1), ?_⟩⟩
  · funext j
    have := congrFun h (j - 1)
    simpa [sh] using this
  · funext j; simp [sh]

/-- Arithmetic of `ZMod L`: the representative of `k - 1`. -/
lemma zmod_val_sub_one (k : ZMod L) :
    ((k - 1).val : ℤ) = (k.val : ℤ) - 1 + (if k = 0 then (L : ℤ) else 0) := by
  by_cases h : k = 0
  · subst h
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have he : (0 - 1 : ZMod L) = ((L - 1 : ℕ) : ZMod L) := by
      push_cast [Nat.cast_sub hL]; simp
    rw [he, ZMod.val_natCast_of_lt (by omega)]
    simp
    omega
  · have hk : k.val ≠ 0 := (ZMod.val_ne_zero k).mpr h
    have h1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.2 hk
    have hlt : k.val < L := ZMod.val_lt k
    have he : k - 1 = ((k.val - 1 : ℕ) : ZMod L) := by
      rw [Nat.cast_sub h1]; simp [ZMod.natCast_val, ZMod.cast_id]
    rw [he, ZMod.val_natCast_of_lt (by omega)]
    simp [h]

lemma Hchain_herm (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ)
    (hb : ∀ p q, b q p = (starRingEnd ℂ) (b p q)) (c c' : Conf n L) :
    Hchain b c' c = (starRingEnd ℂ) (Hchain b c c') := by
  rw [Hchain, Hchain, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i
  · rw [if_pos (fun i hi hi' => (h i hi hi').symm), if_pos h, hb]
  · have h' : ¬ ∀ i, i ≠ j → i ≠ j + 1 → c' i = c i :=
      fun hc => h (fun i hi hi' => (hc i hi hi').symm)
    rw [if_neg h', if_neg h, map_zero]

lemma Hchain_transl (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (c c' : Conf n L) :
    Hchain b (sh c) (sh c') = Hchain b c c' := by
  have hstep : ∀ j : ZMod L,
      (if (∀ i, i ≠ j → i ≠ j + 1 → (sh c) i = (sh c') i)
        then b ((sh c) j, (sh c) (j + 1)) ((sh c') j, (sh c') (j + 1)) else 0)
      = (if (∀ i, i ≠ j + 1 → i ≠ j + 1 + 1 → c i = c' i)
        then b (c (j + 1), c (j + 1 + 1)) (c' (j + 1), c' (j + 1 + 1)) else 0) := by
    intro j
    by_cases hcond : ∀ i, i ≠ j + 1 → i ≠ j + 1 + 1 → c i = c' i
    · have hpos : ∀ i, i ≠ j → i ≠ j + 1 → (sh c) i = (sh c') i := by
        intro i hi hi'
        exact hcond (i + 1) (fun hx => hi (add_right_cancel hx))
          (fun hx => hi' (add_right_cancel hx))
      rw [if_pos hpos, if_pos hcond]
      rfl
    · have hneg : ¬ ∀ i, i ≠ j → i ≠ j + 1 → (sh c) i = (sh c') i := by
        intro hc2
        refine hcond fun i hi hi' => ?_
        have h1 : i - 1 ≠ j := fun hx => hi (by rw [← hx]; ring)
        have h2 : i - 1 ≠ j + 1 := fun hx => hi' (by rw [← hx]; ring)
        have := hc2 (i - 1) h1 h2
        simpa [sh, sub_add_cancel] using this
      rw [if_neg hneg, if_neg hcond]
  calc Hchain b (sh c) (sh c') = ∑ j : ZMod L,
      (if (∀ i, i ≠ j + 1 → i ≠ j + 1 + 1 → c i = c' i)
        then b (c (j + 1), c (j + 1 + 1)) (c' (j + 1), c' (j + 1 + 1)) else 0) :=
        Finset.sum_congr rfl fun j _ => hstep j
    _ = Hchain b c c' :=
        Fintype.sum_bijective (fun j : ZMod L => j + 1) (Equiv.addRight (1 : ZMod L)).bijective
          _ _ (fun j => rfl)

lemma Hchain_rowsum (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (B : ℝ)
    (hB : ∀ p, ∑ q, ‖b p q‖ ≤ B) (c : Conf n L) :
    ∑ c', ‖Hchain b c c'‖ ≤ L * B := by
  have key : ∀ j : ZMod L, ∑ c' : Conf n L,
      ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
        then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖ ≤ B := by
    intro j
    have e1 : ∀ c' : Conf n L,
        ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖
        = if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then ‖b (c j, c (j + 1)) (c' j, c' (j + 1))‖ else 0 := by
      intro c'; split <;> simp
    rw [Finset.sum_congr rfl (fun c' _ => e1 c'), ← Finset.sum_filter]
    have hinj : ∀ x ∈ Finset.univ.filter (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i),
        ∀ y ∈ Finset.univ.filter (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i),
        (fun c' : Conf n L => (c' j, c' (j + 1))) x = (fun c' : Conf n L => (c' j, c' (j + 1))) y →
        x = y := by
      intro x hx y hy hxy
      simp only [Finset.mem_filter] at hx hy
      funext i
      by_cases h1 : i = j
      · subst h1; exact congrArg Prod.fst hxy
      · by_cases h2 : i = j + 1
        · subst h2; exact congrArg Prod.snd hxy
        · rw [← hx.2 i h1 h2, ← hy.2 i h1 h2]
    calc ∑ c' ∈ Finset.univ.filter (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i),
          ‖b (c j, c (j + 1)) (c' j, c' (j + 1))‖
        = ∑ q ∈ (Finset.univ.filter
            (fun c' : Conf n L => ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)).image
            (fun c' : Conf n L => (c' j, c' (j + 1))), ‖b (c j, c (j + 1)) q‖ :=
          (Finset.sum_image (f := fun q => ‖b (c j, c (j + 1)) q‖) hinj).symm
      _ ≤ ∑ q : Fin n × Fin n, ‖b (c j, c (j + 1)) q‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)
      _ ≤ B := hB _
  calc ∑ c' : Conf n L, ‖Hchain b c c'‖
      ≤ ∑ c' : Conf n L, ∑ j : ZMod L,
        ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖ :=
        Finset.sum_le_sum fun c' _ => norm_sum_le _ _
    _ = ∑ j : ZMod L, ∑ c' : Conf n L,
        ‖(if (∀ i, i ≠ j → i ≠ j + 1 → c i = c' i)
          then b (c j, c (j + 1)) (c' j, c' (j + 1)) else 0)‖ := Finset.sum_comm
    _ ≤ ∑ _j : ZMod L, B := Finset.sum_le_sum fun j _ => key j
    _ = L * B := by simp [ZMod.card, nsmul_eq_mul]

/-- **Flux estimate.**  If the bond matrix conserves the total magnetization, then any two
configurations connected by the Hamiltonian have twist phases differing, modulo `2π`, by at
most `2π(n-1)/L`. -/
lemma theta_flux (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ)
    (hcons : ∀ p q, b p q ≠ 0 → w n p.1 + w n p.2 = w n q.1 + w n q.2)
    (c c' : Conf n L) (h : Hchain b c c' ≠ 0) :
    ∃ k : ℤ, |theta c' - theta c - 2 * Real.pi * k| ≤ 2 * Real.pi * ((n : ℝ) - 1) / L := by
  have hLpos : (0 : ℝ) < L := by
    have := Nat.pos_of_ne_zero (NeZero.ne L); exact_mod_cast this
  rw [Hchain] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hcond : ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i := by
    by_contra hx; rw [if_neg hx] at hj; exact hj rfl
  rw [if_pos hcond] at hj
  have hw : w n (c j) + w n (c (j + 1)) = w n (c' j) + w n (c' (j + 1)) := hcons _ _ hj
  set d : ℤ := (c j).val - (c' j).val with hd
  have hd1 : w n (c' j) - w n (c j) = 2 * d := by simp [w, hd]; ring
  have hd2 : w n (c' (j + 1)) - w n (c (j + 1)) = -(2 * d) := by omega
  have e1 : (w n (c' j) : ℝ) - (w n (c j) : ℝ) = 2 * (d : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hd1
  have e2 : (w n (c' (j + 1)) : ℝ) - (w n (c (j + 1)) : ℝ) = -(2 * (d : ℝ)) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hd2
  have hsum : ∑ i ∈ ({j, j + 1} : Finset (ZMod L)),
        (i.val : ℝ) * ((w n (c' i) : ℝ) - (w n (c i) : ℝ))
      = ∑ i : ZMod L, (i.val : ℝ) * ((w n (c' i) : ℝ) - (w n (c i) : ℝ)) := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [hcond i hi.1 hi.2]
    ring
  have hpair : ∑ i ∈ ({j, j + 1} : Finset (ZMod L)),
        (i.val : ℝ) * ((w n (c' i) : ℝ) - (w n (c i) : ℝ))
      = ((j.val : ℝ) - ((j + 1).val : ℝ)) * (2 * (d : ℝ)) := by
    by_cases hjj : j = j + 1
    · have hd0 : d = 0 := by rw [← hjj] at hw; omega
      rw [← hjj]
      simp [e1, hd0]
    · rw [Finset.sum_pair hjj, e1, e2]
      ring
  have hdiff : theta c' - theta c
      = (Real.pi / L) * (((j.val : ℝ) - ((j + 1).val : ℝ)) * (2 * (d : ℝ))) := by
    rw [theta, theta, ← mul_sub, ← Finset.sum_sub_distrib, ← hpair, hsum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
  have hvalj : ((j + 1).val : ℝ) = (j.val : ℝ) + 1 - (if j + 1 = 0 then (L : ℝ) else 0) := by
    have hz := zmod_val_sub_one (L := L) (j + 1)
    rw [add_sub_cancel_right] at hz
    have hz2 := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at hz2
    split_ifs at hz2 ⊢ with hcase
    · linarith
    · linarith
  have hdn : |(d : ℝ)| ≤ (n : ℝ) - 1 := by
    have h1 : ((c j).val : ℤ) < n := by exact_mod_cast (c j).isLt
    have h2 : ((c' j).val : ℤ) < n := by exact_mod_cast (c' j).isLt
    have h3 : -((n : ℤ) - 1) ≤ d := by omega
    have h4 : d ≤ (n : ℤ) - 1 := by omega
    rw [abs_le]
    constructor
    · have : ((-((n : ℤ) - 1) : ℤ) : ℝ) ≤ ((d : ℤ) : ℝ) := by exact_mod_cast h3
      push_cast at this; linarith
    · have : ((d : ℤ) : ℝ) ≤ (((n : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h4
      push_cast at this; linarith
  have hfin : |(-(2 * Real.pi * (d : ℝ) / L))| ≤ 2 * Real.pi * ((n : ℝ) - 1) / L := by
    rw [abs_neg, abs_div, abs_of_pos hLpos, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    gcongr
  by_cases hj0 : j + 1 = 0
  · refine ⟨d, ?_⟩
    rw [hdiff, hvalj, if_pos hj0]
    have heq : (Real.pi / L) * (((j.val : ℝ) - ((j.val : ℝ) + 1 - L)) * (2 * (d : ℝ)))
        - 2 * Real.pi * (d : ℝ) = -(2 * Real.pi * (d : ℝ) / L) := by field_simp; ring
    rw [heq]
    exact hfin
  · refine ⟨0, ?_⟩
    rw [hdiff, hvalj, if_neg hj0]
    have heq : (Real.pi / L) * (((j.val : ℝ) - ((j.val : ℝ) + 1 - 0)) * (2 * (d : ℝ)))
        - 2 * Real.pi * ((0 : ℤ) : ℝ) = -(2 * Real.pi * (d : ℝ) / L) := by
      push_cast; field_simp; ring
    rw [heq]
    exact hfin

/-- **The momentum shift.**  On the zero magnetization sector, translating a configuration
shifts the twist phase by `π` times twice the spin at the origin. -/
lemma theta_sh_sub (c : Conf n L) (hc : M2 c = 0) :
    theta (sh c) - theta c = Real.pi * (w n (c 0) : ℝ) := by
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have h1 : ∑ j : ZMod L, (j.val : ℝ) * (w n ((sh c) j) : ℝ)
      = ∑ k : ZMod L, (((k - 1).val : ℕ) : ℝ) * (w n (c k) : ℝ) :=
    Fintype.sum_bijective (fun j : ZMod L => j + 1) (Equiv.addRight (1 : ZMod L)).bijective _ _
      (fun j => by simp [sh])
  have h2 : ∀ k : ZMod L,
      (((k - 1).val : ℕ) : ℝ) = (k.val : ℝ) - 1 + (if k = 0 then (L : ℝ) else 0) := by
    intro k
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) (zmod_val_sub_one (L := L) k)
    push_cast at h3
    simpa using h3
  have hsum : ∑ k : ZMod L, (w n (c k) : ℝ) = 0 := by
    have h4 : ((M2 c : ℤ) : ℝ) = ∑ k : ZMod L, (w n (c k) : ℝ) := by
      rw [M2]; push_cast; ring
    rw [← h4, hc]; simp
  have hzero : ∑ k : ZMod L, (if k = 0 then (L : ℝ) else 0) * (w n (c k) : ℝ)
      = (L : ℝ) * (w n (c 0) : ℝ) := by
    rw [Finset.sum_congr rfl (fun k _ => by
      by_cases hk : k = 0 <;> simp [hk] :
      ∀ k ∈ Finset.univ, (if k = 0 then (L : ℝ) else 0) * (w n (c k) : ℝ)
        = if k = 0 then (L : ℝ) * (w n (c k) : ℝ) else 0)]
    simp
  calc theta (sh c) - theta c
      = (Real.pi / L) * ∑ k : ZMod L,
          ((((k - 1).val : ℕ) : ℝ) - (k.val : ℝ)) * (w n (c k) : ℝ) := by
        rw [theta, theta, h1, ← mul_sub, ← Finset.sum_sub_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    _ = (Real.pi / L) * (-(∑ k : ZMod L, (w n (c k) : ℝ))
          + ∑ k : ZMod L, (if k = 0 then (L : ℝ) else 0) * (w n (c k) : ℝ)) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [h2 k]; ring)
    _ = Real.pi * (w n (c 0) : ℝ) := by
        rw [hsum, hzero, neg_zero, zero_add]
        field_simp

/-! ## Part III: the Lieb-Schultz-Mattis theorem -/

lemma ip_self (ψ : Conf n L → ℂ) : ip ψ ψ = (nrm2 ψ : ℂ) := by
  rw [ip, nrm2]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by rw [Complex.conj_mul']

lemma nrm2_sh (ψ : Conf n L → ℂ) : nrm2 (fun c => ψ (sh c)) = nrm2 ψ :=
  Fintype.sum_bijective sh sh_bijective _ _ (fun _ => rfl)

/-- The translated ground state is again a ground state. -/
lemma eig_sh (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (ψ : Conf n L → ℂ) (E0 : ℝ)
    (heig : ∀ c, ∑ c', Hchain b c c' * ψ c' = (E0 : ℂ) * ψ c) (c : Conf n L) :
    ∑ c', Hchain b c c' * ψ (sh c') = (E0 : ℂ) * ψ (sh c) := by
  have h : ∑ d, Hchain b (sh c) (sh d) * ψ (sh d) = ∑ c', Hchain b (sh c) c' * ψ c' :=
    Fintype.sum_bijective sh sh_bijective _ _ (fun d => rfl)
  have h2 : ∑ d, Hchain b c d * ψ (sh d) = ∑ d, Hchain b (sh c) (sh d) * ψ (sh d) :=
    Finset.sum_congr rfl fun d _ => by rw [Hchain_transl]
  rw [h2, h, heig (sh c)]

lemma exp_pi_odd (m : ℤ) :
    Complex.exp (((Real.pi * (2 * m + 1) : ℝ) : ℂ) * Complex.I) = -1 := by
  have : ((Real.pi * (2 * m + 1) : ℝ) : ℂ) * Complex.I
      = (m : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

omit [NeZero L] in
/-- A twist whose phase jumps by an odd multiple of `π` under translation turns a translation
eigenstate into a translation eigenstate with the opposite eigenvalue. -/
lemma tw_sh_of_odd (ψ : Conf n L → ℂ) (θ' : Conf n L → ℝ)
    (hodd : ∀ c, ψ c ≠ 0 → ∃ m : ℤ, θ' (sh c) - θ' c = Real.pi * (2 * m + 1))
    (lam : ℂ) (hψ : ∀ c, ψ (sh c) = lam * ψ c) (c : Conf n L) :
    tw θ' ψ (sh c) = -(lam * tw θ' ψ c) := by
  by_cases hc : ψ c = 0
  · simp [tw, hψ c, hc]
  · obtain ⟨m, hm⟩ := hodd c hc
    have hsplit : ((θ' (sh c) : ℝ) : ℂ) * Complex.I
        = ((Real.pi * (2 * m + 1) : ℝ) : ℂ) * Complex.I + ((θ' c : ℝ) : ℂ) * Complex.I := by
      have : (θ' (sh c) : ℝ) = Real.pi * (2 * m + 1) + θ' c := by linarith [hm]
      rw [this]; push_cast; ring
    simp only [tw, hψ c, hsplit, Complex.exp_add, exp_pi_odd]
    ring

/-- Two translation eigenstates with opposite translation eigenvalues are orthogonal. -/
lemma ip_eq_zero_of_shift (ψ χ : Conf n L → ℂ) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hψ : ∀ c, ψ (sh c) = lam * ψ c) (hχ : ∀ c, χ (sh c) = -(lam * χ c)) :
    ip ψ χ = 0 := by
  have hre : ∑ c, (starRingEnd ℂ) (ψ (sh c)) * χ (sh c) = ip ψ χ :=
    Fintype.sum_bijective sh sh_bijective _ _ (fun c => rfl)
  have hlam2 : (starRingEnd ℂ) lam * lam = 1 := by
    rw [Complex.conj_mul']
    norm_cast
    rw [hlam]; norm_num
  have : ∑ c, (starRingEnd ℂ) (ψ (sh c)) * χ (sh c) = -ip ψ χ := by
    rw [ip, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hψ c, hχ c, map_mul]
    calc (starRingEnd ℂ) lam * (starRingEnd ℂ) (ψ c) * -(lam * χ c)
        = -((starRingEnd ℂ) lam * lam) * ((starRingEnd ℂ) (ψ c) * χ c) := by ring
      _ = -((starRingEnd ℂ) (ψ c) * χ c) := by rw [hlam2]; ring
  rw [hre] at this
  linear_combination this / 2

lemma w_odd (hn : Even n) (k : Fin n) : ∃ m : ℤ, w n k = 2 * m + 1 := by
  obtain ⟨t, ht⟩ := hn
  refine ⟨(t : ℤ) - 1 - (k : ℕ), ?_⟩
  have hnz : (n : ℤ) = 2 * t := by rw [ht]; push_cast; ring
  rw [w, hnz]
  ring

/-- The twist phase jumps by an odd multiple of `π` under translation, on the zero
magnetization sector.  This is where half-integrality of the spin enters. -/
lemma theta_odd_jump (hn : Even n) (ψ : Conf n L → ℂ) (hsector : ∀ c, ψ c ≠ 0 → M2 c = 0)
    (c : Conf n L) (hc : ψ c ≠ 0) :
    ∃ m : ℤ, theta (sh c) - theta c = Real.pi * (2 * m + 1) := by
  obtain ⟨m, hm⟩ := w_odd hn (c 0)
  refine ⟨m, ?_⟩
  rw [theta_sh_sub c (hsector c hc), hm]
  push_cast
  ring

/-- **Lieb-Schultz-Mattis.**  Consider a periodic chain of `L` sites, each carrying `n = 2S+1`
states, with half-integral spin (`n` even), and a translation invariant nearest-neighbour
Hamiltonian `Hchain b` whose bond matrix `b` is hermitian and conserves the total magnetization.
Let `ψ` be a ground state of energy `E0` lying in the zero magnetization sector.  Then either
the ground state energy is degenerate (there is a second, orthogonal, ground state), or there is
an excited state orthogonal to `ψ` whose energy exceeds `E0` by at most `2π²(n-1)²B/L`, where
`B` bounds the row sums of the bond matrix.  In particular the gap above the ground state closes
at least as fast as `O(1/L)` as the chain length `L` grows. -/
theorem lieb_schultz_mattis (hn : Even n)
    (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ)
    (hherm : ∀ p q, b q p = (starRingEnd ℂ) (b p q))
    (hcons : ∀ p q, b p q ≠ 0 → w n p.1 + w n p.2 = w n q.1 + w n q.2)
    (B : ℝ) (hB : ∀ p, ∑ q, ‖b p q‖ ≤ B)
    (ψ : Conf n L → ℂ) (E0 : ℝ)
    (hunit : nrm2 ψ = 1)
    (hsector : ∀ c, ψ c ≠ 0 → M2 c = 0)
    (heig : ∀ c, ∑ c', Hchain b c c' * ψ c' = (E0 : ℂ) * ψ c)
    (hmin : ∀ φ : Conf n L → ℂ, nrm2 φ = 1 → E0 ≤ qf (Hchain b) φ) :
    (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ qf (Hchain b) φ = E0) ∨
    (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ E0 < qf (Hchain b) φ ∧
      qf (Hchain b) φ ≤ E0 + 2 * Real.pi ^ 2 * ((n : ℝ) - 1) ^ 2 * B / L) := by
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := lt_of_le_of_ne (Nat.cast_nonneg L) (Ne.symm hLne)
  set H := Hchain (L := L) b with hH
  set C : ℝ := 2 * Real.pi ^ 2 * ((n : ℝ) - 1) ^ 2 * B / L with hC
  -- the dichotomy, given a unit vector orthogonal to `ψ` with energy at most `E0 + C`
  have main : ∀ φ : Conf n L → ℂ, nrm2 φ = 1 → ip ψ φ = 0 → qf H φ ≤ E0 + C →
      (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ qf H φ = E0) ∨
      (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ E0 < qf H φ ∧ qf H φ ≤ E0 + C) := by
    intro φ h1 h2 h3
    rcases (hmin φ h1).eq_or_lt with h | h
    · exact Or.inl ⟨φ, h1, h2, h.symm⟩
    · exact Or.inr ⟨φ, h1, h2, h, h3⟩
  by_cases hprop : ∃ lam : ℂ, ∀ c, ψ (sh c) = lam * ψ c
  · -- the ground state is a translation eigenstate: insert a flux
    obtain ⟨lam, hlam⟩ := hprop
    have hlam1 : ‖lam‖ = 1 := by
      have h1 : nrm2 (fun c => ψ (sh c)) = ‖lam‖ ^ 2 * nrm2 ψ := by
        rw [nrm2, nrm2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by rw [hlam c, norm_mul, mul_pow]
      rw [nrm2_sh, hunit, mul_one] at h1
      nlinarith [norm_nonneg lam]
    have hunit' : ∑ c, ‖ψ c‖ ^ 2 = 1 := hunit
    have hE : qf H ψ = E0 := by rw [qf_of_eigen H ψ E0 heig, hunit, mul_one]
    -- the two twisted states
    have hodd : ∀ c, ψ c ≠ 0 → ∃ m : ℤ, theta (sh c) - theta c = Real.pi * (2 * m + 1) :=
      theta_odd_jump hn ψ hsector
    have hodd' : ∀ c, ψ c ≠ 0 → ∃ m : ℤ,
        (fun d => -theta d) (sh c) - (fun d => -theta d) c = Real.pi * (2 * m + 1) := by
      intro c hc
      obtain ⟨m, hm⟩ := hodd c hc
      exact ⟨-m - 1, by simp only []; push_cast; linarith [hm]⟩
    have horth : ip ψ (tw theta ψ) = 0 :=
      ip_eq_zero_of_shift ψ _ lam hlam1 hlam (tw_sh_of_odd ψ theta hodd lam hlam)
    have horth' : ip ψ (tw (fun d => -theta d) ψ) = 0 :=
      ip_eq_zero_of_shift ψ _ lam hlam1 hlam (tw_sh_of_odd ψ _ hodd' lam hlam)
    have hn1 : nrm2 (tw (theta (n := n) (L := L)) ψ) = 1 := by
      rw [nrm2]; simpa [norm_tw] using hunit'
    have hn1' : nrm2 (tw (fun d => -theta d) ψ) = 1 := by
      rw [nrm2]; simpa [norm_tw] using hunit'
    -- the twist estimate
    have hbd := qf_tw_add_le H theta ψ (2 * Real.pi * ((n : ℝ) - 1) / L) ((L : ℝ) * B)
      (Hchain_herm b hherm) (fun c c' h => theta_flux b hcons c c' h)
      (Hchain_rowsum b B hB)
    rw [hunit', hE, mul_one] at hbd
    have hCeq : (2 * Real.pi * ((n : ℝ) - 1) / L) ^ 2 * ((L : ℝ) * B) = 2 * C := by
      rw [hC]
      field_simp
    rw [hCeq] at hbd
    rcases le_or_gt (qf H (tw theta ψ)) (E0 + C) with h | h
    · exact main _ hn1 horth h
    · exact main _ hn1' horth' (by linarith)
  · -- the ground state is not a translation eigenstate: the ground level is degenerate
    push_neg at hprop
    set k : ℂ := ip ψ (fun d => ψ (sh d)) with hk
    set χ : Conf n L → ℂ := fun c => ψ (sh c) - k * ψ c with hχ
    have heigχ : ∀ c, ∑ c', H c c' * χ c' = (E0 : ℂ) * χ c := by
      intro c
      have hsplit : ∑ c', H c c' * χ c'
          = (∑ c', H c c' * ψ (sh c')) - k * ∑ c', H c c' * ψ c' := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c' _ => by rw [hχ]; ring
      rw [hsplit, eig_sh b ψ E0 heig c, heig c, hχ]
      ring
    have horthχ : ip ψ χ = 0 := by
      have : ip ψ χ = ip ψ (fun d => ψ (sh d)) - k * ip ψ ψ := by
        rw [ip, ip, ip, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by rw [hχ]; ring
      rw [this, ip_self, hunit, ← hk]
      push_cast
      ring
    have hne : nrm2 χ ≠ 0 := by
      intro h0
      obtain ⟨c0, hc0⟩ := hprop k
      have hz : ‖χ c0‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg ‖χ c‖)).1 h0 c0
          (Finset.mem_univ c0)
      have hzz : χ c0 = 0 := by simpa using hz
      simp only [hχ, sub_eq_zero] at hzz
      exact hc0 hzz
    exact Or.inl (exists_unit_eigen H ψ χ E0 hne heigχ horthχ)

/-! ## Part IV: the hypotheses are not vacuous -/

/-- The spin-1/2 Heisenberg bond matrix, in the basis `0 = up`, `1 = down`:
`S·S = S^z⊗S^z + (S^+⊗S^- + S^-⊗S^+)/2`. -/
noncomputable def heisBond : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ := fun p q =>
  if p = q then (if p.1 = p.2 then (1 : ℂ) / 4 else -(1 / 4))
  else if p.1 ≠ p.2 ∧ q = (p.2, p.1) then (1 : ℂ) / 2 else 0

/-- The spin-1/2 Heisenberg bond is hermitian. -/
lemma heisBond_herm : ∀ p q, heisBond q p = (starRingEnd ℂ) (heisBond p q) := by
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    norm_num [heisBond, Prod.ext_iff, Complex.ext_iff]

/-- The spin-1/2 Heisenberg bond conserves the total magnetization. -/
lemma heisBond_cons : ∀ p q, heisBond p q ≠ 0 → w 2 p.1 + w 2 p.2 = w 2 q.1 + w 2 q.2 := by
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp_all [heisBond, Prod.ext_iff, w]

/-- The row sums of the spin-1/2 Heisenberg bond are bounded by `1`. -/
lemma heisBond_rowsum : ∀ p, ∑ q, ‖heisBond p q‖ ≤ 1 := by
  rintro ⟨p1, p2⟩
  fin_cases p1 <;> fin_cases p2 <;>
    norm_num [heisBond, Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff]

/-- The hypotheses of `lieb_schultz_mattis` are consistent: they are all satisfied (for the
trivial Hamiltonian) as soon as the zero magnetization sector is nonempty. -/
lemma lsm_hypotheses_satisfiable (c0 : Conf n L) (hc0 : M2 c0 = 0) :
    ∃ (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (B : ℝ) (ψ : Conf n L → ℂ) (E0 : ℝ),
      (∀ p q, b q p = (starRingEnd ℂ) (b p q)) ∧
      (∀ p q, b p q ≠ 0 → w n p.1 + w n p.2 = w n q.1 + w n q.2) ∧
      (∀ p, ∑ q, ‖b p q‖ ≤ B) ∧ nrm2 ψ = 1 ∧ (∀ c, ψ c ≠ 0 → M2 c = 0) ∧
      (∀ c, ∑ c', Hchain b c c' * ψ c' = (E0 : ℂ) * ψ c) ∧
      (∀ φ : Conf n L → ℂ, nrm2 φ = 1 → E0 ≤ qf (Hchain b) φ) := by
  have hH : ∀ c c' : Conf n L, Hchain (fun _ _ => (0 : ℂ)) c c' = 0 := by
    intro c c'; simp [Hchain]
  refine ⟨fun _ _ => 0, 0, fun c => if c = c0 then 1 else 0, 0, by simp, by simp, by simp, ?_, ?_,
    by simp [hH], ?_⟩
  · simp [nrm2, apply_ite norm, Finset.sum_ite_eq']
  · intro c hc
    by_cases h : c = c0
    · rw [h]; exact hc0
    · simp [h] at hc
  · intro φ _
    simp [qf, hH]

/-- The zero magnetization sector of the spin-1/2 chain with two sites is nonempty. -/
example : M2 (L := 2) (fun j => if j = 0 then (0 : Fin 2) else 1) = 0 := by decide

end Chain

end Phys

