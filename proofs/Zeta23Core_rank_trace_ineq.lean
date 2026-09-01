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

/- (Header as requested, written as a plain block comment because Lean 4.28 does not
   allow a module docstring to precede the import line.)
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Matrix
open scoped ComplexOrder BigOperators

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/
noncomputable def frobSq (M : Matrix n n 𝕜) : ℝ := RCLike.re (Matrix.trace (Mᴴ * M))

/-- The positive index of a Hermitian matrix: the number of its positive eigenvalues. -/
noncomputable def posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hQ.eigenvalues i).card

/-! ### Basic facts about the squared Frobenius norm -/

omit [DecidableEq n] in
theorem frobSq_eq_sum (M : Matrix n n 𝕜) : frobSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, conjTranspose_apply,
    map_sum, RCLike.star_def, RCLike.conj_mul]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq n] in
theorem sum_diag_sq_le_frobSq (M : Matrix n n 𝕜) : ∑ i, ‖M i i‖ ^ 2 ≤ frobSq M := by
  rw [frobSq_eq_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => ‖M i j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

omit [DecidableEq n] in
theorem frobSq_add (X Y : Matrix n n 𝕜) :
    frobSq (X + Y) = frobSq X + 2 * RCLike.re (Matrix.trace (Xᴴ * Y)) + frobSq Y := by
  have h : Matrix.trace (Yᴴ * X) = starRingEnd 𝕜 (Matrix.trace (Xᴴ * Y)) := by
    rw [show (starRingEnd 𝕜) (Matrix.trace (Xᴴ * Y)) = star (Matrix.trace (Xᴴ * Y)) from rfl,
      ← Matrix.trace_conjTranspose]
    congr 1
    simp [Matrix.conjTranspose_mul]
  simp only [frobSq, conjTranspose_add, add_mul, mul_add, Matrix.trace_add, map_add, h,
    RCLike.conj_re]
  ring

theorem trace_conj_unitary (u : Matrix.unitaryGroup n 𝕜) (M : Matrix n n 𝕜) :
    Matrix.trace ((star u : Matrix n n 𝕜) * M * (u : Matrix n n 𝕜)) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle]
  simp [Unitary.mul_star_self_of_mem u.2]

theorem trace_conj_unitary' (u : Matrix.unitaryGroup n 𝕜) (M : Matrix n n 𝕜) :
    Matrix.trace ((u : Matrix n n 𝕜) * M * (star u : Matrix n n 𝕜)) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle]
  simp [Unitary.star_mul_self_of_mem u.2]

theorem frobSq_conj_unitary (u : Matrix.unitaryGroup n 𝕜) (M : Matrix n n 𝕜) :
    frobSq ((star u : Matrix n n 𝕜) * M * (u : Matrix n n 𝕜)) = frobSq M := by
  have h2 : (u : Matrix n n 𝕜) * star (u : Matrix n n 𝕜) = 1 := Unitary.mul_star_self_of_mem u.2
  simp only [frobSq, ← star_eq_conjTranspose]
  have key : star ((star (u : Matrix n n 𝕜)) * M * u) * ((star (u : Matrix n n 𝕜)) * M * u)
      = (star (u : Matrix n n 𝕜)) * (star M * M) * u := by
    simp only [Matrix.star_mul, star_star, mul_assoc]
    rw [← mul_assoc (u : Matrix n n 𝕜) (star (u : Matrix n n 𝕜)), h2, one_mul]
  rw [key, trace_conj_unitary]

theorem frobSq_conj_unitary' (u : Matrix.unitaryGroup n 𝕜) (M : Matrix n n 𝕜) :
    frobSq ((u : Matrix n n 𝕜) * M * (star u : Matrix n n 𝕜)) = frobSq M := by
  have hs : (star (u : Matrix n n 𝕜)) * (u : Matrix n n 𝕜) = 1 := Unitary.star_mul_self_of_mem u.2
  simp only [frobSq, ← star_eq_conjTranspose]
  have key : star ((u : Matrix n n 𝕜) * M * star (u : Matrix n n 𝕜))
        * ((u : Matrix n n 𝕜) * M * star (u : Matrix n n 𝕜))
      = (u : Matrix n n 𝕜) * (star M * M) * star (u : Matrix n n 𝕜) := by
    simp only [Matrix.star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star (u : Matrix n n 𝕜)) (u : Matrix n n 𝕜), hs, one_mul]
  rw [key, trace_conj_unitary']

/-! ### Diagonal conjugates -/

/-- `diagConj u d` is the Hermitian matrix `u * diag d * uᴴ`. -/
noncomputable def diagConj (u : Matrix.unitaryGroup n 𝕜) (d : n → ℝ) : Matrix n n 𝕜 :=
  (u : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ d) * (star u : Matrix n n 𝕜)

theorem diagConj_posSemidef (u : Matrix.unitaryGroup n 𝕜) {d : n → ℝ} (hd : ∀ i, 0 ≤ d i) :
    (diagConj u d).PosSemidef := by
  have h : (diagonal (RCLike.ofReal ∘ d : n → 𝕜)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact RCLike.ofReal_nonneg (K := 𝕜) |>.mpr (hd i)
  simpa [diagConj, star_eq_conjTranspose] using
    h.mul_mul_conjTranspose_same (B := (u : Matrix n n 𝕜))

theorem diagConj_sub (u : Matrix.unitaryGroup n 𝕜) (d e : n → ℝ) :
    diagConj u (fun i => d i - e i) = diagConj u d - diagConj u e := by
  have hd : (diagonal (RCLike.ofReal ∘ fun i => d i - e i) : Matrix n n 𝕜)
      = diagonal (RCLike.ofReal ∘ d) - diagonal (RCLike.ofReal ∘ e) := by
    rw [Matrix.diagonal_sub]; congr 1; funext i; simp
  simp only [diagConj, hd, Matrix.mul_sub, Matrix.sub_mul]

theorem trace_diagConj (u : Matrix.unitaryGroup n 𝕜) (d : n → ℝ) :
    RCLike.re (Matrix.trace (diagConj u d : Matrix n n 𝕜)) = ∑ i, d i := by
  rw [diagConj, trace_conj_unitary', Matrix.trace_diagonal]
  simp

theorem frobSq_diagConj (u : Matrix.unitaryGroup n 𝕜) (d : n → ℝ) :
    frobSq (diagConj u d : Matrix n n 𝕜) = ∑ i, (d i) ^ 2 := by
  rw [diagConj, frobSq_conj_unitary', frobSq, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [sq, map_sum]

theorem diagConj_mul_diagConj (u : Matrix.unitaryGroup n 𝕜) (d e : n → ℝ)
    (h : ∀ i, d i * e i = 0) :
    (diagConj u d : Matrix n n 𝕜) * diagConj u e = 0 := by
  have hs : (star (u : Matrix n n 𝕜)) * (u : Matrix n n 𝕜) = 1 := Unitary.star_mul_self_of_mem u.2
  have hde : (fun i => (RCLike.ofReal ∘ d) i * (RCLike.ofReal ∘ e) i : n → 𝕜) = 0 := by
    funext i; simp [← RCLike.ofReal_mul, h i]
  simp only [diagConj, mul_assoc]
  rw [← mul_assoc (star (u : Matrix n n 𝕜)) (u : Matrix n n 𝕜), hs, one_mul,
    ← mul_assoc (diagonal (RCLike.ofReal ∘ d)), Matrix.diagonal_mul_diagonal, hde]
  simp

omit [Fintype n] [DecidableEq n] in
theorem psd_diag_re_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i : n) :
    0 ≤ RCLike.re (A i i) := (RCLike.nonneg_iff.mp hA.diag_nonneg).1

theorem trace_mul_diag (B : Matrix n n 𝕜) (e : n → 𝕜) :
    Matrix.trace (B * diagonal e) = ∑ i, B i i * e i := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]

theorem trace_mul_diagConj_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (u : Matrix.unitaryGroup n 𝕜) {d : n → ℝ} (hd : ∀ i, 0 ≤ d i) :
    0 ≤ RCLike.re (Matrix.trace (A * diagConj u d)) := by
  have hB : ((star (u : Matrix n n 𝕜)) * A * (u : Matrix n n 𝕜)).PosSemidef := by
    simpa [star_eq_conjTranspose] using hA.conjTranspose_mul_mul_same (B := (u : Matrix n n 𝕜))
  have hcyc : Matrix.trace (A * diagConj u d)
      = Matrix.trace ((star (u : Matrix n n 𝕜)) * A * (u : Matrix n n 𝕜)
          * diagonal (RCLike.ofReal ∘ d)) := by
    simp only [diagConj, ← mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [hcyc, trace_mul_diag, map_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have h : RCLike.re (((star (u : Matrix n n 𝕜)) * A * (u : Matrix n n 𝕜)) i i *
        (RCLike.ofReal ∘ d) i)
      = RCLike.re (((star (u : Matrix n n 𝕜)) * A * (u : Matrix n n 𝕜)) i i) * d i := by
    simp [RCLike.mul_re]
  rw [h]
  exact mul_nonneg (psd_diag_re_nonneg hB i) (hd i)

/-! ### The two scalar inequalities -/

omit [DecidableEq n] in
/-- Scalar core of the bound for the positive part of `Q`: if `d ≥ 0` has at most `b` positive
entries then `2c·∑ d − c²b ≤ ∑ d²`. -/
theorem scalar_pos_part_bound (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) {b : ℕ}
    (hb : (Finset.univ.filter fun i => 0 < d i).card ≤ b) (c : ℝ) :
    2 * c * (∑ i, d i) - c ^ 2 * b ≤ ∑ i, (d i) ^ 2 := by
  have key : ∑ i, (2 * c * d i - (d i) ^ 2) ≤ ∑ i : n, (if 0 < d i then c ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases lt_or_ge 0 (d i) with h | h
    · simp only [if_pos h]; nlinarith [sq_nonneg (c - d i)]
    · have h0 : d i = 0 := le_antisymm h (hd i)
      simp [h0]
  have h2 : ∑ i : n, (if 0 < d i then c ^ 2 else 0)
      = c ^ 2 * ((Finset.univ.filter fun i => 0 < d i).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : c ^ 2 * ((Finset.univ.filter fun i => 0 < d i).card : ℝ) ≤ c ^ 2 * b := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
    exact_mod_cast hb
  rw [Finset.sum_sub_distrib] at key
  simp only [← Finset.mul_sum] at key
  linarith [key, h2 ▸ h3]

omit [DecidableEq n] in
/-- Scalar core of the bound comparing `P` with the negative part of `Q`: if at most `r` of the
`l i` are nonzero and `rho ≥ 0` then `c·∑ l − (c²/4)r − 2c·∑ rho ≤ ∑ (l − rho)²`. -/
theorem scalar_rank_bound (l rho : n → ℝ) (hrho : ∀ i, 0 ≤ rho i) {r : ℕ}
    (hr : (Finset.univ.filter fun i => l i ≠ 0).card ≤ r) {c : ℝ} (hc : 0 < c) :
    c * (∑ i, l i) - c ^ 2 / 4 * r - 2 * c * (∑ i, rho i) ≤ ∑ i, (l i - rho i) ^ 2 := by
  have key : ∑ i, (c * l i - 2 * c * rho i - (l i - rho i) ^ 2)
      ≤ ∑ i : n, (if l i ≠ 0 then c ^ 2 / 4 else 0) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : l i = 0
    · simp only [h, ne_eq, not_true_eq_false, if_false]
      nlinarith [hrho i, sq_nonneg (rho i)]
    · simp only [ne_eq, h, not_false_eq_true, if_pos]
      nlinarith [sq_nonneg (l i - rho i - c / 2), hrho i, hc]
  have h2 : ∑ i : n, (if l i ≠ 0 then c ^ 2 / 4 else 0)
      = c ^ 2 / 4 * ((Finset.univ.filter fun i => l i ≠ 0).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : c ^ 2 / 4 * ((Finset.univ.filter fun i => l i ≠ 0).card : ℝ) ≤ c ^ 2 / 4 * r := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast hr
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at key
  simp only [← Finset.mul_sum] at key
  linarith [key, h2 ▸ h3]

/-! ### The matrix bound for `P` against a positive semidefinite matrix -/

/-- If `P` is positive semidefinite of rank at most `r` and `R` is positive semidefinite, then
`c·Re tr P − (c²/4)r − 2c·Re tr R ≤ ‖P − R‖_F²`. -/
theorem key_P_bound {P R : Matrix n n 𝕜} (hP : P.PosSemidef) (hR : R.PosSemidef)
    {r : ℕ} (hr : P.rank ≤ r) {c : ℝ} (hc : 0 < c) :
    c * RCLike.re P.trace - c ^ 2 / 4 * r - 2 * c * RCLike.re R.trace ≤ frobSq (P - R) := by
  have hPh : P.IsHermitian := hP.isHermitian
  set V := hPh.eigenvectorUnitary with hV
  set lam := hPh.eigenvalues with hlam
  have hPd : (star V : Matrix n n 𝕜) * P * (V : Matrix n n 𝕜)
      = diagonal (RCLike.ofReal ∘ lam) := by
    simpa [Unitary.conjStarAlgAut_star_apply] using hPh.conjStarAlgAut_star_eigenvectorUnitary
  set R' := (star V : Matrix n n 𝕜) * R * (V : Matrix n n 𝕜) with hR'def
  set D := (diagonal (RCLike.ofReal ∘ lam) : Matrix n n 𝕜) with hD
  have hR' : R'.PosSemidef := by
    simpa [hR'def, star_eq_conjTranspose] using
      hR.conjTranspose_mul_mul_same (B := (V : Matrix n n 𝕜))
  have hfrob : frobSq (P - R) = frobSq (D - R') := by
    rw [← frobSq_conj_unitary V (P - R)]
    congr 1
    rw [Matrix.mul_sub, Matrix.sub_mul, hPd]
  have hentry : ∀ i, (D - R') i i = RCLike.ofReal (lam i - RCLike.re (R' i i)) := by
    intro i
    have h := hR'.isHermitian.coe_re_apply_self i
    simp only [hD, Matrix.sub_apply, Matrix.diagonal_apply_eq, Function.comp_apply]
    rw [← h]
    push_cast
    ring
  have hdiag : ∑ i, (lam i - RCLike.re (R' i i)) ^ 2 ≤ frobSq (D - R') := by
    refine le_trans (le_of_eq ?_) (sum_diag_sq_le_frobSq _)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hentry i, RCLike.norm_ofReal, sq_abs]
  have htrP : RCLike.re P.trace = ∑ i, lam i := by
    have h : Matrix.trace P = Matrix.trace D := by rw [← hPd, trace_conj_unitary]
    rw [h, hD, Matrix.trace_diagonal]
    simp
  have htrR : RCLike.re R.trace = ∑ i, RCLike.re (R' i i) := by
    have h : Matrix.trace R = Matrix.trace R' := (trace_conj_unitary V R).symm
    rw [h, Matrix.trace, map_sum]
    rfl
  have hcard : (Finset.univ.filter fun i => lam i ≠ 0).card ≤ r := by
    rw [← Fintype.card_subtype, ← hPh.rank_eq_card_non_zero_eigs]
    exact hr
  rw [hfrob, htrP, htrR]
  exact le_trans (scalar_rank_bound lam (fun i => RCLike.re (R' i i))
    (fun i => psd_diag_re_nonneg hR' i) hcard hc) hdiag

/-! ### Main theorem -/

/-- **Rank–trace inequality** (preprint Lemma 3.2).  If `P` is positive semidefinite of rank at
most `r`, `Q` is Hermitian with at most `b` positive eigenvalues, and `c > 0`, then
`c·Re tr P − (c²/4)·r + 2c·Re tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
theorem rank_trace_ineq {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * RCLike.re P.trace - c ^ 2 / 4 * r + 2 * c * RCLike.re Q.trace - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  set U := hQ.eigenvectorUnitary with hU
  set mu := hQ.eigenvalues with hmu
  set dp : n → ℝ := fun i => max (mu i) 0 with hdpdef
  set dm : n → ℝ := fun i => max (-(mu i)) 0 with hdmdef
  have hdp : ∀ i, 0 ≤ dp i := fun i => le_max_right _ _
  have hdm : ∀ i, 0 ≤ dm i := fun i => le_max_right _ _
  have hmusplit : ∀ i, mu i = dp i - dm i := by
    intro i
    simp only [hdpdef, hdmdef]
    rcases le_or_gt 0 (mu i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h.le, max_eq_left (by linarith)]; ring
  set Qp := (diagConj U dp : Matrix n n 𝕜) with hQp
  set Qm := (diagConj U dm : Matrix n n 𝕜) with hQm
  have hQdiag : Q = diagConj U mu := by
    rw [diagConj]
    exact hQ.spectral_theorem
  have hQsplit : Q = Qp - Qm := by
    rw [hQdiag, hQp, hQm, ← diagConj_sub]
    congr 1
    funext i
    exact hmusplit i
  have hQpPSD : Qp.PosSemidef := diagConj_posSemidef U hdp
  have hQmPSD : Qm.PosSemidef := diagConj_posSemidef U hdm
  -- splitting of the Frobenius norm
  have hsplit : P + Q = (P - Qm) + Qp := by rw [hQsplit]; abel
  have hcrossterm : RCLike.re (Matrix.trace ((P - Qm)ᴴ * Qp))
      = RCLike.re (Matrix.trace (P * Qp)) := by
    have hherm : (P - Qm)ᴴ = P - Qm := by
      rw [Matrix.conjTranspose_sub, hP.isHermitian, hQmPSD.isHermitian]
    have hzero : Qm * Qp = 0 := by
      refine diagConj_mul_diagConj U dm dp fun i => ?_
      simp only [hdpdef, hdmdef]
      rcases le_or_gt 0 (mu i) with h | h
      · rw [max_eq_right (by linarith : -(mu i) ≤ 0)]; ring
      · rw [max_eq_right h.le]; ring
    rw [hherm, Matrix.sub_mul, Matrix.trace_sub, hzero, Matrix.trace_zero]
    simp
  have hcross : 0 ≤ RCLike.re (Matrix.trace ((P - Qm)ᴴ * Qp)) := by
    rw [hcrossterm, hQp]
    exact trace_mul_diagConj_nonneg hP U hdp
  have hfrobsplit : frobSq (P - Qm) + frobSq Qp ≤ frobSq (P + Q) := by
    rw [hsplit, frobSq_add]
    linarith
  -- traces
  have htrQm : RCLike.re Qm.trace = ∑ i, dm i := trace_diagConj U dm
  have htrQ : RCLike.re Q.trace = (∑ i, dp i) - ∑ i, dm i := by
    rw [hQsplit, Matrix.trace_sub, map_sub, trace_diagConj, trace_diagConj]
  -- the two bounds
  have hcardp : (Finset.univ.filter fun i => 0 < dp i).card ≤ b := by
    refine le_trans (le_of_eq ?_) hb
    unfold posIndex
    congr 1
    apply Finset.filter_congr
    intro i _
    simp [hdpdef, hmu]
  have hboundQ : 2 * c * (∑ i, dp i) - c ^ 2 * b ≤ frobSq Qp := by
    rw [hQp, frobSq_diagConj]
    exact scalar_pos_part_bound dp hdp hcardp c
  have hboundP : c * RCLike.re P.trace - c ^ 2 / 4 * r - 2 * c * (∑ i, dm i)
      ≤ frobSq (P - Qm) := by
    have := key_P_bound hP hQmPSD hr hc
    rwa [htrQm] at this
  rw [htrQ]
  linarith

end Zeta23Core

