import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic definitions -/

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr (Mᴴ M)`. -/
noncomputable def frobSq (M : Matrix n n 𝕜) : ℝ := RCLike.re (Matrix.trace (Mᴴ * M))

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues. -/
noncomputable def posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : ℕ :=
  Nat.card {i // 0 < hQ.eigenvalues i}

/-! ## Functional calculus for Hermitian matrices -/

/-- `hFun hA g` is the matrix obtained by applying the real function `g` to the eigenvalues of
the Hermitian matrix `A`, in an eigenbasis of `A`. -/
noncomputable def hFun {A : Matrix n n 𝕜} (hA : A.IsHermitian) (g : ℝ → ℝ) : Matrix n n 𝕜 :=
  (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => (RCLike.ofReal (g (hA.eigenvalues i)) : 𝕜)) *
    star (hA.eigenvectorUnitary : Matrix n n 𝕜)

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

lemma hFun_congr {g h : ℝ → ℝ} (hgh : ∀ i, g (hA.eigenvalues i) = h (hA.eigenvalues i)) :
    hFun hA g = hFun hA h := by
  have h' : (fun i => (RCLike.ofReal (g (hA.eigenvalues i)) : 𝕜))
      = fun i => (RCLike.ofReal (h (hA.eigenvalues i)) : 𝕜) := funext fun i => by rw [hgh i]
  simp only [hFun, h']

lemma hFun_mul (g h : ℝ → ℝ) :
    hFun hA g * hFun hA h = hFun hA (fun x => g x * h x) := by
  have hU : star (hA.eigenvectorUnitary : Matrix n n 𝕜) * (hA.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := Unitary.coe_star_mul_self _
  simp only [hFun, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix n n 𝕜)), hU, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
  simp

lemma hFun_id : hFun hA (fun x => x) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  simp [hFun, Unitary.conjStarAlgAut_apply, Function.comp_def]

lemma hFun_one : hFun hA (fun _ => 1) = 1 := by
  simp [hFun]

lemma hFun_zero : hFun hA (fun _ => 0) = 0 := by
  simp [hFun]

lemma hFun_add (g h : ℝ → ℝ) : hFun hA g + hFun hA h = hFun hA (fun x => g x + h x) := by
  simp only [hFun, ← Matrix.add_mul, ← Matrix.mul_add]
  simp

lemma hFun_isHermitian (g : ℝ → ℝ) : (hFun hA g).IsHermitian := by
  unfold Matrix.IsHermitian hFun
  rw [conjTranspose_mul, conjTranspose_mul]
  simp [Matrix.star_eq_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def,
    RCLike.star_def]

lemma trace_hFun (g : ℝ → ℝ) :
    (hFun hA g).trace = ∑ i, (RCLike.ofReal (g (hA.eigenvalues i)) : 𝕜) := by
  rw [hFun, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul,
    trace_diagonal]

lemma re_trace_hFun (g : ℝ → ℝ) :
    RCLike.re ((hFun hA g).trace) = ∑ i, g (hA.eigenvalues i) := by
  rw [trace_hFun, map_sum]
  simp

lemma hFun_posSemidef {g : ℝ → ℝ} (hg : ∀ i, 0 ≤ g (hA.eigenvalues i)) :
    (hFun hA g).PosSemidef := by
  have hd : (diagonal (fun i => (RCLike.ofReal (g (hA.eigenvalues i)) : 𝕜))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    have : (0:ℝ) ≤ g (hA.eigenvalues i) := hg i
    simpa using RCLike.ofReal_nonneg (K := 𝕜) |>.mpr this
  have := hd.mul_mul_conjTranspose_same (B := (hA.eigenvectorUnitary : Matrix n n 𝕜))
  simpa [hFun, Matrix.star_eq_conjTranspose] using this

/-! ## Generalities on the Frobenius norm and traces -/

omit [DecidableEq n] in
lemma frobSq_nonneg (M : Matrix n n 𝕜) : 0 ≤ frobSq M := by
  have h : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have := h.trace_nonneg
  simpa [frobSq] using RCLike.re_le_re this

omit [DecidableEq n] in
lemma frobSq_sub (M X : Matrix n n 𝕜) :
    frobSq (M - X) = frobSq M - 2 * RCLike.re (Matrix.trace (Mᴴ * X)) + frobSq X := by
  have hcross : RCLike.re (Matrix.trace (Xᴴ * M)) = RCLike.re (Matrix.trace (Mᴴ * X)) := by
    have h : (Mᴴ * X)ᴴ = Xᴴ * M := by simp
    rw [← h, Matrix.trace_conjTranspose]
    simp
  simp only [frobSq, conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, map_sub,
    hcross]
  ring

omit [DecidableEq n] in
lemma frobSq_ge (M X : Matrix n n 𝕜) :
    2 * RCLike.re (Matrix.trace (Mᴴ * X)) - frobSq X ≤ frobSq M := by
  have h := frobSq_nonneg (M - X)
  rw [frobSq_sub] at h
  linarith

/-- The trace of the product of two positive semidefinite matrices is nonnegative. -/
lemma re_trace_mul_nonneg {P₁ P₂ : Matrix n n 𝕜} (h₁ : P₁.PosSemidef) (h₂ : P₂.PosSemidef) :
    0 ≤ RCLike.re (Matrix.trace (P₁ * P₂)) := by
  obtain ⟨T, hTpsd, hTT⟩ : ∃ T : Matrix n n 𝕜, T.PosSemidef ∧ T * T = P₁ := by
    refine ⟨hFun h₁.1 Real.sqrt, hFun_posSemidef h₁.1 fun i => Real.sqrt_nonneg _, ?_⟩
    rw [hFun_mul, show (hFun h₁.1 fun x => Real.sqrt x * Real.sqrt x) = hFun h₁.1 (fun x => x) from
      hFun_congr h₁.1 fun i => Real.mul_self_sqrt (h₁.eigenvalues_nonneg i), hFun_id]
  have hTH : Tᴴ = T := hTpsd.1
  have key : Matrix.trace (P₁ * P₂) = Matrix.trace (Tᴴ * P₂ * T) := by
    rw [hTH, ← hTT, Matrix.mul_assoc, Matrix.trace_mul_comm T (T * P₂), Matrix.mul_assoc]
  rw [key]
  simpa using RCLike.re_le_re (h₂.conjTranspose_mul_mul_same T).trace_nonneg

omit [DecidableEq n] in
/-- A Hermitian idempotent matrix is positive semidefinite. -/
lemma posSemidef_of_idem {G : Matrix n n 𝕜} (hG : G.IsHermitian) (hGG : G * G = G) :
    G.PosSemidef := by
  have h : G = Gᴴ * G := by rw [hG, hGG]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self G

/-! ## Spectral projections -/

/-- The spectral projection onto the positive part of a Hermitian matrix `Q`, together with its
complement `R` and the negative part `S = -R Q R` of `Q`. -/
lemma exists_pos_proj {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    ∃ E R S : Matrix n n 𝕜, Eᴴ = E ∧ Rᴴ = R ∧ E + R = 1 ∧ E * E = E ∧ R * R = R ∧
      E * R = 0 ∧ R * E = 0 ∧ R * Q * R = -S ∧ S.PosSemidef ∧
      RCLike.re E.trace = (posIndex hQ : ℝ) := by
  classical
  refine ⟨hFun hQ (fun x => if 0 < x then 1 else 0), hFun hQ (fun x => if 0 < x then 0 else 1),
    hFun hQ (fun x => if 0 < x then 0 else -x), hFun_isHermitian hQ _, hFun_isHermitian hQ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFun_add, ← hFun_one hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul, ← hFun_zero hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul, ← hFun_zero hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · have key : hFun hQ (fun x => if 0 < x then (0:ℝ) else 1) * hFun hQ (fun x => x) *
        hFun hQ (fun x => if 0 < x then (0:ℝ) else 1)
        = hFun hQ (fun x => (if 0 < x then (0:ℝ) else 1) * x * (if 0 < x then (0:ℝ) else 1)) := by
      rw [hFun_mul, hFun_mul]
    rw [hFun_id] at key
    rw [key, eq_comm, neg_eq_iff_add_eq_zero, hFun_add, ← hFun_zero hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> ring
  · refine hFun_posSemidef hQ fun i => ?_
    split_ifs with h
    · exact le_refl 0
    · linarith [not_lt.mp h]
  · rw [re_trace_hFun, posIndex, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [Finset.sum_boole]

/-- The orthogonal projection onto the range of a positive semidefinite matrix `A`. -/
lemma exists_range_proj {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ F B : Matrix n n 𝕜, Fᴴ = F ∧ F * F = F ∧ A * F = A ∧ A * B = F ∧
      RCLike.re F.trace = (A.rank : ℝ) := by
  classical
  refine ⟨hFun hA.1 (fun x => if x ≠ 0 then 1 else 0),
    hFun hA.1 (fun x => if x ≠ 0 then x⁻¹ else 0), hFun_isHermitian hA.1 _, ?_, ?_, ?_, ?_⟩
  · rw [hFun_mul]
    exact hFun_congr hA.1 fun i => by split_ifs <;> norm_num
  · have key : hFun hA.1 (fun x => x) * hFun hA.1 (fun x => if x ≠ 0 then (1:ℝ) else 0)
        = hFun hA.1 (fun x => x * (if x ≠ 0 then (1:ℝ) else 0)) := hFun_mul hA.1 _ _
    rw [hFun_id] at key
    rw [key, show (hFun hA.1 fun x => x * (if x ≠ 0 then (1:ℝ) else 0))
        = hFun hA.1 (fun x => x) from hFun_congr hA.1 fun i => by
          split_ifs with h
          · ring
          · simp only [ne_eq, not_not] at h; simp [h]]
    exact hFun_id hA.1
  · have key : hFun hA.1 (fun x => x) * hFun hA.1 (fun x => if x ≠ 0 then x⁻¹ else 0)
        = hFun hA.1 (fun x => x * (if x ≠ 0 then x⁻¹ else 0)) := hFun_mul hA.1 _ _
    rw [hFun_id] at key
    rw [key]
    exact hFun_congr hA.1 fun i => by
      split_ifs with h
      · exact mul_inv_cancel₀ h
      · ring
  · rw [re_trace_hFun, hA.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp_all

/-! ## Two computations with the test matrix -/

lemma re_trace_mul_comb (M E F : Matrix n n 𝕜) (c d : ℝ) :
    RCLike.re (Matrix.trace (M * ((c : 𝕜) • E + (d : 𝕜) • F)))
      = c * RCLike.re (Matrix.trace (M * E)) + d * RCLike.re (Matrix.trace (M * F)) := by
  simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, RCLike.smul_re]

omit [DecidableEq n] in
lemma frobSq_proj_comb {E F : Matrix n n 𝕜} (hEH : Eᴴ = E) (hFH : Fᴴ = F)
    (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0) (hFE : F * E = 0) (c d : ℝ) :
    frobSq ((c : 𝕜) • E + (d : 𝕜) • F)
      = c ^ 2 * RCLike.re E.trace + d ^ 2 * RCLike.re F.trace := by
  have hXH : (((c : 𝕜) • E + (d : 𝕜) • F))ᴴ = (c : 𝕜) • E + (d : 𝕜) • F := by
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, hEH, hFH]
    simp
  rw [frobSq, hXH]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hEE, hFF, hEF, hFE,
    smul_zero, add_zero, zero_add, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, map_add, smul_smul]
  simp [RCLike.mul_re]
  ring

/-! ## The main inequality -/

/-- **Rank–trace inequality** (Lemma 3.2).  If `P` is positive semidefinite of rank at most `r`,
`Q` is Hermitian with at most `b` positive eigenvalues, and `c > 0`, then
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
theorem rank_trace_ineq {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (r b : ℕ) (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) (c : ℝ) (hc : 0 < c) :
    c * RCLike.re P.trace - c ^ 2 / 4 * r + 2 * c * RCLike.re Q.trace - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  classical
  obtain ⟨E, R, S, hEH, hRH, hER1, hEE, hRR, hER0, hRE0, hRQR, hSpsd, hEtr⟩ :=
    exists_pos_proj hQ
  have hEpsd : E.PosSemidef := posSemidef_of_idem hEH hEE
  have hRPRpsd : (R * P * R).PosSemidef := by
    have h := hP.conjTranspose_mul_mul_same R
    rwa [hRH] at h
  obtain ⟨F, B, hFH, hFF, hAF, hAB, hFtr⟩ := exists_range_proj hRPRpsd
  -- `F` lives inside the range of `R`
  have hRRP : R * (R * P * R) = R * P * R := by
    rw [← Matrix.mul_assoc R (R * P) R, ← Matrix.mul_assoc R R P, hRR]
  have hRF : R * F = F := by
    rw [← hAB, ← Matrix.mul_assoc, hRRP]
  have hFR : F * R = F := by
    have h := congrArg Matrix.conjTranspose hRF
    rw [conjTranspose_mul, hFH, hRH] at h
    exact h
  have hRFR : R * F * R = F := by rw [hRF, hFR]
  have hEF : E * F = 0 := by rw [← hRF, ← Matrix.mul_assoc, hER0, Matrix.zero_mul]
  have hFE : F * E = 0 := by rw [← hFR, Matrix.mul_assoc, hRE0, Matrix.mul_zero]
  have hFpsd : F.PosSemidef := posSemidef_of_idem hFH hFF
  -- `R = 1 - E`
  have hRE : R = 1 - E := by rw [← hER1]; abel
  -- traces
  have hpe : 0 ≤ RCLike.re (Matrix.trace (P * E)) := re_trace_mul_nonneg hP hEpsd
  have hs : 0 ≤ RCLike.re S.trace := by simpa using RCLike.re_le_re hSpsd.trace_nonneg
  have hSFle : RCLike.re (Matrix.trace (S * F)) ≤ RCLike.re S.trace := by
    have h1 : (1 - F : Matrix n n 𝕜).PosSemidef := by
      refine posSemidef_of_idem (by simp [Matrix.IsHermitian, hFH]) ?_
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hFF]
      simp
    have h2 := re_trace_mul_nonneg hSpsd h1
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, map_sub] at h2
    linarith
  have hPF : RCLike.re (Matrix.trace (P * F))
      = RCLike.re P.trace - RCLike.re (Matrix.trace (P * E)) := by
    have e1 : Matrix.trace (P * F) = Matrix.trace (R * P * R * F) := by
      calc Matrix.trace (P * F) = Matrix.trace (P * (R * F * R)) := by rw [hRFR]
        _ = Matrix.trace (P * R * F * R) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace (R * (P * R * F)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (R * P * R * F) := by simp [Matrix.mul_assoc]
    have e2 : Matrix.trace (R * P * R * F) = Matrix.trace (P * R) := by
      calc Matrix.trace (R * P * R * F) = Matrix.trace (R * P * R) := by rw [hAF]
        _ = Matrix.trace (R * (P * R)) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace (P * R * R) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (P * (R * R)) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace (P * R) := by rw [hRR]
    have e3 : Matrix.trace (P * R) = Matrix.trace P - Matrix.trace (P * E) := by
      rw [hRE, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
    rw [e1, e2, e3, map_sub]
  have hQR : Matrix.trace (Q * R) = -Matrix.trace S := by
    have e1 : Matrix.trace (Q * R) = Matrix.trace (R * Q * R) := by
      calc Matrix.trace (Q * R) = Matrix.trace (Q * (R * R)) := by rw [hRR]
        _ = Matrix.trace (Q * R * R) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace (R * (Q * R)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (R * Q * R) := by simp [Matrix.mul_assoc]
    rw [e1, hRQR, Matrix.trace_neg]
  have hQE : RCLike.re (Matrix.trace (Q * E))
      = RCLike.re Q.trace + RCLike.re S.trace := by
    have e0 : Matrix.trace (Q * E) + Matrix.trace (Q * R) = Matrix.trace Q := by
      rw [← Matrix.trace_add, ← Matrix.mul_add, hER1, Matrix.mul_one]
    have h := congrArg RCLike.re e0
    rw [map_add, hQR, map_neg] at h
    linarith
  have hQF : -RCLike.re S.trace ≤ RCLike.re (Matrix.trace (Q * F)) := by
    have e1 : Matrix.trace (Q * F) = Matrix.trace (R * Q * R * F) := by
      calc Matrix.trace (Q * F) = Matrix.trace (Q * (R * F * R)) := by rw [hRFR]
        _ = Matrix.trace (Q * R * F * R) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace (R * (Q * R * F)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (R * Q * R * F) := by simp [Matrix.mul_assoc]
    rw [e1, hRQR, Matrix.neg_mul, Matrix.trace_neg, map_neg]
    linarith
  -- rank / index bounds
  have hEb : RCLike.re E.trace ≤ (b : ℝ) := by
    rw [hEtr]; exact_mod_cast hb
  have hFr : RCLike.re F.trace ≤ (r : ℝ) := by
    rw [hFtr]
    have h1 : (R * P * R).rank ≤ P.rank :=
      le_trans (Matrix.rank_mul_le_left (R * P) R) (Matrix.rank_mul_le_right R P)
    exact_mod_cast le_trans h1 hr
  -- the variational bound
  have hMH : (P + Q)ᴴ = P + Q := by rw [conjTranspose_add, hP.1, hQ]
  have main := frobSq_ge (P + Q) ((c : 𝕜) • E + ((c / 2 : ℝ) : 𝕜) • F)
  rw [hMH, re_trace_mul_comb, frobSq_proj_comb hEH hFH hEE hFF hEF hFE] at main
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add, map_add, map_add] at main
  nlinarith [main, hpe, hs, hSFle, hPF, hQE, hQF, hEb, hFr, hc.le, sq_nonneg c]


/-! ## A scalar shadow of the inequality

Instantiating `rank_trace_ineq` with `P = 0`, `Q = (m)` a `1 × 1` real matrix, `r = 0`, `b = 1`
and `c = 1` yields the integrality step `2 m - 1 ≤ m ^ 2`.  This is recorded to witness that the
main inequality is not vacuous. -/

theorem two_mul_sub_one_le_sq (m : ℝ) : 2 * m - 1 ≤ m ^ 2 := by
  have hQ : ((!![m] : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hb : posIndex hQ ≤ 1 := by
    have h := Nat.card_le_card_of_injective
      (Subtype.val : {i // 0 < hQ.eigenvalues i} → Fin 1) Subtype.val_injective
    simpa [posIndex] using h
  have h := rank_trace_ineq (P := (0 : Matrix (Fin 1) (Fin 1) ℝ)) (Q := !![m])
    Matrix.PosSemidef.zero hQ 0 1 (by simp) hb 1 one_pos
  have hf : frobSq ((0 : Matrix (Fin 1) (Fin 1) ℝ) + !![m]) = m ^ 2 := by
    rw [zero_add, frobSq, Matrix.trace_fin_one]
    simp [Matrix.mul_apply]
    ring
  rw [hf] at h
  simpa using h

end Zeta23Core

