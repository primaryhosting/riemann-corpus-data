/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `eigenProj v w` is the orthogonal projection of `w` onto the complex line spanned by
the unit vector `v`; for a nondegenerate eigenvector `v` of a Hamiltonian this is the
projection onto the corresponding instantaneous eigenspace. -/
noncomputable def eigenProj (v w : E) : E := (inner ℂ v w : ℂ) • v

/-- A linear map preserving inner products preserves norms. -/
lemma norm_map_of_inner_preserving {U : E →ₗ[ℂ] E}
    (hU : ∀ w z : E, (inner ℂ (U w) (U z) : ℂ) = inner ℂ w z) (w : E) :
    ‖U w‖ = ‖w‖ := by
  have h1 : ‖U w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (U w), ← inner_self_eq_norm_sq (𝕜 := ℂ) w, hU w w]
  nlinarith [norm_nonneg (U w), norm_nonneg w]

/-- A unitary map commuting with the Hamiltonian maps a nondegenerate eigenvector to a
unimodular multiple of itself. -/
lemma exists_phase_of_commute {H U : E →ₗ[ℂ] E} {v : E} {lam : ℂ}
    (hunit : ‖v‖ = 1)
    (heig : H v = lam • v)
    (hnondeg : ∀ w : E, H w = lam • w → ∃ c : ℂ, w = c • v)
    (hU : ∀ w z : E, (inner ℂ (U w) (U z) : ℂ) = inner ℂ w z)
    (hcomm : ∀ w : E, U (H w) = H (U w)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U v = c • v := by
  have hev : H (U v) = lam • U v := by
    rw [← hcomm v, heig, map_smul]
  obtain ⟨c, hc⟩ := hnondeg _ hev
  refine ⟨c, ?_, hc⟩
  have h1 : ‖U v‖ = 1 := by rw [norm_map_of_inner_preserving hU v, hunit]
  rw [hc] at h1
  simpa [norm_smul, hunit] using h1

/-- A unitary map that multiplies `v` by a unimodular scalar commutes with the orthogonal
projection onto the line spanned by `v`. -/
lemma eigenProj_commute_of_phase {U : E →ₗ[ℂ] E} {v : E} {c : ℂ}
    (hc1 : ‖c‖ = 1) (hUv : U v = c • v)
    (hU : ∀ w z : E, (inner ℂ (U w) (U z) : ℂ) = inner ℂ w z) (w : E) :
    U (eigenProj v w) = eigenProj v (U w) := by
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq, hc1]
  have key : (inner ℂ v (U w) : ℂ) = c * inner ℂ v w := by
    have h := hU v w
    rw [hUv, inner_smul_left] at h
    calc (inner ℂ v (U w) : ℂ) = (c * (starRingEnd ℂ) c) * inner ℂ v (U w) := by rw [hcc, one_mul]
      _ = c * ((starRingEnd ℂ) c * inner ℂ v (U w)) := by ring
      _ = c * inner ℂ v w := by rw [h]
  simp only [eigenProj, map_smul, hUv, key, smul_smul]
  ring_nf

/-- The instantaneous propagator commutes with the projection onto the instantaneous
(nondegenerate) eigenspace. -/
lemma eigenProj_commute {H U : E →ₗ[ℂ] E} {v : E} {lam : ℂ}
    (hunit : ‖v‖ = 1)
    (heig : H v = lam • v)
    (hnondeg : ∀ w : E, H w = lam • w → ∃ c : ℂ, w = c • v)
    (hU : ∀ w z : E, (inner ℂ (U w) (U z) : ℂ) = inner ℂ w z)
    (hcomm : ∀ w : E, U (H w) = H (U w)) (w : E) :
    U (eigenProj v w) = eigenProj v (U w) := by
  obtain ⟨c, hc1, hUv⟩ := exists_phase_of_commute hunit heig hnondeg hU hcomm
  exact eigenProj_commute_of_phase hc1 hUv hU w

/--
**Adiabatic theorem** (discrete-time form).

Let `H n` be a time-dependent Hamiltonian on a complex inner product space, with an
instantaneous *nondegenerate* eigenvector `v n` of unit norm for the eigenvalue `lam n`
(nondegeneracy: every vector in the `lam n`-eigenspace is a multiple of `v n`), so that
`eigenProj (v n)` is the orthogonal projection onto the instantaneous eigenspace.  Let
`U n` be the propagator over the `n`-th time step: it preserves inner products (unitary)
and commutes with the instantaneous Hamiltonian `H n`.  The hypothesis `hslow` says the
Hamiltonian varies *slowly*: the instantaneous eigenprojection changes by at most `eps`
(in operator norm) per step.

If the initial state `psi 0` lies in the initial eigenspace, then after `N` steps the
state stays in the instantaneous eigenspace up to an error `N * eps * ‖psi 0‖`.  In
particular, in the adiabatic limit (`N * eps → 0`) the state remains in the instantaneous
eigenspace.
-/
theorem adiabatic_theorem
    (H U : ℕ → E →ₗ[ℂ] E) (v : ℕ → E) (lam : ℕ → ℂ) (psi : ℕ → E) (eps : ℝ)
    (hunit : ∀ n, ‖v n‖ = 1)
    (heig : ∀ n, H n (v n) = lam n • v n)
    (hnondeg : ∀ (n : ℕ) (w : E), H n w = lam n • w → ∃ c : ℂ, w = c • v n)
    (hU : ∀ (n : ℕ) (w z : E), (inner ℂ (U n w) (U n z) : ℂ) = inner ℂ w z)
    (hcomm : ∀ (n : ℕ) (w : E), U n (H n w) = H n (U n w))
    (hslow : ∀ (n : ℕ) (w : E), ‖eigenProj (v (n + 1)) w - eigenProj (v n) w‖ ≤ eps * ‖w‖)
    (hstart : psi 0 = eigenProj (v 0) (psi 0))
    (hstep : ∀ n, psi (n + 1) = U n (psi n))
    (N : ℕ) :
    ‖psi N - eigenProj (v N) (psi N)‖ ≤ N * eps * ‖psi 0‖ := by
  -- The evolution is norm preserving.
  have hnorm : ∀ n, ‖psi n‖ = ‖psi 0‖ := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [hstep k, norm_map_of_inner_preserving (hU k), ih]
  induction N with
  | zero =>
      simp [← hstart]
  | succ n ih =>
      have hcm : U n (eigenProj (v n) (psi n)) = eigenProj (v n) (U n (psi n)) :=
        eigenProj_commute (hunit n) (heig n) (hnondeg n) (hU n) (hcomm n) (psi n)
      have hsplit :
          psi (n + 1) - eigenProj (v (n + 1)) (psi (n + 1))
            = U n (psi n - eigenProj (v n) (psi n))
              + (eigenProj (v n) (U n (psi n)) - eigenProj (v (n + 1)) (U n (psi n))) := by
        rw [hstep n, map_sub, hcm]
        abel
      have hb1 : ‖U n (psi n - eigenProj (v n) (psi n))‖ ≤ n * eps * ‖psi 0‖ := by
        rw [norm_map_of_inner_preserving (hU n)]
        exact ih
      have hb2 : ‖eigenProj (v n) (U n (psi n)) - eigenProj (v (n + 1)) (U n (psi n))‖
          ≤ eps * ‖psi 0‖ := by
        rw [norm_sub_rev]
        have := hslow n (U n (psi n))
        rwa [norm_map_of_inner_preserving (hU n), hnorm n] at this
      calc ‖psi (n + 1) - eigenProj (v (n + 1)) (psi (n + 1))‖
          = ‖U n (psi n - eigenProj (v n) (psi n))
              + (eigenProj (v n) (U n (psi n)) - eigenProj (v (n + 1)) (U n (psi n)))‖ := by
            rw [hsplit]
        _ ≤ ‖U n (psi n - eigenProj (v n) (psi n))‖
              + ‖eigenProj (v n) (U n (psi n)) - eigenProj (v (n + 1)) (U n (psi n))‖ :=
            norm_add_le _ _
        _ ≤ n * eps * ‖psi 0‖ + eps * ‖psi 0‖ := add_le_add hb1 hb2
        _ = (n + 1 : ℕ) * eps * ‖psi 0‖ := by push_cast; ring

end Phys

