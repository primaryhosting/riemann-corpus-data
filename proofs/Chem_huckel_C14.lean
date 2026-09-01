import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₄`, i.e. the Hückel matrix of the
carbon skeleton of a 14-membered annulene in units where `α = 0` and `β = 1`. -/
noncomputable def C14adj : Matrix (Fin 14) (Fin 14) ℂ := (cycleGraph 14).adjMatrix ℂ

/-- The standard additive character `j ↦ exp (2 π I j / 14)` on `ZMod 14`. -/
private noncomputable abbrev chi : AddChar (ZMod 14) ℂ := ZMod.stdAddChar

/-- Multiplying by the adjacency matrix of `C₁₄` sums the two cyclic neighbours. -/
private lemma C14adj_mulVec (v : Fin 14 → ℂ) (i : Fin 14) :
    C14adj.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : i - 1 ≠ i + 1 := by revert i; decide
  rw [C14adj, SimpleGraph.adjMatrix_mulVec_apply]
  rw [show (14 : ℕ) = 12 + 2 from rfl] at *
  rw [SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]

/-- The same statement, with the index set `Fin 14` viewed as the additive group `ZMod 14`. -/
private lemma C14adj_mulVec_zmod (v : ZMod 14 → ℂ) (i : ZMod 14) :
    C14adj.mulVec v i = v (i + -1) + v (i + 1) := by
  have h := C14adj_mulVec v i
  rw [sub_eq_add_neg] at h
  exact h

/-- `χ(k) + χ(-k) = 2 cos (2πk/14)`. -/
private lemma chi_add_chi_neg (k : ZMod 14) :
    chi k + chi (-k) = 2 * Real.cos (2 * π * k.val / 14) := by
  have h1 : chi k = Complex.exp ((2 * π * k.val / 14 : ℝ) * I) := by
    rw [chi, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    push_cast; ring_nf
  have h2 : chi (-k) = (chi k)⁻¹ := AddChar.map_neg_eq_inv _ _
  rw [h2, h1, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    ← Complex.ofReal_neg, ← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

/-- Translation rule for the discrete Fourier transform on `ZMod 14`. -/
private lemma dft_shift (v : ZMod 14 → ℂ) (a k : ZMod 14) :
    ZMod.dft (fun j => v (j + a)) k = chi (a * k) * ZMod.dft v k := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ (fun j => ?_)
  simp only [Equiv.coe_addRight, smul_eq_mul, chi]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  ring_nf

/-- **Hückel theory for C₁₄.** The eigenvalues of the adjacency matrix of the cycle graph `C₁₄`
are exactly the numbers `2 cos (2πk/14)` for `k = 0, 1, …, 13`. -/
theorem huckel_C14 :
    {μ : ℂ | ∃ v : Fin 14 → ℂ, v ≠ 0 ∧ C14adj.mulVec v = μ • v}
      = {μ : ℂ | ∃ k : ℕ, k < 14 ∧ μ = 2 * Real.cos (2 * π * k / 14)} := by
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, hA⟩
    obtain ⟨V, hV⟩ : ∃ V : ZMod 14 → ℂ, V = v := ⟨v, rfl⟩
    have hVne : V ≠ 0 := by rw [hV]; exact hv
    have hAV : ∀ i : ZMod 14, C14adj.mulVec V i = μ * V i := by
      rw [hV]; exact fun i => congrFun hA i
    have hw0 : ZMod.dft (N := 14) V ≠ 0 := by simpa using hVne
    obtain ⟨k, hk⟩ : ∃ k : ZMod 14, ZMod.dft (N := 14) V k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw0 (funext h)
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    have hfun : (fun j : ZMod 14 => V (j + -1)) + (fun j : ZMod 14 => V (j + 1)) = μ • V := by
      funext i
      have h := hAV i
      rw [C14adj_mulVec_zmod] at h
      exact h
    have h2 := congrArg (fun f : ZMod 14 → ℂ => ZMod.dft (N := 14) f k) hfun
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [dft_shift, dft_shift] at h2
    have h3 : (chi (-1 * k) + chi (1 * k)) * ZMod.dft (N := 14) V k
        = μ * ZMod.dft (N := 14) V k := by rw [add_mul]; exact h2
    have h4 : chi (-1 * k) + chi (1 * k) = μ := mul_right_cancel₀ hk h3
    rw [neg_one_mul, one_mul, add_comm] at h4
    rw [← h4, chi_add_chi_neg]
  · rintro ⟨k, hk, rfl⟩
    have hKval : ((k : ZMod 14)).val = k := ZMod.val_natCast_of_lt hk
    refine ⟨fun j : ZMod 14 => chi ((k : ZMod 14) * j), ?_, ?_⟩
    · intro h
      have h0 := congrFun h (0 : ZMod 14)
      simp at h0
    · have key : ∀ i : ZMod 14, C14adj.mulVec (fun j : ZMod 14 => chi ((k : ZMod 14) * j)) i
          = (2 * (Real.cos (2 * π * k / 14) : ℂ)) * chi ((k : ZMod 14) * i) := by
        intro i
        rw [C14adj_mulVec_zmod]
        have e1 : (k : ZMod 14) * (i + -1) = (k : ZMod 14) * i + (-(k : ZMod 14)) := by ring
        have e2 : (k : ZMod 14) * (i + 1) = (k : ZMod 14) * i + (k : ZMod 14) := by ring
        show chi ((k : ZMod 14) * (i + -1)) + chi ((k : ZMod 14) * (i + 1)) = _
        rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add,
          add_comm (chi (-(k : ZMod 14))) (chi (k : ZMod 14)), chi_add_chi_neg, hKval, mul_comm]
      funext i
      exact key i

end Chem

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

