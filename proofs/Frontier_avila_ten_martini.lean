import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ)` on which the almost Mathieu operator acts. -/
abbrev HilbertZ : Type := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial HilbertZ := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have := congrArg (fun f : HilbertZ => (f : ℤ → ℂ) 0) h
  simp at this

theorem summable_sq (f : HilbertZ) : Summable fun n : ℤ => ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ) := by
  have := (lp.memℓp f).summable (p := 2) (by norm_num)
  simpa using this

/-! ## Shift operators -/

theorem memℓp_shift (k : ℤ) (f : HilbertZ) :
    Memℓp (fun n : ℤ => (f : ℤ → ℂ) (n + k)) 2 := by
  refine memℓp_gen ?_
  have h := summable_sq f
  have := (Equiv.addRight k).summable_iff (f := fun n : ℤ => ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ))
  simpa using this.mpr h

/-- Translation of a sequence in `ℓ²(ℤ)`. -/
noncomputable def shiftFn (k : ℤ) (f : HilbertZ) : HilbertZ :=
  ⟨fun n => (f : ℤ → ℂ) (n + k), memℓp_shift k f⟩

@[simp] theorem shiftFn_apply (k : ℤ) (f : HilbertZ) (n : ℤ) :
    (shiftFn k f : ℤ → ℂ) n = (f : ℤ → ℂ) (n + k) := rfl

theorem norm_shiftFn (k : ℤ) (f : HilbertZ) : ‖shiftFn k f‖ = ‖f‖ := by
  have h2 : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow h2, lp.norm_eq_tsum_rpow h2]
  congr 1
  exact (Equiv.addRight k).tsum_eq (fun n : ℤ => ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal)

/-- Translation as a bounded operator on `ℓ²(ℤ)`. -/
noncomputable def shift (k : ℤ) : HilbertZ →L[ℂ] HilbertZ :=
  LinearMap.mkContinuous
    { toFun := shiftFn k
      map_add' := by intro f g; ext n; simp [shiftFn]
      map_smul' := by intro c f; ext n; simp [shiftFn] }
    1 (by intro f; simp [norm_shiftFn])

@[simp] theorem shift_apply (k : ℤ) (f : HilbertZ) (n : ℤ) :
    ((shift k f : HilbertZ) : ℤ → ℂ) n = (f : ℤ → ℂ) (n + k) := rfl

/-! ## Multiplication by a bounded real potential -/

theorem memℓp_mul (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : HilbertZ) :
    Memℓp (fun n : ℤ => (v n : ℂ) * (f : ℤ → ℂ) n) 2 := by
  refine memℓp_gen ?_
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((summable_sq f).mul_left (C ^ (2:ℝ))))
  have h1 : ‖(v n : ℂ) * (f : ℤ → ℂ) n‖ = |v n| * ‖(f : ℤ → ℂ) n‖ := by
    simp [norm_mul, Complex.norm_real]
  have h2 : ‖(v n : ℂ) * (f : ℤ → ℂ) n‖ ≤ C * ‖(f : ℤ → ℂ) n‖ := by
    rw [h1]; exact mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _)
  calc ‖(v n : ℂ) * (f : ℤ → ℂ) n‖ ^ ((2:ℝ≥0∞).toReal)
      ≤ (C * ‖(f : ℤ → ℂ) n‖) ^ ((2:ℝ≥0∞).toReal) := by
        apply Real.rpow_le_rpow (norm_nonneg _) h2 (by norm_num)
    _ = C ^ (2:ℝ) * ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) := by
        rw [Real.mul_rpow hC (norm_nonneg _)]; norm_num
  
/-- Multiplication by a bounded real-valued potential, as a map on `ℓ²(ℤ)`. -/
noncomputable def mulFn (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : HilbertZ) : HilbertZ :=
  ⟨fun n => (v n : ℂ) * (f : ℤ → ℂ) n, memℓp_mul v C hv f⟩

@[simp] theorem mulFn_apply (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : HilbertZ) (n : ℤ) :
    (mulFn v C hv f : ℤ → ℂ) n = (v n : ℂ) * (f : ℤ → ℂ) n := rfl

theorem norm_mulFn_le (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : HilbertZ) :
    ‖mulFn v C hv f‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  have h2 : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le h2 (by positivity) ?_
  have hle : ∀ n : ℤ, ‖(mulFn v C hv f : ℤ → ℂ) n‖ ^ ((2:ℝ≥0∞).toReal)
      ≤ C ^ (2:ℝ) * ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) := by
    intro n
    have h1 : ‖(mulFn v C hv f : ℤ → ℂ) n‖ ≤ C * ‖(f : ℤ → ℂ) n‖ := by
      simp only [mulFn_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _)
    calc ‖(mulFn v C hv f : ℤ → ℂ) n‖ ^ ((2:ℝ≥0∞).toReal)
        ≤ (C * ‖(f : ℤ → ℂ) n‖) ^ ((2:ℝ≥0∞).toReal) :=
          Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num)
      _ = C ^ (2:ℝ) * ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) := by
          rw [Real.mul_rpow hC (norm_nonneg _)]; norm_num
  have hsum : ∑' n : ℤ, ‖(mulFn v C hv f : ℤ → ℂ) n‖ ^ ((2:ℝ≥0∞).toReal)
      ≤ ∑' n : ℤ, C ^ (2:ℝ) * ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) := by
    refine Summable.tsum_le_tsum hle ?_ ((summable_sq f).mul_left _)
    have := (lp.memℓp (mulFn v C hv f)).summable (p := 2) (by norm_num)
    simpa using this
  refine hsum.trans ?_
  rw [tsum_mul_left]
  have : ∑' n : ℤ, ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) = ‖f‖ ^ (2:ℝ) := by
    have := lp.norm_rpow_eq_tsum (p := 2) h2 f
    simpa using this.symm
  rw [this, ← Real.mul_rpow hC (norm_nonneg _)]
  norm_num

/-- Multiplication by a bounded real-valued potential, as a bounded operator on `ℓ²(ℤ)`. -/
noncomputable def mulOp (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : HilbertZ →L[ℂ] HilbertZ :=
  LinearMap.mkContinuous
    { toFun := mulFn v C hv
      map_add' := by intro f g; ext n; simp [mulFn, mul_add]
      map_smul' := by intro c f; ext n; simp [mulFn]; ring }
    C (fun f => norm_mulFn_le v C hv f)

@[simp] theorem mulOp_apply (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : HilbertZ) (n : ℤ) :
    ((mulOp v C hv f : HilbertZ) : ℤ → ℂ) n = (v n : ℂ) * (f : ℤ → ℂ) n := rfl

end Frontier

