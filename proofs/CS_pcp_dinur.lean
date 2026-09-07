import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

variable {Inst : Type*}

/-- **Amplification along iterations.**  If one application of the transformation `T`
doubles the unsatisfiability value (until it reaches the target `gap`), then `k`
applications multiply it by `2 ^ k` (until it reaches `gap`). -/
theorem unsat_iterate_ge (unsat : Inst → ℝ) (T : Inst → Inst) (gap : ℝ)
    (hgap : 0 ≤ gap)
    (hamp : ∀ G : Inst, min (2 * unsat G) gap ≤ unsat (T G)) :
    ∀ (k : ℕ) (G : Inst), min (2 ^ k * unsat G) gap ≤ unsat (T^[k] G) := by
  intro k
  induction k with
  | zero => intro G; simp
  | succ k ih =>
    intro G
    have h1 : min (2 ^ k * unsat G) gap ≤ unsat (T^[k] G) := ih G
    have h2 : min (2 * unsat (T^[k] G)) gap ≤ unsat (T (T^[k] G)) := hamp _
    rw [Function.iterate_succ_apply']
    refine le_trans (le_min ?_ (min_le_right _ _)) h2
    rcases le_total (2 ^ k * unsat G) gap with h | h
    · have : min (2 ^ k * unsat G) gap = 2 ^ k * unsat G := min_eq_left h
      rw [this] at h1
      have hk : (2 : ℝ) ^ (k + 1) * unsat G = 2 * (2 ^ k * unsat G) := by ring
      calc min ((2 : ℝ) ^ (k + 1) * unsat G) gap ≤ 2 ^ (k + 1) * unsat G := min_le_left _ _
        _ = 2 * (2 ^ k * unsat G) := hk
        _ ≤ 2 * unsat (T^[k] G) := by linarith
    · have : min (2 ^ k * unsat G) gap = gap := min_eq_right h
      rw [this] at h1
      calc min ((2 : ℝ) ^ (k + 1) * unsat G) gap ≤ gap := min_le_right _ _
        _ ≤ 2 * unsat (T^[k] G) := by linarith

/-- Perfect satisfiability (`unsat = 0`) is preserved by iterating `T`. -/
theorem unsat_iterate_eq_zero (unsat : Inst → ℝ) (T : Inst → Inst)
    (hcomplete : ∀ G : Inst, unsat G = 0 → unsat (T G) = 0) :
    ∀ (k : ℕ) (G : Inst), unsat G = 0 → unsat (T^[k] G) = 0 := by
  intro k
  induction k with
  | zero => intro G hG; simpa using hG
  | succ k ih =>
    intro G hG
    rw [Function.iterate_succ_apply']
    exact hcomplete _ (ih G hG)

/-- The size blow-up of `k` iterations of `T` is at most `C ^ k`. -/
theorem size_iterate_le (size : Inst → ℕ) (T : Inst → Inst) (C : ℕ)
    (hsize : ∀ G : Inst, size (T G) ≤ C * size G) :
    ∀ (k : ℕ) (G : Inst), size (T^[k] G) ≤ C ^ k * size G := by
  intro k
  induction k with
  | zero => intro G; simp
  | succ k ih =>
    intro G
    rw [Function.iterate_succ_apply']
    calc size (T (T^[k] G)) ≤ C * size (T^[k] G) := hsize _
      _ ≤ C * (C ^ k * size G) := by
          exact Nat.mul_le_mul_left C (ih G)
      _ = C ^ (k + 1) * size G := by ring

/-- **Dinur's gap amplification (statement), iterated form.**

This is the combinatorial core of Dinur's proof of the PCP theorem, phrased over an
abstract type `Inst` of constraint-satisfaction instances equipped with

* a size function `size : Inst → ℕ` (the number of constraints), and
* an unsatisfiability value `unsat : Inst → ℝ` (the least fraction of constraints
  violated by any assignment),

together with a *gap-amplification step* `T : Inst → Inst` satisfying Dinur's three
requirements:

* `hsize`  : linear size blow-up, `size (T G) ≤ C * size G`;
* `hcomplete` : completeness, satisfiable instances are mapped to satisfiable instances;
* `hamp`   : soundness/amplification, `min (2 * unsat G) gap ≤ unsat (T G)`;

and the normalisation `hfrac`: a nonzero unsatisfiability value is at least one over
the number of constraints.

The conclusion is the PCP-style gap reduction obtained by iterating `T`: there are
`k = O(log (size G))` rounds producing an instance `H` of size at most
`C ^ k * size G` (hence polynomial in `size G`) which is satisfiable if `G` is, and
otherwise has unsatisfiability value at least the absolute constant `gap`. -/
theorem pcp_dinur (size : Inst → ℕ) (unsat : Inst → ℝ) (T : Inst → Inst)
    (C : ℕ) (gap : ℝ) (hgap0 : 0 < gap)
    (hsize : ∀ G : Inst, size (T G) ≤ C * size G)
    (hcomplete : ∀ G : Inst, unsat G = 0 → unsat (T G) = 0)
    (hamp : ∀ G : Inst, min (2 * unsat G) gap ≤ unsat (T G))
    (hfrac : ∀ G : Inst, 0 < size G → 0 < unsat G → 1 / (size G : ℝ) ≤ unsat G)
    (G : Inst) (hG : 0 < size G) :
    ∃ (k : ℕ) (H : Inst),
      (2 : ℝ) ^ k ≤ 2 * (gap + 1) * (size G : ℝ) ∧
      size H ≤ C ^ k * size G ∧
      (unsat G = 0 → unsat H = 0) ∧
      (0 < unsat G → gap ≤ unsat H) := by
  set n : ℕ := size G with hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hG
  set m : ℕ := ⌈gap * (n : ℝ)⌉₊ with hm
  set k : ℕ := Nat.clog 2 m with hk
  refine ⟨k, T^[k] G, ?_, size_iterate_le size T C hsize k G, ?_, ?_⟩
  · -- the number of rounds is logarithmic
    rcases le_or_gt m 1 with hm1 | hm1
    · have : k = 0 := by
        rw [hk]
        exact Nat.clog_of_right_le_one hm1 2
      rw [this]
      have : (0 : ℝ) < gap + 1 := by linarith
      nlinarith
    · have hlt : 2 ^ (k - 1) < m := Nat.pow_pred_clog_lt_self (by norm_num) hm1
      have hk1 : 1 ≤ k := by
        rw [hk]
        exact Nat.clog_pos (by norm_num) hm1
      have hpow : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        ring
      have h1 : (2 : ℕ) ^ k ≤ 2 * m := by omega
      have h2 : (2 : ℝ) ^ k ≤ 2 * (m : ℝ) := by exact_mod_cast h1
      have h3 : (m : ℝ) ≤ gap * (n : ℝ) + 1 := by
        have := Nat.ceil_lt_add_one (a := gap * (n : ℝ)) (by positivity)
        linarith
      nlinarith
  · exact unsat_iterate_eq_zero unsat T hcomplete k G
  · intro hpos
    have hmain : min (2 ^ k * unsat G) gap ≤ unsat (T^[k] G) :=
      unsat_iterate_ge unsat T gap hgap0.le hamp k G
    have hlow : 1 / (n : ℝ) ≤ unsat G := hfrac G hG hpos
    have hpk : gap * (n : ℝ) ≤ (2 : ℝ) ^ k := by
      have h1 : m ≤ 2 ^ k := by
        rw [hk]
        exact Nat.le_pow_clog (by norm_num) m
      have h2 : (m : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast h1
      exact le_trans (Nat.le_ceil _) h2
    have hge : gap ≤ 2 ^ k * unsat G := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have : (2 : ℝ) ^ k * (1 / (n : ℝ)) ≤ 2 ^ k * unsat G := by
        have : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
        nlinarith
      have hgn : gap ≤ (2 : ℝ) ^ k * (1 / (n : ℝ)) := by
        rw [mul_one_div, le_div_iff₀ hnpos]
        exact hpk
      linarith
    have : min ((2 : ℝ) ^ k * unsat G) gap = gap := min_eq_right hge
    rw [this] at hmain
    exact hmain

end CS

#print axioms CS.pcp_dinur

