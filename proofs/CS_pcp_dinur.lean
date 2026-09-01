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

/-!
## Dinur's gap amplification

We formalise the combinatorial engine of Dinur's proof of the PCP theorem.

A *constraint system* is modelled abstractly by a type `Inst` of instances equipped with

* a size function `size : Inst → ℕ` (the number of constraints), and
* an *unsat value* `unsat : Inst → ℚ`, the minimum, over all assignments, of the
  fraction of constraints that are violated.  In particular `unsat I = 0` says that
  `I` is satisfiable.

Dinur's **Main Lemma** (proved via preprocessing / expanderisation, graph powering and
composition with an assignment tester) produces a polynomial-time map `amp : Inst → Inst`
over a *fixed* alphabet, together with constants `C ≥ 1` and `0 < alpha ≤ 1`, satisfying

* `size (amp I) ≤ C * size I`            (linear blow-up),
* `unsat I = 0 → unsat (amp I) = 0`      (completeness),
* `min alpha (2 * unsat I) ≤ unsat (amp I)` (the gap doubles, until it reaches `alpha`).

The content of the theorem `CS.pcp_dinur` below is the second half of Dinur's argument:
iterating the Main Lemma logarithmically many times turns *any* nonzero gap — in
particular the trivial gap `1/m` enjoyed by an unsatisfiable instance with `m`
constraints — into the *constant* gap `alpha`, while keeping the size polynomial.
This is exactly the gap-amplification reduction underlying the PCP theorem: the map
`amp^[⌈log₂ m⌉]` sends satisfiable instances to satisfiable instances and unsatisfiable
instances to instances with `unsat ≥ alpha`.
-/

section Amplification

variable {Inst : Type*} (size : Inst → ℕ) (unsat : Inst → ℚ) (amp : Inst → Inst)
  (C : ℕ) (alpha : ℚ)

/-- Iterating the size bound of the Main Lemma. -/
theorem size_iterate_le (hsize : ∀ I : Inst, size (amp I) ≤ C * size I) (I : Inst) (k : ℕ) :
    size (amp^[k] I) ≤ C ^ k * size I := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc size (amp (amp^[k] I)) ≤ C * size (amp^[k] I) := hsize _
        _ ≤ C * (C ^ k * size I) := Nat.mul_le_mul_left _ ih
        _ = C ^ (k + 1) * size I := by ring

/-- Iterating completeness of the Main Lemma: satisfiable instances stay satisfiable. -/
theorem unsat_iterate_eq_zero (hcomplete : ∀ I : Inst, unsat I = 0 → unsat (amp I) = 0)
    (I : Inst) (hI : unsat I = 0) (k : ℕ) : unsat (amp^[k] I) = 0 := by
  induction k with
  | zero => simpa using hI
  | succ k ih => rw [Function.iterate_succ_apply']; exact hcomplete _ ih

/-- Iterating the gap amplification step: after `k` rounds the gap has been multiplied by
`2 ^ k`, unless it has already saturated at `alpha`. -/
theorem le_unsat_iterate (halpha0 : 0 < alpha)
    (hgap : ∀ I : Inst, min alpha (2 * unsat I) ≤ unsat (amp I)) (I : Inst) (k : ℕ) :
    min alpha (2 ^ k * unsat I) ≤ unsat (amp^[k] I) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ (hgap (amp^[k] I))
      have h2 : (2 : ℚ) * min alpha (2 ^ k * unsat I) ≤ 2 * unsat (amp^[k] I) := by linarith
      rcases min_cases alpha (2 ^ k * unsat I) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at h2
        have hle : alpha ≤ 2 * unsat (amp^[k] I) := by linarith
        exact le_trans (min_le_left _ _) (le_min le_rfl hle)
      · rw [he] at h2
        have : (2 : ℚ) ^ (k + 1) * unsat I ≤ 2 * unsat (amp^[k] I) := by
          calc (2 : ℚ) ^ (k + 1) * unsat I = 2 * (2 ^ k * unsat I) := by ring
            _ ≤ 2 * unsat (amp^[k] I) := h2
        exact min_le_min le_rfl this

end Amplification

/--
**Dinur's gap amplification (the PCP theorem via gap amplification).**

Assume the conclusion of Dinur's Main Lemma: a size-linear, complete, gap-doubling
transformation `amp` of constraint systems over a fixed alphabet, with constants
`C ≥ 1` and `0 < alpha ≤ 1`.  Let `I` be an instance with at most `m` constraints
(`m ≥ 1`), so that its unsat value is either `0` (satisfiable) or at least `1/m`
(at least one of the at most `m` constraints is violated).

Then, after `k = ⌈log₂ m⌉` iterations of `amp`:

* the size stays polynomially bounded: `size (amp^[k] I) ≤ C ^ k * m`;
* satisfiable instances remain satisfiable (perfect completeness);
* unsatisfiable instances acquire the *constant* gap `alpha`.

Hence `I ↦ amp^[⌈log₂ m⌉] I` is a gap-creating reduction with constant soundness gap,
which is precisely the reduction yielding the PCP theorem.
-/
theorem pcp_dinur
    {Inst : Type*} (size : Inst → ℕ) (unsat : Inst → ℚ) (amp : Inst → Inst)
    (C : ℕ) (alpha : ℚ)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hsize : ∀ I : Inst, size (amp I) ≤ C * size I)
    (hcomplete : ∀ I : Inst, unsat I = 0 → unsat (amp I) = 0)
    (hgap : ∀ I : Inst, min alpha (2 * unsat I) ≤ unsat (amp I))
    (I : Inst) (m : ℕ) (hm : 0 < m) (hIm : size I ≤ m)
    (htrivial : unsat I = 0 ∨ (1 : ℚ) / m ≤ unsat I) :
    size (amp^[Nat.clog 2 m] I) ≤ C ^ (Nat.clog 2 m) * m ∧
      (unsat I = 0 → unsat (amp^[Nat.clog 2 m] I) = 0) ∧
      (unsat I ≠ 0 → alpha ≤ unsat (amp^[Nat.clog 2 m] I)) := by
  set k : ℕ := Nat.clog 2 m with hk
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (size_iterate_le size amp C hsize I k)
      (Nat.mul_le_mul_left _ hIm)
  · intro h0
    exact unsat_iterate_eq_zero unsat amp hcomplete I h0 k
  · intro hne
    have hlow : (1 : ℚ) / m ≤ unsat I := by
      rcases htrivial with h | h
      · exact absurd h hne
      · exact h
    have hmk : (m : ℚ) ≤ 2 ^ k := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) m
    have hmpos : (0 : ℚ) < m := by exact_mod_cast hm
    have hone : (1 : ℚ) ≤ 2 ^ k * unsat I := by
      have h1 : (2 : ℚ) ^ k * (1 / m) ≤ 2 ^ k * unsat I := by
        have : (0 : ℚ) < 2 ^ k := by positivity
        exact mul_le_mul_of_nonneg_left hlow (le_of_lt this)
      have h2 : (1 : ℚ) ≤ 2 ^ k * (1 / m) := by
        rw [mul_one_div, le_div_iff₀ hmpos]
        simpa using hmk
      linarith
    have := le_unsat_iterate unsat amp alpha halpha0 hgap I k
    have hmin : alpha ≤ min alpha (2 ^ k * unsat I) := by
      refine le_min le_rfl ?_
      linarith
    linarith

end CS

