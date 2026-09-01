import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace QI

variable {N M : ℕ}

/-- The state space of a quantum query algorithm searching a database of size `N`:
an index register `Fin N` together with an arbitrary finite workspace `Fin M`. -/
abbrev State (N M : ℕ) : Type := EuclideanSpace ℂ (Fin N × Fin M)

/-- The standard phase oracle marking the index `i`: it flips the sign of every
amplitude whose index register holds `i`, and does nothing otherwise. -/
def oracle (i : Fin N) (psi : State N M) : State N M :=
  WithLp.toLp 2 (fun jw => if jw.1 = i then -psi jw else psi jw)

@[simp] lemma oracle_apply (i : Fin N) (psi : State N M) (jw : Fin N × Fin M) :
    oracle i psi jw = if jw.1 = i then -psi jw else psi jw := by
  simp [oracle]

lemma oracle_sub (i : Fin N) (psi phi : State N M) :
    oracle i (psi - phi) = oracle i psi - oracle i phi := by
  ext jw
  by_cases h : jw.1 = i
  · simp [h]; ring
  · simp [h]

lemma oracle_norm (i : Fin N) (psi : State N M) : ‖oracle i psi‖ = ‖psi‖ := by
  have h : ‖oracle i psi‖ ^ 2 = ‖psi‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun jw _ => ?_
    by_cases h : jw.1 = i <;> simp [h]
  calc ‖oracle i psi‖ = √(‖oracle i psi‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(‖psi‖ ^ 2) := by rw [h]
    _ = ‖psi‖ := Real.sqrt_sq (norm_nonneg _)

lemma oracle_dist (i : Fin N) (psi phi : State N M) :
    ‖oracle i psi - oracle i phi‖ = ‖psi - phi‖ := by
  rw [← oracle_sub, oracle_norm]

/-- The squared norm of the part of `psi` whose index register holds `i`. -/
noncomputable def markSq (i : Fin N) (psi : State N M) : ℝ := ∑ w : Fin M, ‖psi (i, w)‖ ^ 2

lemma sum_markSq (psi : State N M) : ∑ i : Fin N, markSq i psi = ‖psi‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- A query to the oracle for `i` disturbs `psi` by exactly twice the amplitude that
`psi` places on the index `i`. -/
lemma norm_oracle_sub_self_sq (i : Fin N) (psi : State N M) :
    ‖oracle i psi - psi‖ ^ 2 = 4 * markSq i psi := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp only [markSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have : (oracle i psi - psi) (i, w) = -(2 * psi (i, w)) := by
      simp; ring
    rw [this]
    rw [norm_neg, norm_mul, mul_pow]
    norm_num
  · intro j _ hj
    refine Finset.sum_eq_zero fun w _ => ?_
    have : (oracle i psi - psi) (j, w) = 0 := by simp [hj]
    rw [this]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The state of the algorithm after `t` queries: the unitaries `U 0, U 1, …` are
arbitrary (they encode the whole algorithm) and `O` is the oracle being queried. -/
def run (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M)) (psi0 : State N M)
    (O : State N M → State N M) : ℕ → State N M
  | 0 => psi0
  | t + 1 => U t (O (run U psi0 O t))

@[simp] lemma run_zero (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M)) (psi0 : State N M)
    (O : State N M → State N M) : run U psi0 O 0 = psi0 := rfl

@[simp] lemma run_succ (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M)) (psi0 : State N M)
    (O : State N M → State N M) (t : ℕ) :
    run U psi0 O (t + 1) = U t (O (run U psi0 O t)) := rfl

lemma norm_run_id (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M)) (psi0 : State N M) (t : ℕ) :
    ‖run U psi0 id t‖ = ‖psi0‖ := by
  induction t with
  | zero => simp
  | succ t ih => simpa using ih

/-- **Hybrid argument** (Bennett–Bernstein–Brassard–Vazirani): after `T` queries, the
state produced with the oracle for `i` differs from the state produced with no oracle
at all by at most the total disturbance the oracle for `i` would cause along the
undisturbed trajectory. -/
lemma hybrid (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M)) (psi0 : State N M) (i : Fin N)
    (T : ℕ) :
    ‖run U psi0 (oracle i) T - run U psi0 id T‖
      ≤ ∑ t ∈ Finset.range T, ‖oracle i (run U psi0 id t) - run U psi0 id t‖ := by
  induction T with
  | zero => simp
  | succ T ih =>
    set a := run U psi0 (oracle i) T with ha
    set b := run U psi0 id T with hb
    have hstep : run U psi0 (oracle i) (T + 1) - run U psi0 id (T + 1)
        = U T (oracle i a - b) := by
      simp [← ha, ← hb, map_sub]
    rw [hstep, LinearIsometryEquiv.norm_map, Finset.sum_range_succ]
    calc ‖oracle i a - b‖
        ≤ ‖oracle i a - oracle i b‖ + ‖oracle i b - b‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub (oracle i a) (oracle i b) b
      _ = ‖a - b‖ + ‖oracle i b - b‖ := by rw [oracle_dist]
      _ ≤ (∑ t ∈ Finset.range T, ‖oracle i (run U psi0 id t) - run U psi0 id t‖)
            + ‖oracle i b - b‖ := by gcongr

/-- **Optimality of Grover search (BBBV lower bound).**

`U` is an arbitrary quantum query algorithm on an index register `Fin N` and a workspace
`Fin M`: it starts in the unit vector `psi0` and alternates a query to the oracle with an
arbitrary unitary, `T` times in total. `oracle i` is the phase oracle for the marked item
`i`, and `run U psi0 id T` is the final state of the same algorithm run with no marked
item at all.

If the algorithm can tell *every* marked item `i` apart from the unmarked database — i.e.
the two final states are at distance at least `c` for every `i`, which is what a bounded
error probability of success forces, with `c` a positive constant — then

  `T ≥ (c/2) * √N`,

so `Ω(√N)` queries are necessary and Grover's algorithm is optimal up to a constant. -/
theorem grover_optimal {N M T : ℕ} (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M))
    (psi0 : State N M) (hpsi0 : ‖psi0‖ = 1) (c : ℝ) (hc : 0 ≤ c)
    (hdist : ∀ i : Fin N, c ≤ ‖run U psi0 (oracle i) T - run U psi0 id T‖) :
    c / 2 * √N ≤ T := by
  set psi : ℕ → State N M := fun t => run U psi0 id t with hpsi
  set d : Fin N → ℕ → ℝ := fun i t => ‖oracle i (psi t) - psi t‖ with hd
  -- Step 1: each marked item is reached only through a large total disturbance.
  have step1 : ∀ i : Fin N, c ≤ ∑ t ∈ Finset.range T, d i t := fun i =>
    le_trans (hdist i) (hybrid U psi0 i T)
  -- Step 2: at each step the total disturbance over all indices is exactly `4`.
  have step2 : ∀ t : ℕ, ∑ i : Fin N, (d i t) ^ 2 = 4 := by
    intro t
    have : ∑ i : Fin N, (d i t) ^ 2 = 4 * ∑ i : Fin N, markSq i (psi t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => norm_oracle_sub_self_sq i (psi t)
    rw [this, sum_markSq, hpsi, norm_run_id, hpsi0]
    norm_num
  -- Step 3: Cauchy-Schwarz plus the counting bound.
  have step3 : (N : ℝ) * c ^ 2 ≤ 4 * (T : ℝ) ^ 2 := by
    have h1 : (N : ℝ) * c ^ 2 ≤ ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2 := by
      have : ∀ i : Fin N, c ^ 2 ≤ (∑ t ∈ Finset.range T, d i t) ^ 2 := fun i =>
        pow_le_pow_left₀ hc (step1 i) 2
      calc (N : ℝ) * c ^ 2 = ∑ _i : Fin N, c ^ 2 := by
            simp [Finset.sum_const]
        _ ≤ ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2 :=
            Finset.sum_le_sum fun i _ => this i

    have h2 : ∀ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2
        ≤ (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2 := by
      intro i
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range T) (f := fun t => d i t)
    have h3 : ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2
        ≤ ∑ i : Fin N, (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2 :=
      Finset.sum_le_sum fun i _ => h2 i
    have h4 : ∑ i : Fin N, (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2
        = (T : ℝ) * ∑ t ∈ Finset.range T, ∑ i : Fin N, (d i t) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    have h5 : ∑ t ∈ Finset.range T, ∑ i : Fin N, (d i t) ^ 2 = 4 * (T : ℝ) := by
      rw [Finset.sum_congr rfl fun t _ => step2 t]
      simp [mul_comm]
    calc (N : ℝ) * c ^ 2
        ≤ ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2 := h1
      _ ≤ ∑ i : Fin N, (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2 := h3
      _ = (T : ℝ) * ∑ t ∈ Finset.range T, ∑ i : Fin N, (d i t) ^ 2 := h4
      _ = (T : ℝ) * (4 * (T : ℝ)) := by rw [h5]
      _ = 4 * (T : ℝ) ^ 2 := by ring
  -- Step 4: conclude.
  have hsq : (√N) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : (0 : ℝ) ≤ √N := Real.sqrt_nonneg _
  have hT : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  nlinarith [step3, hsq, hs0, hT, hc, sq_nonneg (c * √N - 2 * T)]

/-- Specialisation: an algorithm whose final states for the marked databases are at
distance at least `1` from the final state for the unmarked database must make at least
`√N / 2` queries. -/
theorem grover_optimal_one {N M T : ℕ} (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M))
    (psi0 : State N M) (hpsi0 : ‖psi0‖ = 1)
    (hdist : ∀ i : Fin N, 1 ≤ ‖run U psi0 (oracle i) T - run U psi0 id T‖) :
    √N / 2 ≤ T := by
  have := grover_optimal U psi0 hpsi0 1 zero_le_one hdist
  linarith [this]

/-- The hypotheses of `grover_optimal` are satisfiable, so the statement is not vacuous:
on a one-element database a single query already separates the marked oracle from the
unmarked one by the maximal distance `2`, and the bound `T ≥ (c/2)·√N` is then tight
(`(2/2)·√1 = 1 ≤ 1`). -/
theorem grover_hypotheses_satisfiable :
    ∃ (U : ℕ → (State 1 1 ≃ₗᵢ[ℂ] State 1 1)) (psi0 : State 1 1),
      ‖psi0‖ = 1 ∧
      ∀ i : Fin 1, (2 : ℝ) ≤ ‖run U psi0 (oracle i) 1 - run U psi0 id 1‖ := by
  refine ⟨fun _ => LinearIsometryEquiv.refl ℂ (State 1 1), WithLp.toLp 2 (fun _ => 1), ?_, ?_⟩
  · rw [show ‖(WithLp.toLp 2 (fun _ => 1) : State 1 1)‖
        = √(‖(WithLp.toLp 2 (fun _ => 1) : State 1 1)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm, EuclideanSpace.norm_sq_eq]
    simp
  · intro i
    have hall : ∀ x : Fin 1 × Fin 1, x.1 = i := fun x => Subsingleton.elim _ _
    have hsq : ‖run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) (oracle i) 1
        - run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) id 1‖ ^ 2 = 4 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [run, hall]
      norm_num
    nlinarith [norm_nonneg (run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) (oracle i) 1
        - run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) id 1)]

end QI

