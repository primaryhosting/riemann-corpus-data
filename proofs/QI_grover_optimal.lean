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

namespace QI

/-- The Hilbert space of a quantum query algorithm searching a database of `N` items:
the index register `Fin N` together with an arbitrary workspace register `K`. -/
abbrev HSpace (N : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Fin N => K)

variable {N : ℕ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The (phase) query operator for the database whose unique marked item is `x`:
it flips the sign of the component of the index register at `x`. -/
noncomputable def phaseOracle (x : Fin N) (psi : HSpace N K) : HSpace N K :=
  WithLp.toLp 2 (fun y => if y = x then -(psi y) else psi y)

@[simp] lemma phaseOracle_apply (x y : Fin N) (psi : HSpace N K) :
    (phaseOracle x psi) y = if y = x then -(psi y) else psi y := rfl

/-- The state of a quantum query algorithm after `t` queries: it starts in `psi0`, and each
step consists of one oracle call followed by an (input independent) unitary. -/
noncomputable def run (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (O : HSpace N K → HSpace N K)
    (psi0 : HSpace N K) : ℕ → HSpace N K
  | 0 => psi0
  | (t + 1) => U t (O (run U O psi0 t))

@[simp] lemma run_zero (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (O : HSpace N K → HSpace N K)
    (psi0 : HSpace N K) : run U O psi0 0 = psi0 := rfl

@[simp] lemma run_succ (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (O : HSpace N K → HSpace N K)
    (psi0 : HSpace N K) (t : ℕ) :
    run U O psi0 (t + 1) = U t (O (run U O psi0 t)) := rfl

/-- The oracle is additive on differences. -/
lemma phaseOracle_sub (x : Fin N) (psi phi : HSpace N K) :
    phaseOracle x psi - phaseOracle x phi = phaseOracle x (psi - phi) := by
  ext y
  simp only [phaseOracle_apply, PiLp.sub_apply]
  split <;> abel

/-- The oracle is norm preserving. -/
lemma phaseOracle_norm (x : Fin N) (psi : HSpace N K) :
    ‖phaseOracle x psi‖ = ‖psi‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  show ‖(phaseOracle x psi) y‖ ^ 2 = ‖psi y‖ ^ 2
  simp only [phaseOracle_apply]
  split <;> simp

/-- The query magnitude: applying the oracle changes the state by exactly twice the norm of
the amplitude sitting on the marked index. -/
lemma norm_phaseOracle_sub_self (x : Fin N) (psi : HSpace N K) :
    ‖phaseOracle x psi - psi‖ = 2 * ‖psi x‖ := by
  rw [PiLp.norm_eq_of_L2]
  have key : ∀ y : Fin N, ‖(phaseOracle x psi - psi).ofLp y‖ ^ 2
      = if y = x then (2 * ‖psi x‖) ^ 2 else 0 := by
    intro y
    show ‖(phaseOracle x psi) y - psi y‖ ^ 2 = _
    simp only [phaseOracle_apply]
    split <;> rename_i h
    · subst h
      rw [show -(psi y) - psi y = (-2 : ℝ) • psi y by module, norm_smul]
      simp [mul_pow]
    · simp
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_ite_eq' Finset.univ x]
  simp [Real.sqrt_sq]

/-- Cauchy–Schwarz: the sum of the index-register component norms is at most `√N ‖ψ‖`. -/
lemma sum_norm_apply_le (psi : HSpace N K) :
    ∑ x : Fin N, ‖psi x‖ ≤ Real.sqrt N * ‖psi‖ := by
  have hsq : ‖psi‖ ^ 2 = ∑ x : Fin N, ‖psi x‖ ^ 2 := by
    rw [PiLp.norm_eq_of_L2, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => by positivity
  have h2 : (0 : ℝ) ≤ ∑ x : Fin N, ‖psi x‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have h1 : (∑ x : Fin N, ‖psi x‖) ^ 2 ≤ (N : ℝ) * ‖psi‖ ^ 2 := by
    rw [hsq]
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun x => ‖psi x‖)
  calc ∑ x : Fin N, ‖psi x‖ = Real.sqrt ((∑ x : Fin N, ‖psi x‖) ^ 2) := (Real.sqrt_sq h2).symm
    _ ≤ Real.sqrt ((N : ℝ) * ‖psi‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt N * ‖psi‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq (norm_nonneg _)]

/-- The state of the oracle-free run keeps the norm of the initial state. -/
lemma norm_run_id (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (psi0 : HSpace N K) (t : ℕ) :
    ‖run U id psi0 t‖ = ‖psi0‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ]; simpa using ih

/-- The BBBV hybrid argument: the run with oracle `x` and the oracle-free run differ by at
most twice the total query magnitude on index `x` along the oracle-free run. -/
lemma hybrid_bound (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (psi0 : HSpace N K) (x : Fin N)
    (t : ℕ) :
    ‖run U (phaseOracle x) psi0 t - run U id psi0 t‖ ≤
      2 * ∑ s ∈ Finset.range t, ‖(run U id psi0 s) x‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
      set f := run U (phaseOracle x) psi0 t with hf
      set g := run U id psi0 t with hg
      have hstep : ‖run U (phaseOracle x) psi0 (t + 1) - run U id psi0 (t + 1)‖
          = ‖phaseOracle x f - g‖ := by
        rw [run_succ, run_succ]
        show ‖U t (phaseOracle x f) - U t (id g)‖ = _
        simp only [id_eq, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      have htri : ‖phaseOracle x f - g‖
          ≤ ‖phaseOracle x f - phaseOracle x g‖ + ‖phaseOracle x g - g‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h1 : ‖phaseOracle x f - phaseOracle x g‖ = ‖f - g‖ := by
        rw [phaseOracle_sub, phaseOracle_norm]
      have h2 : ‖phaseOracle x g - g‖ = 2 * ‖g x‖ := norm_phaseOracle_sub_self x g
      rw [Finset.sum_range_succ]
      rw [hstep]
      rw [h1, h2] at htri
      linarith [htri, ih]

/-- **Optimality of Grover search (BBBV lower bound).**

Any quantum query algorithm which, for every marked item `x` of a database of size `N`,
finds `x` with probability at least `2/3` (i.e. the index register of its final state has
squared amplitude at least `2/3` on `x`) must use at least `(√(2N/3) - 1)/2` queries.
In particular the number of queries is `Ω(√N)`, so Grover's `O(√N)` algorithm is optimal. -/
theorem grover_optimal (T : ℕ) (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (psi0 : HSpace N K)
    (hpsi0 : ‖psi0‖ = 1)
    (hsucc : ∀ x : Fin N, (2 : ℝ) / 3 ≤ ‖(run U (phaseOracle x) psi0 T) x‖ ^ 2) :
    (Real.sqrt (2 * N / 3) - 1) / 2 ≤ (T : ℝ) := by
  set g := run U id psi0 with hg
  set f := fun x : Fin N => run U (phaseOracle x) psi0 with hfdef
  -- Upper bound on the total distinguishability.
  have hupper : ∑ x : Fin N, ‖f x T - g T‖ ≤ 2 * T * Real.sqrt N := by
    have step1 : ∑ x : Fin N, ‖f x T - g T‖
        ≤ ∑ x : Fin N, 2 * ∑ s ∈ Finset.range T, ‖(g s) x‖ :=
      Finset.sum_le_sum fun x _ => hybrid_bound U psi0 x T
    have step2 : ∑ x : Fin N, 2 * ∑ s ∈ Finset.range T, ‖(g s) x‖
        = 2 * ∑ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    have step3 : ∑ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖ ≤ T * Real.sqrt N := by
      have : ∀ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖ ≤ Real.sqrt N := by
        intro s _
        have := sum_norm_apply_le (g s)
        rwa [hg, norm_run_id U psi0 s, hpsi0, mul_one] at this
      calc ∑ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖
          ≤ ∑ _s ∈ Finset.range T, Real.sqrt N := Finset.sum_le_sum this
        _ = T * Real.sqrt N := by simp
    linarith [step1, step2 ▸ step1, step3]
  -- Lower bound on the total distinguishability.
  have hlower : (N : ℝ) * Real.sqrt (2 / 3) - Real.sqrt N ≤ ∑ x : Fin N, ‖f x T - g T‖ := by
    have hpt : ∀ x : Fin N, Real.sqrt (2 / 3) - ‖(g T) x‖ ≤ ‖f x T - g T‖ := by
      intro x
      have hs : Real.sqrt (2 / 3) ≤ ‖(f x T) x‖ := by
        have := Real.sqrt_le_sqrt (hsucc x)
        rwa [Real.sqrt_sq (norm_nonneg _)] at this
      have hcomp : ‖(f x T) x - (g T) x‖ ≤ ‖f x T - g T‖ := by
        have := PiLp.norm_apply_le (f x T - g T) x
        simpa using this
      have := norm_sub_norm_le ((f x T) x) ((g T) x)
      linarith
    calc (N : ℝ) * Real.sqrt (2 / 3) - Real.sqrt N
        ≤ ∑ x : Fin N, (Real.sqrt (2 / 3) - ‖(g T) x‖) := by
          have hsum : ∑ x : Fin N, (Real.sqrt (2 / 3) - ‖(g T) x‖)
              = (N : ℝ) * Real.sqrt (2 / 3) - ∑ x : Fin N, ‖(g T) x‖ := by
            rw [Finset.sum_sub_distrib]
            simp
          have hle : ∑ x : Fin N, ‖(g T) x‖ ≤ Real.sqrt N := by
            have := sum_norm_apply_le (g T)
            rwa [hg, norm_run_id U psi0 T, hpsi0, mul_one] at this
          rw [hsum]; linarith
      _ ≤ ∑ x : Fin N, ‖f x T - g T‖ := Finset.sum_le_sum fun x _ => hpt x
  -- Combine.
  have hcomb : (N : ℝ) * Real.sqrt (2 / 3) - Real.sqrt N ≤ 2 * T * Real.sqrt N :=
    le_trans hlower hupper
  have hsN : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hprod : Real.sqrt (2 * N / 3) = Real.sqrt N * Real.sqrt (2 / 3) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
    ring_nf
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.sqrt_zero]
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    linarith
  · have hpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    rw [hprod]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have hkey : Real.sqrt N * (Real.sqrt N * Real.sqrt (2 / 3)) - Real.sqrt N
        ≤ Real.sqrt N * (2 * T) := by
      have : (N : ℝ) * Real.sqrt (2 / 3) = Real.sqrt N * (Real.sqrt N * Real.sqrt (2 / 3)) := by
        rw [← mul_assoc, ← sq, hsN]
      linarith [hcomb, this]
    have := le_of_mul_le_mul_left
      (by linarith [hkey] :
        Real.sqrt N * (Real.sqrt N * Real.sqrt (2 / 3) - 1) ≤ Real.sqrt N * (2 * T)) hpos
    linarith [this]

/-- A convenient `Ω(√N)` form of the BBBV bound: any bounded-error quantum search algorithm
for a database of `N` items uses `T ≥ √N / 3 - 1` queries. -/
theorem grover_optimal_sqrt (T : ℕ) (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (psi0 : HSpace N K)
    (hpsi0 : ‖psi0‖ = 1)
    (hsucc : ∀ x : Fin N, (2 : ℝ) / 3 ≤ ‖(run U (phaseOracle x) psi0 T) x‖ ^ 2) :
    Real.sqrt N ≤ 3 * ((T : ℝ) + 1) := by
  have hmain := grover_optimal T U psi0 hpsi0 hsucc
  have hprod : Real.sqrt (2 * N / 3) = Real.sqrt N * Real.sqrt (2 / 3) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
    ring_nf
  have hc : (4 : ℝ) / 5 ≤ Real.sqrt (2 / 3) := by
    rw [show (4 : ℝ) / 5 = Real.sqrt ((4 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsq : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith [hmain, hprod, hc, hsq]

end QI

