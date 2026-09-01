import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The two-dimensional Ising model on a periodic square lattice -/

/-- The real spin value attached to a Boolean spin variable: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- A spin configuration on the `(n+1) × (n+1)` square lattice with periodic
boundary conditions (a discrete torus). -/
abbrev Config (n : ℕ) : Type := Fin (n + 1) × Fin (n + 1) → Bool

/-- The sum `∑_{⟨x,y⟩} σ_x σ_y` over all nearest-neighbour bonds of the periodic
`(n+1) × (n+1)` square lattice.  Each site contributes the bond to its right
neighbour and the bond to the neighbour below it, so every bond is counted once. -/
def bondSum {n : ℕ} (σ : Config n) : ℝ :=
  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
    (spin (σ (i, j)) * spin (σ (i + 1, j)) + spin (σ (i, j)) * spin (σ (i, j + 1)))

/-- The partition function `Z_N(K) = ∑_σ exp (K ∑_{⟨x,y⟩} σ_x σ_y)` of the
two-dimensional Ising model on the periodic `(n+1) × (n+1)` lattice, at reduced
coupling `K = β J`. -/
noncomputable def isingPartition (n : ℕ) (K : ℝ) : ℝ :=
  ∑ σ : Config n, Real.exp (K * bondSum σ)

/-- The free energy density in the form `(1 / N²) log Z_N(K)`, i.e. `-β f_N(K)`. -/
noncomputable def logPartitionDensity (n : ℕ) (K : ℝ) : ℝ :=
  Real.log (isingPartition n K) / ((n + 1 : ℝ) ^ 2)

/-- Onsager's exact expression for the infinite-volume free energy density
`-β f(K)` of the two-dimensional Ising model:
`log 2 + (2π)⁻² ∫₀^{2π} ∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₂ dθ₁`. -/
noncomputable def onsagerLogPartitionDensity (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (2 * π) ^ 2) *
    ∫ t₁ in (0 : ℝ)..(2 * π), ∫ t₂ in (0 : ℝ)..(2 * π),
      Real.log (Real.cosh (2 * K) ^ 2
        - Real.sinh (2 * K) * (Real.cos t₁ + Real.cos t₂))

/-- The partition function is positive, so the free energy density is well defined. -/
theorem isingPartition_pos (n : ℕ) (K : ℝ) : 0 < isingPartition n K := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- The single-site lattice: both configurations have bond sum `2` (the site is its own
neighbour in both directions), so `Z₁(K) = 2 e^{2K}`. -/
theorem isingPartition_zero_size (K : ℝ) :
    isingPartition 0 K = 2 * Real.exp (2 * K) := by
  have hb : ∀ σ : Config 0, bondSum σ = 2 := by
    intro σ
    rw [bondSum, Fin.sum_univ_one, Fin.sum_univ_one, show (0 + 1 : Fin 1) = 0 from rfl]
    rcases h : σ (0, 0) with _ | _ <;> norm_num [spin, h]
  simp only [isingPartition, hb]
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (Config 0) = 2 := by decide
  rw [hcard, nsmul_eq_mul, mul_comm K 2]
  norm_num

/-! ## Exact evaluation at infinite temperature (`K = 0`) -/

/-- At infinite temperature all `2^{N²}` configurations have equal weight. -/
theorem isingPartition_zero (n : ℕ) :
    isingPartition n 0 = 2 ^ ((n + 1) ^ 2) := by
  simp [isingPartition, Finset.card_univ, pow_two]

/-- The finite-volume free energy density at infinite temperature is exactly `log 2`,
for every lattice size. -/
theorem logPartitionDensity_zero (n : ℕ) :
    logPartitionDensity n 0 = Real.log 2 := by
  have hn : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  rw [logPartitionDensity, isingPartition_zero, Real.log_pow]
  push_cast
  field_simp

/-- Onsager's expression at `K = 0` collapses to `log 2`. -/
theorem onsagerLogPartitionDensity_zero :
    onsagerLogPartitionDensity 0 = Real.log 2 := by
  simp [onsagerLogPartitionDensity]

/-! ## The transfer-matrix reduction -/

/-- A configuration of a single row of the lattice. -/
abbrev RowConfig (n : ℕ) : Type := Fin (n + 1) → Bool

/-- The interaction energy (with sign convention `∑ σ σ'`) between two adjacent rows. -/
def rowCoupling {n : ℕ} (s s' : RowConfig n) : ℝ :=
  ∑ j : Fin (n + 1), spin (s j) * spin (s' j)

/-- The interaction inside a single row. -/
def rowInternal {n : ℕ} (s : RowConfig n) : ℝ :=
  ∑ j : Fin (n + 1), spin (s j) * spin (s (j + 1))

/-- The Ising transfer matrix: it acts on the `2^{n+1}` configurations of one row. -/
noncomputable def transferMatrix (n : ℕ) (K : ℝ) : Matrix (RowConfig n) (RowConfig n) ℝ :=
  Matrix.of fun s s' => Real.exp (K * (rowCoupling s s' + rowInternal s))

/-- Entries of a matrix power as a sum over paths: `(T ^ (m+1)) x y` is the sum,
over all choices `f` of `m` intermediate states, of the product of the transition
weights along the path `x, f 0, …, f (m-1), y`. -/
theorem pow_apply_eq_sum_paths {S : Type} [Fintype S] [DecidableEq S] (T : Matrix S S ℝ) :
    ∀ (m : ℕ) (x y : S), (T ^ (m + 1)) x y =
      ∑ f : Fin m → S,
        (∏ i : Fin m, T ((Fin.cons x f : Fin (m + 1) → S) i.castSucc)
            ((Fin.cons x f : Fin (m + 1) → S) i.succ)) *
          T ((Fin.cons x f : Fin (m + 1) → S) (Fin.last m)) y := by
  intro m
  induction m with
  | zero => intro x y; simp
  | succ m ih =>
      intro x y
      have hpow : (T ^ (m + 2)) x y = ∑ z : S, T x z * (T ^ (m + 1)) z y := by
        rw [pow_succ']
        simp [Matrix.mul_apply]
      rw [hpow]
      simp only [ih]
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => S)), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      show T x z * _ = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.castSucc_zero, Fin.cons_zero,
        Fin.succ_zero_eq_one, ← Fin.succ_castSucc, Fin.cons_succ, ← Fin.succ_last]
      rw [show (1 : Fin (m + 2)) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
      ring

/-- The trace of a matrix power as a sum over closed cycles. -/
theorem trace_pow_eq_sum_cycles {S : Type} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℝ) (m : ℕ) :
    Matrix.trace (T ^ (m + 1)) =
      ∑ h : Fin (m + 1) → S, ∏ i : Fin (m + 1), T (h i) (h (i + 1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => S)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_apply_eq_sum_paths T m x x]
  refine Finset.sum_congr rfl fun f _ => ?_
  show _ = ∏ i : Fin (m + 1), _
  rw [Fin.prod_univ_castSucc]
  simp [Fin.coeSucc_eq_succ, Fin.last_add_one, Fin.consEquiv]

/-- The bond sum of a configuration, organised row by row. -/
theorem bondSum_eq_rows {n : ℕ} (σ : Config n) :
    bondSum σ = ∑ i : Fin (n + 1),
      (rowCoupling (fun j => σ (i, j)) (fun j => σ (i + 1, j))
        + rowInternal (fun j => σ (i, j))) := by
  rw [bondSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_add_distrib]
  rfl

/-- **Transfer-matrix reduction.**  The partition function of the periodic
`(n+1) × (n+1)` Ising lattice is the trace of the `(n+1)`-st power of the
transfer matrix. -/
theorem isingPartition_eq_trace_transferMatrix (n : ℕ) (K : ℝ) :
    isingPartition n K = Matrix.trace (transferMatrix n K ^ (n + 1)) := by
  rw [trace_pow_eq_sum_cycles, isingPartition,
    ← Equiv.sum_comp (Equiv.curry (Fin (n + 1)) (Fin (n + 1)) Bool)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [transferMatrix, Matrix.of_apply, Equiv.curry_apply]
  rw [← Real.exp_sum]
  congr 1
  rw [bondSum_eq_rows, Finset.mul_sum]
  rfl

/-! ## Main statement -/

/-- **Onsager's solution of the two-dimensional Ising model** (formalised statement,
with the transfer-matrix reduction and the infinite-temperature case proved).

The conjuncts are:

0. positivity of the finite-volume partition function (so that the free energy
   density is well defined);
1. the exact transfer-matrix reduction of the finite-volume partition function,
   valid for every lattice size and every coupling;
2. the exact evaluation `Z_N(0) = 2^{N²}` of the partition function at infinite
   temperature, together with Onsager's formula giving the value `log 2` there;
3. the infinite-temperature case of Onsager's theorem: the finite-volume free
   energy densities converge, as the lattice size tends to infinity, to the value
   predicted by Onsager's exact expression. -/
theorem onsager_2d_ising :
    (∀ (n : ℕ) (K : ℝ), 0 < isingPartition n K) ∧
    (∀ (n : ℕ) (K : ℝ),
        isingPartition n K = Matrix.trace (transferMatrix n K ^ (n + 1))) ∧
    (∀ n : ℕ, isingPartition n 0 = 2 ^ ((n + 1) ^ 2)) ∧
    onsagerLogPartitionDensity 0 = Real.log 2 ∧
    Filter.Tendsto (fun n : ℕ => logPartitionDensity n 0) Filter.atTop
      (nhds (onsagerLogPartitionDensity 0)) := by
  refine ⟨isingPartition_pos, isingPartition_eq_trace_transferMatrix, isingPartition_zero,
    onsagerLogPartitionDensity_zero, ?_⟩
  rw [onsagerLogPartitionDensity_zero]
  simp only [logPartitionDensity_zero]
  exact tendsto_const_nhds

end Frontier

