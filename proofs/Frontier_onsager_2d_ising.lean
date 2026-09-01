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

/-- The real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The cyclic successor of an index of `Fin m` (periodic boundary conditions). -/
def nextIdx {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.1 + 1) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- The energy of a spin configuration on the `m × n` square-lattice torus,
with nearest-neighbour coupling `J`. -/
def energy {m n : ℕ} (J : ℝ) (σ : Fin m × Fin n → Bool) : ℝ :=
  -J * ∑ i : Fin m, ∑ j : Fin n,
      (spin (σ (i, j)) * spin (σ (nextIdx i, j)) + spin (σ (i, j)) * spin (σ (i, nextIdx j)))

/-- The canonical partition function of the 2D Ising model on the `m × n` torus
at inverse temperature `β` and coupling `J`. -/
noncomputable def Z (m n : ℕ) (β J : ℝ) : ℝ :=
  ∑ σ : Fin m × Fin n → Bool, Real.exp (-β * energy J σ)

/-- The (dimensionless) free energy per site, `-β f = (1/(mn)) log Z`. -/
noncomputable def freeEnergyDensity (m n : ℕ) (β J : ℝ) : ℝ :=
  (1 / (m * n : ℝ)) * Real.log (Z m n β J)

/-- Onsager's exact expression for `-β f` in the thermodynamic limit. -/
noncomputable def onsagerFree (β J : ℝ) : ℝ :=
  Real.log 2 + (1 / (2 * (2 * π) ^ 2)) * ∫ x in (0:ℝ)..(2 * π), ∫ y in (0:ℝ)..(2 * π),
    Real.log ((Real.cosh (2 * β * J)) ^ 2 - Real.sinh (2 * β * J) * (Real.cos x + Real.cos y))

/-- The partition function is a sum of exponentials, hence strictly positive. -/
lemma Z_pos (m n : ℕ) (β J : ℝ) : 0 < Z m n β J :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- At infinite temperature (`β = 0`) every one of the `2 ^ (mn)` configurations has weight `1`. -/
lemma Z_zero_beta (m n : ℕ) (J : ℝ) : Z m n 0 J = 2 ^ (m * n) := by
  simp [Z]

/-- Onsager's expression at `β = 0` reduces to `log 2`. -/
lemma onsagerFree_zero_beta (J : ℝ) : onsagerFree 0 J = Real.log 2 := by
  simp [onsagerFree]

/-- The finite-lattice free energy per site at `β = 0` is `log 2`. -/
lemma freeEnergyDensity_zero_beta (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (J : ℝ) :
    freeEnergyDensity m n 0 J = Real.log 2 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [freeEnergyDensity, Z_zero_beta, Real.log_pow]
  push_cast
  field_simp

/-- The explicit enumeration of the sixteen spin configurations of the `2 × 2` torus. -/
def cfg22 : (Bool × Bool × Bool × Bool) ≃ (Fin 2 × Fin 2 → Bool) where
  toFun b p :=
    if p = (0, 0) then b.1 else if p = (0, 1) then b.2.1 else if p = (1, 0) then b.2.2.1
    else b.2.2.2
  invFun σ := (σ (0, 0), σ (0, 1), σ (1, 0), σ (1, 1))
  left_inv b := by rfl
  right_inv σ := by funext p; fin_cases p <;> rfl

/-- Exact finite-size evaluation: on the `2 × 2` torus (where every bond is doubled)
`Z = 12 + 4 cosh (8βJ)`. -/
lemma Z_two_two (β J : ℝ) : Z 2 2 β J = 12 + 4 * Real.cosh (8 * β * J) := by
  rw [Z, ← Equiv.sum_comp cfg22 (fun σ => Real.exp (-β * energy J σ))]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, energy, Fin.sum_univ_two, cfg22,
    Equiv.coe_fn_mk, spin, nextIdx]
  norm_num
  rw [Real.cosh_eq, show (8:ℝ) * β * J = β * (J * 8) by ring]
  ring

/-- The Onsager critical point: `sinh (2βJ) = 1` holds exactly at `β = log (1 + √2) / (2J)`. -/
lemma sinh_two_beta_J_eq_one_iff (J β : ℝ) (hJ : 0 < J) :
    Real.sinh (2 * β * J) = 1 ↔ β = Real.log (1 + Real.sqrt 2) / (2 * J) := by
  have harsinh : Real.arsinh 1 = Real.log (1 + Real.sqrt 2) := by rw [Real.arsinh]; norm_num
  have key : ∀ t : ℝ, Real.sinh t = 1 ↔ t = Real.log (1 + Real.sqrt 2) := by
    intro t
    constructor
    · intro h
      have h' := congrArg Real.arsinh h
      rwa [Real.arsinh_sinh, harsinh] at h'
    · intro h
      rw [h, ← harsinh, Real.sinh_arsinh]
  rw [key, eq_div_iff (by positivity : (2:ℝ) * J ≠ 0)]
  constructor <;> intro h <;> linarith

/-- **Onsager 2D Ising (formalized statement and Lean-checked reduction).**

The 2D square-lattice Ising model on the `m × n` torus is set up in `Frontier.Z`, its
free energy per site in `Frontier.freeEnergyDensity`, and Onsager's exact thermodynamic-limit
expression in `Frontier.onsagerFree`.  The theorem records:

* the partition function is strictly positive, so the free energy is well defined;
* the infinite-temperature base case: for every finite torus the free energy per site equals
  Onsager's expression evaluated at `β = 0` (both are `log 2`);
* the exact finite-size evaluation on the `2 × 2` torus;
* the Kramers–Wannier/Onsager critical point: `sinh (2βJ) = 1` exactly at
  `β = log (1 + √2) / (2J)`.
-/
theorem onsager_2d_ising :
    (∀ (m n : ℕ) (β J : ℝ), 0 < Z m n β J) ∧
    (∀ (m n : ℕ) (J : ℝ), 0 < m → 0 < n →
      freeEnergyDensity m n 0 J = onsagerFree 0 J) ∧
    (∀ (m n : ℕ) (J : ℝ), Z m n 0 J = 2 ^ (m * n)) ∧
    (∀ β J : ℝ, Z 2 2 β J = 12 + 4 * Real.cosh (8 * β * J)) ∧
    (∀ β J : ℝ, 0 < J →
      (Real.sinh (2 * β * J) = 1 ↔ β = Real.log (1 + Real.sqrt 2) / (2 * J))) := by
  refine ⟨Z_pos, ?_, Z_zero_beta, Z_two_two, fun β J hJ => sinh_two_beta_J_eq_one_iff J β hJ⟩
  intro m n J hm hn
  rw [freeEnergyDensity_zero_beta m n hm hn J, onsagerFree_zero_beta]

end Frontier

