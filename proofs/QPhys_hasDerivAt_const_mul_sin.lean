/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The normalized stationary states of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/
noncomputable def psi (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (2 / L) * Real.sin (n * Real.pi * x / L)

/-- The energy levels of the infinite square well of width `L`:
`E_n = n²π²ℏ²/(2mL²)`. -/
noncomputable def energy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

lemma hasDerivAt_const_mul_sin (C c x : ℝ) :
    HasDerivAt (fun y : ℝ => C * Real.sin (c * y)) (C * c * Real.cos (c * x)) x := by
  have h : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have h2 := (h.sin).const_mul C
  convert h2 using 1
  ring

lemma hasDerivAt_const_mul_cos (C c x : ℝ) :
    HasDerivAt (fun y : ℝ => C * Real.cos (c * y)) (-(C * c) * Real.sin (c * x)) x := by
  have h : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have h2 := (h.cos).const_mul C
  convert h2 using 1
  ring

/-- `ψ_n` written with the wave number `k = nπ/L` factored out. -/
lemma psi_eq (L : ℝ) (n : ℕ) :
    psi L n = fun x => Real.sqrt (2 / L) * Real.sin ((n * Real.pi / L) * x) := by
  funext x
  unfold psi
  rw [show (n : ℝ) * Real.pi * x / L = (n * Real.pi / L) * x by ring]

/-- First derivative of `ψ_n`. -/
lemma deriv_psi (L : ℝ) (n : ℕ) :
    deriv (psi L n) =
      fun x => Real.sqrt (2 / L) * (n * Real.pi / L) * Real.cos ((n * Real.pi / L) * x) := by
  funext x
  rw [psi_eq]
  exact (hasDerivAt_const_mul_sin _ _ x).deriv

/-- Second derivative of `ψ_n`: it is `-k²ψ_n` with `k = nπ/L`. -/
lemma deriv2_psi (L : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (psi L n)) x = -((n * Real.pi / L) ^ 2) * psi L n x := by
  rw [deriv_psi, psi_eq]
  have := (hasDerivAt_const_mul_cos (Real.sqrt (2 / L) * (n * Real.pi / L))
      (n * Real.pi / L) x).deriv
  rw [this]
  ring

/-- Quantization: a positive wave number `k` with a node at `x = L` is of the form `nπ/L`
with `n ≥ 1`. -/
lemma wavenumber_quantized {L k : ℝ} (hL : 0 < L) (hk : 0 < k) (h : Real.sin (k * L) = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ k = n * Real.pi / L := by
  obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp h
  have hzpos : 0 < (z : ℝ) := by
    have hkl : 0 < k * L := mul_pos hk hL
    nlinarith [Real.pi_pos]
  have hz1 : 1 ≤ z := by exact_mod_cast hzpos
  refine ⟨z.toNat, ?_, ?_⟩
  · omega
  · have : ((z.toNat : ℤ) : ℝ) = (z : ℝ) := by
      rw [Int.toNat_of_nonneg (by omega)]
    push_cast at this ⊢
    rw [this]
    field_simp
    linarith [hz]

/-- **Particle in a box.**  For a well of width `L > 0`, mass `m > 0` and reduced Planck
constant `ℏ > 0`:

1. the state `ψ_n(x) = √(2/L)·sin(nπx/L)` satisfies the box boundary conditions
   `ψ_n(0) = ψ_n(L) = 0`;
2. it solves the time-independent Schrödinger equation
   `-ℏ²/(2m) ψ_n'' = E_n ψ_n` with `E_n = n²π²ℏ²/(2mL²)`;
3. conversely, any positive wave number `k` for which `sin(k·)` vanishes at `x = L`
   (i.e. any solution of the free equation obeying both boundary conditions) has
   energy `ℏ²k²/(2m) = E_n` for some `n ≥ 1`;
4. the energies are strictly increasing in `n`, and positive for `n ≥ 1`. -/
theorem particle_in_box {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    (∀ n : ℕ, psi L n 0 = 0 ∧ psi L n L = 0) ∧
    (∀ (n : ℕ) (x : ℝ),
      -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi L n)) x = energy hbar m L n * psi L n x) ∧
    (∀ k : ℝ, 0 < k → Real.sin (k * L) = 0 →
      ∃ n : ℕ, 1 ≤ n ∧ hbar ^ 2 * k ^ 2 / (2 * m) = energy hbar m L n) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < energy hbar m L n ∧ energy hbar m L n < energy hbar m L (n + 1)) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · simp [psi]
    · have : (n : ℝ) * Real.pi * L / L = n * Real.pi := by field_simp
      simp [psi, this, Real.sin_nat_mul_pi]
  · intro n x
    rw [deriv2_psi, energy]
    have : ((n : ℝ) * Real.pi / L) ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 / L ^ 2 := by
      field_simp
    rw [this]
    field_simp
  · intro k hk hsin
    obtain ⟨n, hn, hkn⟩ := wavenumber_quantized hL hk hsin
    refine ⟨n, hn, ?_⟩
    rw [hkn, energy]
    field_simp
  · intro n hn
    have hpi := Real.pi_pos
    have hden : 0 < 2 * m * L ^ 2 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    constructor
    · unfold energy
      apply div_pos _ hden
      have : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
      positivity
    · unfold energy
      push_cast
      gcongr
      nlinarith [Real.pi_pos, sq_nonneg hbar]

end QPhys

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

