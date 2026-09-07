/-
  Brockian/D5Isotypic.lean

  Cyclic Fourier analysis on the D₅ permutation representation
  `VertexSpace = Fin 5 → ℂ` from `Brockian.D5Representation`.

  Honest scope (this file proves, and only proves):
    * Rotation pullback: `d5Pull (r k) f x = f (x - k)` for `k : Fin 5`.
    * Fifth root `ω = exp(2πi/5)` is a primitive 5-th root of unity.
    * Eigenmodes `vⱼ(x) = ω^{j·x}` (exponent via `ZMod.val` / `Fin.val`).
    * Eigenrelation under the pullback convention of `d5Pull`:
        `d5Pull (r 1) vⱼ = ω^{-j} • vⱼ`
      (equivalently `d5Pull (r k) vⱼ = ω^{-j k} • vⱼ`).
    * Constant mode: `v₀ = constantVector 1`; non-constant modes are zero-sum.
    * Geometric sum / character orthogonality of powers of `ω`.
    * Cyclic isotypic projector for the rotation subgroup C₅ ≤ D₅:
        `Pⱼ f = (1/5) ∑_k ω^{j k} · (rᵏ • f)`
      (pullback character `χⱼ(rᵏ) = ω^{-j k}`, so the projector conjugates with
      `ω^{j k}`).  Proved: `Pⱼ vₗ = δⱼₗ vₗ`, and idempotence / orthogonality of
      the family `{Pⱼ}` on the Fourier basis (hence on its span).

  Not claimed:
    * Full D₅-isotypic decomposition into the 2-dimensional real irreps.
    * Pointwise Fourier inversion for an arbitrary `f : VertexSpace` (the basis
      diagonalization is enough for the cyclic projector algebra on modes).
    * Any RH / spectral statement about ζ.  No new axioms.

  Verification target (spec §2A): AXLE @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.D5Representation
import Brockian.AutomorphismFull

open BigOperators
open DihedralGroup
open Complex
open Brockian.D5Representation
open Brockian.Automorphism
open Brockian.Automorphism.Full

namespace Brockian.D5Isotypic

/-! ### Rotation pullback on vertex functions

All rotation indices are `Fin 5` (definitionally `ZMod 5`), so subtraction and
multiplication stay homogeneous and typeclass search succeeds. -/

/-- Pullback by the pure rotation `r k`: `(rᵏ • f)(x) = f(x − k)`. -/
theorem d5Pull_r_apply (k : Fin 5) (f : VertexSpace) (x : Fin 5) :
    d5Pull (r k) f x = f (x - k) := by
  -- `dihedralHom (r k) = rotIso k = Equiv.addRight k`, inverse = subtract-`k`.
  simp [d5Pull_apply, dihedralHom_r, rotIso, rotEquiv, sub_eq_add_neg]

/-- Generator rotation by one vertex. -/
theorem d5Pull_r_one_apply (f : VertexSpace) (x : Fin 5) :
    d5Pull (r (1 : Fin 5)) f x = f (x - 1) :=
  d5Pull_r_apply 1 f x

/-- Rotations compose: `r a` then `r b` is `r (a+b)`. -/
theorem d5Pull_r_mul (a b : Fin 5) (f : VertexSpace) :
    d5Pull (r a) (d5Pull (r b) f) = d5Pull (r (a + b)) f := by
  ext x
  simp only [d5Pull_r_apply]
  abel

/-! ### Fifth root of unity -/

/-- Primitive fifth root of unity `ω = exp(2πi/5)`. -/
noncomputable def omega : ℂ := exp (2 * Real.pi * I / 5)

local notation "ω" => omega

theorem omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 :=
  isPrimitiveRoot_exp 5 (by decide)

theorem omega_pow_five : ω ^ 5 = 1 :=
  omega_isPrimitiveRoot.pow_eq_one

theorem orderOf_omega : orderOf ω = 5 :=
  omega_isPrimitiveRoot.eq_orderOf.symm

/-- Powers of `ω` depend only on the exponent mod 5. -/
theorem omega_pow_modEq {m n : ℕ} (h : m ≡ n [MOD 5]) : ω ^ m = ω ^ n := by
  -- Use `pow_mod_orderOf` (available without left-cancellation on `ℂ`) plus `orderOf ω = 5`.
  have hord : orderOf ω = 5 := orderOf_omega
  have hm : ω ^ m = ω ^ (m % 5) := by
    simpa [hord] using (pow_mod_orderOf ω m).symm
  have hn : ω ^ n = ω ^ (n % 5) := by
    simpa [hord] using (pow_mod_orderOf ω n).symm
  -- `m ≡ n [MOD 5]` is definitionally `m % 5 = n % 5` on `ℕ`.
  have hmn : m % 5 = n % 5 := h
  rw [hm, hn, hmn]

/-- Canonical power map `Fin 5 → ℂ`, `a ↦ ω^{a.val}`. -/
noncomputable def omegaPow (a : Fin 5) : ℂ := ω ^ a.val

@[simp] theorem omegaPow_zero : omegaPow 0 = 1 := by
  simp [omegaPow]

@[simp] theorem omegaPow_one : omegaPow 1 = ω := by
  simp [omegaPow]

/-- The power map is multiplicative: `ω^{a+b} = ω^a · ω^b`. -/
theorem omegaPow_add (a b : Fin 5) : omegaPow (a + b) = omegaPow a * omegaPow b := by
  simp only [omegaPow]
  -- On `Fin 5`, `(a+b).val = (a.val + b.val) % 5`.
  have hval : (a + b).val = (a.val + b.val) % 5 := by
    -- `Fin.val_add` : `(a + b).val = (a.val + b.val) % n`
    simpa using (Fin.val_add a b)
  have hmod : ω ^ ((a.val + b.val) % 5) = ω ^ (a.val + b.val) :=
    omega_pow_modEq (Nat.mod_modEq (a.val + b.val) 5)
  rw [hval, hmod, pow_add]

theorem omegaPow_neg (a : Fin 5) : omegaPow (-a) = (omegaPow a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← omegaPow_add, neg_add_cancel, omegaPow_zero]

/-- `ω^n = 1` iff `5 ∣ n`. -/
theorem omega_pow_eq_one_iff (n : ℕ) : ω ^ n = 1 ↔ 5 ∣ n := by
  rw [← orderOf_omega, orderOf_dvd_iff_pow_eq_one]

/-! ### Eigenmodes `vⱼ(x) = ω^{j·x}` -/

/-- Fourier mode of frequency `j` on the five vertices. -/
noncomputable def eigenmode (j : Fin 5) : VertexSpace :=
  fun x => omegaPow (j * x)

@[simp] theorem eigenmode_apply (j x : Fin 5) :
    eigenmode j x = omegaPow (j * x) := rfl

/-- The zero mode is the constant function `1`. -/
theorem eigenmode_zero : eigenmode 0 = constantVector 1 := by
  funext x
  simp [eigenmode, constantVector, omegaPow]

/-- Pullback of an eigenmode by `r k` multiplies by the character `ω^{-j k}`. -/
theorem d5Pull_r_eigenmode (j k : Fin 5) :
    d5Pull (r k) (eigenmode j) = omegaPow (-(j * k)) • eigenmode j := by
  ext x
  simp only [d5Pull_r_apply, eigenmode_apply, Pi.smul_apply, smul_eq_mul]
  -- Goal: `ω^{j(x−k)} = ω^{-j k} · ω^{j x}`.
  have hidx : (-(j * k) + j * x : Fin 5) = j * (x - k) := by
    calc
      -(j * k) + j * x = j * x + -(j * k) := by abel
      _ = j * x + j * (-k) := by rw [mul_neg]
      _ = j * (x + -k) := by rw [← mul_add]
      _ = j * (x - k) := by rw [← sub_eq_add_neg]
  calc
    omegaPow (j * (x - k))
        = omegaPow (-(j * k) + j * x) := by rw [← hidx]
    _   = omegaPow (-(j * k)) * omegaPow (j * x) := omegaPow_add _ _

/-- Generator form: `r₁ • vⱼ = ω^{-j} • vⱼ` (pullback convention). -/
theorem d5Pull_r_one_eigenmode (j : Fin 5) :
    d5Pull (r (1 : Fin 5)) (eigenmode j) = omegaPow (-j) • eigenmode j := by
  simpa [mul_one] using d5Pull_r_eigenmode j 1

/-! ### Geometric sums / character orthogonality -/

private theorem val_ne_zero_of_ne_zero {a : Fin 5} (ha : a ≠ 0) : a.val ≠ 0 := by
  intro h
  apply ha
  exact Fin.ext h

/-- Full geometric sum of a nontrivial 5-th root of unity vanishes. -/
theorem sum_omegaPow_ne_zero {a : Fin 5} (ha : a ≠ 0) :
    ∑ x : Fin 5, omegaPow (a * x) = 0 := by
  have ha0 : a.val ≠ 0 := val_ne_zero_of_ne_zero ha
  have hcop : Nat.Coprime a.val 5 := by
    have hlt : a.val < 5 := a.is_lt
    -- a.val ∈ {1,2,3,4} (0 is ruled out by `ha0`)
    interval_cases a.val
    · exact absurd rfl ha0
    · decide
    · decide
    · decide
    · decide
  have hprim : IsPrimitiveRoot (ω ^ a.val) 5 :=
    omega_isPrimitiveRoot.pow_of_coprime a.val hcop
  have hgeom : ∑ i ∈ Finset.range 5, (ω ^ a.val) ^ i = 0 :=
    IsPrimitiveRoot.geom_sum_eq_zero hprim (by decide)
  -- Reindex `Fin 5` ↔ `range 5`.
  have hreindex :
      ∑ x : Fin 5, omegaPow (a * x) = ∑ i ∈ Finset.range 5, (ω ^ a.val) ^ i := by
    simp only [omegaPow]
    refine Finset.sum_bij (fun x _ => (x : ℕ)) ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_range.mpr x.is_lt
    · intro x y _ _ h
      exact Fin.ext h
    · intro i hi
      refine ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩
    · intro x _
      -- `(a * x).val = a.val * x.val % 5`, so the powers of `ω` agree.
      have hmul : (a * x).val ≡ a.val * x.val [MOD 5] := by
        rw [Fin.val_mul]
        exact Nat.mod_modEq _ _
      exact (omega_pow_modEq hmul).trans (by rw [pow_mul])
  rw [hreindex, hgeom]

/-- Geometric sum: `∑_x ω^{a x} = 5` if `a = 0`, else `0`. -/
theorem sum_omegaPow (a : Fin 5) :
    ∑ x : Fin 5, omegaPow (a * x) = if a = 0 then (5 : ℂ) else 0 := by
  split_ifs with ha
  · -- a = 0: each term is `ω^0 = 1`, five of them.
    subst ha
    simp [omegaPow]
  · exact sum_omegaPow_ne_zero ha

/-- Character orthogonality: `(1/5) ∑_k ω^{(j−ℓ) k} = δ_{jℓ}`. -/
theorem character_orthogonality (j ℓ : Fin 5) :
    (5 : ℂ)⁻¹ * ∑ k : Fin 5, omegaPow ((j - ℓ) * k) =
      if j = ℓ then (1 : ℂ) else 0 := by
  rw [sum_omegaPow (j - ℓ)]
  by_cases hjl : j = ℓ
  · -- `j = ℓ` ⇒ `j − ℓ = 0` ⇒ sum = 5 ⇒ (5)⁻¹ * 5 = 1
    subst hjl
    simp only [sub_self, ↓reduceIte]
    field_simp
  · -- `j ≠ ℓ` ⇒ `j − ℓ ≠ 0` ⇒ sum = 0 ⇒ (5)⁻¹ * 0 = 0
    have hne : j - ℓ ≠ 0 := fun h => hjl (sub_eq_zero.mp h)
    simp only [hne, hjl, ↓reduceIte, mul_zero]

/-- Coordinate sum of an eigenmode: `5` on the constant mode, else `0`. -/
theorem coordSum_eigenmode (j : Fin 5) :
    coordSum (eigenmode j) = if j = 0 then (5 : ℂ) else 0 := by
  simp only [coordSum, eigenmode_apply]
  -- `sum_omegaPow j` is exactly this sum.
  simpa using sum_omegaPow j

theorem eigenmode_mem_zeroSumSubmodule {j : Fin 5} (hj : j ≠ 0) :
    eigenmode j ∈ zeroSumSubmodule := by
  change coordSumLinear (eigenmode j) = 0
  rw [coordSumLinear_apply, coordSum_eigenmode, if_neg hj]

/-! ### Cyclic isotypic projectors -/

/-- Cyclic isotypic projector for frequency `j` along the rotation subgroup:
`Pⱼ f = (1/5) ∑_k ω^{j k} · (rᵏ • f)`.

(The pullback character is `χⱼ(rᵏ) = ω^{-j k}`, so the projector conjugates by
`χⱼ(rᵏ)⁻¹ = ω^{j k}` — matching `d5Pull_r_eigenmode`.) -/
noncomputable def isotypicProjector (j : Fin 5) (f : VertexSpace) : VertexSpace :=
  (5 : ℂ)⁻¹ • ∑ k : Fin 5, omegaPow (j * k) • d5Pull (r k) f

theorem isotypicProjector_apply (j : Fin 5) (f : VertexSpace) (x : Fin 5) :
    isotypicProjector j f x =
      (5 : ℂ)⁻¹ * ∑ k : Fin 5, omegaPow (j * k) * f (x - k) := by
  simp only [isotypicProjector, Pi.smul_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, d5Pull_r_apply, Finset.mul_sum]

/-- The projector diagonalizes the Fourier basis: `Pⱼ vₗ = δⱼₗ vₗ`. -/
theorem isotypicProjector_eigenmode (j ℓ : Fin 5) :
    isotypicProjector j (eigenmode ℓ) =
      (if j = ℓ then (1 : ℂ) else 0) • eigenmode ℓ := by
  funext x
  simp only [isotypicProjector, Pi.smul_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  -- Each term: `ω^{j k} · (rᵏ vₗ)(x) = ω^{(j−ℓ) k} · vₗ(x)`.
  have hterm : ∀ k : Fin 5,
      omegaPow (j * k) * d5Pull (r k) (eigenmode ℓ) x =
        omegaPow ((j - ℓ) * k) * eigenmode ℓ x := by
    intro k
    rw [d5Pull_r_eigenmode, Pi.smul_apply, smul_eq_mul]
    have hab : omegaPow (j * k) * omegaPow (-(ℓ * k)) = omegaPow ((j - ℓ) * k) := by
      rw [← omegaPow_add]
      congr 1
      -- `j*k + -(ℓ*k) = (j + -ℓ)*k = (j - ℓ)*k`
      calc
        j * k + -(ℓ * k) = j * k + (-ℓ) * k := by rw [neg_mul]
        _ = (j + -ℓ) * k := by rw [← add_mul]
        _ = (j - ℓ) * k := by rw [← sub_eq_add_neg]
    rw [← mul_assoc, hab]
  simp_rw [hterm]
  have hsum :
      ∑ k : Fin 5, omegaPow ((j - ℓ) * k) * eigenmode ℓ x =
        (∑ k : Fin 5, omegaPow ((j - ℓ) * k)) * eigenmode ℓ x := by
    rw [Finset.sum_mul]
  rw [hsum]
  have hchar := character_orthogonality j ℓ
  calc
    (5 : ℂ)⁻¹ * ((∑ k : Fin 5, omegaPow ((j - ℓ) * k)) * eigenmode ℓ x)
        = ((5 : ℂ)⁻¹ * ∑ k : Fin 5, omegaPow ((j - ℓ) * k)) * eigenmode ℓ x := by
          ring
    _ = (if j = ℓ then (1 : ℂ) else 0) * eigenmode ℓ x := by rw [hchar]

/-- Special case: `Pⱼ` fixes its own mode. -/
theorem isotypicProjector_eigenmode_self (j : Fin 5) :
    isotypicProjector j (eigenmode j) = eigenmode j := by
  simpa using isotypicProjector_eigenmode j j

/-- Off-diagonal modes are killed. -/
theorem isotypicProjector_eigenmode_of_ne {j ℓ : Fin 5} (h : j ≠ ℓ) :
    isotypicProjector j (eigenmode ℓ) = 0 := by
  simpa [h] using isotypicProjector_eigenmode j ℓ

/-- Homogeneity of the isotypic projector. -/
theorem isotypicProjector_smul (j : Fin 5) (c : ℂ) (f : VertexSpace) :
    isotypicProjector j (c • f) = c • isotypicProjector j f := by
  funext x
  simp only [isotypicProjector, Pi.smul_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  have hsmul : ∀ k : Fin 5, d5Pull (r k) (c • f) = c • d5Pull (r k) f := by
    intro k
    ext y
    simp [Pi.smul_apply, smul_eq_mul]
  simp_rw [hsmul, Pi.smul_apply, smul_eq_mul]
  have hsum :
      ∑ k : Fin 5, omegaPow (j * k) * (c * d5Pull (r k) f x) =
        c * ∑ k : Fin 5, omegaPow (j * k) * d5Pull (r k) f x := by
    simp_rw [mul_left_comm _ c]
    rw [← Finset.mul_sum]
  rw [hsum]
  -- `(5)⁻¹ * (c * S) = c * ((5)⁻¹ * S)`
  ac_rfl

/-- **Idempotence on the Fourier basis.** `Pⱼ (Pⱼ vₗ) = Pⱼ vₗ`.

Together with `isotypicProjector_eigenmode`, this is the cyclic projector algebra
on the eigenbasis. (Full-space idempotence for arbitrary `f` is the same identity
after Fourier expansion; we stop at the basis to keep the proof hole-free and
local.) -/
theorem isotypicProjector_idempotent_eigenmode (j ℓ : Fin 5) :
    isotypicProjector j (isotypicProjector j (eigenmode ℓ)) =
      isotypicProjector j (eigenmode ℓ) := by
  rw [isotypicProjector_eigenmode, isotypicProjector_smul,
    isotypicProjector_eigenmode]
  -- `(if j=ℓ then 1 else 0) • ((if j=ℓ then 1 else 0) • v) = (if …) • v`
  by_cases h : j = ℓ
  · simp [h]
  · simp [h]

/-- **Self-idempotence on its own mode:** `Pⱼ (Pⱼ vⱼ) = Pⱼ vⱼ = vⱼ`. -/
theorem isotypicProjector_idempotent_self (j : Fin 5) :
    isotypicProjector j (isotypicProjector j (eigenmode j)) = eigenmode j := by
  rw [isotypicProjector_idempotent_eigenmode, isotypicProjector_eigenmode_self]

/-- Projectors for distinct frequencies annihilate each other's modes:
`Pⱼ (Pₗ v) = 0` on eigenmodes when `j ≠ ℓ`. -/
theorem isotypicProjector_orthogonal_eigenmode {j ℓ : Fin 5} (h : j ≠ ℓ)
    (m : Fin 5) :
    isotypicProjector j (isotypicProjector ℓ (eigenmode m)) = 0 := by
  rw [isotypicProjector_eigenmode, isotypicProjector_smul]
  by_cases hm : ℓ = m
  · subst hm
    rw [isotypicProjector_eigenmode_of_ne h, smul_zero]
  · -- P_ℓ v_m = 0 already
    simp [hm]

end Brockian.D5Isotypic
