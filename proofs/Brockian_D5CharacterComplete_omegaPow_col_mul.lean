/-
  Brockian/D5CharacterComplete.lean

  The FULL irreducible character table of `D₅ = DihedralGroup 5`, together with
  the two orthogonality relations, the dimension identity, and the tie of the
  golden 2-dimensional character to the pentagon spectrum of
  `Brockian.PentagonIsotypic`.

  `Brockian.D5CharacterTable` already carries the character of the natural
  5-dimensional *permutation* representation (a single reducible character).
  This file instead builds the four genuine irreducible characters of `D₅` and
  proves that they form an orthonormal system for the class-function inner
  product, exactly as classical representation theory predicts.

  `D₅` has 4 conjugacy classes — `{1}`, `{r, r⁴}`, `{r², r³}`, `{reflections}`
  — and 4 irreducible characters:
    * `chiTrivial`   (dim 1) : `1, 1, 1, 1`
    * `chiSign`      (dim 1) : `1, 1, 1, −1`
    * `chiGolden`    (dim 2) : `2, φ−1, −φ, 0`
    * `chiConjugate` (dim 2) : `2, −φ, φ−1, 0`
  where `2cos(2π/5) = φ−1` and `2cos(4π/5) = −φ` (see `Brockian.Spectral`).

  ## What is proved
    * `chiTrivial, chiSign, chiGolden, chiConjugate` — the four irreducible
      characters as functions `DihedralGroup 5 → ℂ` (rotation values routed
      through `goldenRot, conjRot : Fin 5 → ℂ`), with their explicit values on
      class representatives (`*_one`, `*_r1`, `*_r2`, `*_sr`).
    * `chiGolden_r`, `golden_char_rotation_class`, `golden_char_eq_two_cos` —
      the golden character on the rotation class is the pentagon adjacency
      eigenvalue `φ−1 = 2cos(2π/5)`, tying this table to
      `Brockian.PentagonIsotypic.adjEigenvalue` and thence to
      `two_cos_two_pi_div_five_eq_golden_sub_one`.
    * `charInner` — the class-function inner product
      `⟨χ,ψ⟩ = (1/|G|) Σ_g χ(g)·conj(ψ(g))`, `|G| = 10`.
    * `row_orthonormal` (FIRST orthogonality relation) — `⟨χ_i, χ_j⟩ = δ_ij`
      for the ten distinct pairs `row_TT … row_GC` (the remaining six equal
      these by symmetry of the real character table).
    * `colInner`, `col_orthogonal` (SECOND orthogonality relation) — the columns
      indexed by the four class representatives are orthogonal, each diagonal
      entry equal to the centralizer order `|G| / |class|` (`10, 5, 5, 2`).
    * `dimension_identity`, `dimension_identity_card` — `Σ dᵢ² = 1+1+4+4 = 10 =
      |D₅|`, the dimensions read off as the character values at `1`.

  ## What is NOT proved
    * We do NOT construct the underlying representations (no `FDRep`/`Rep`
      objects) nor prove *completeness* of the irreducible list through
      Mathlib's abstract representation theory — Mathlib 4.32 lacks a usable
      concrete character-table API.  Instead we exhibit four explicit class
      functions and prove they satisfy BOTH orthogonality relations and the
      dimension identity — the full numerical content of the character table.
      That these are all the irreducibles is the classical corollary (four
      orthonormal class functions on a group with four conjugacy classes span
      the class functions) whose Mathlib-native packaging is left open; the
      missing formal step is `ConjClasses`/`finrank`-level completeness of the
      class-function basis.
    * No `sorry`/`admit`, no new axiom, no `native_decide`, no `maxHeartbeats`
      tuning, no `exact?`.  Verified on AXLE at `lean-4.32.0`.
-/
import Mathlib
import Brockian.D5CharacterTable
import Brockian.PentagonIsotypic
import Brockian.Spectral

open BigOperators
open DihedralGroup
open Brockian.D5Isotypic
open Brockian.D5Representation

namespace Brockian.D5CharacterComplete

/-! ### Conjugation of the fifth root of unity -/

/-- Complex conjugation sends `ω = exp(2πi/5)` to `ω⁻¹`. -/
theorem star_omega : (starRingEnd ℂ) omega = omega⁻¹ := by
  have hconj : (starRingEnd ℂ) omega
      = Complex.exp (-(2 * Real.pi * Complex.I / 5)) := by
    unfold omega
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj, Complex.exp_neg]
  rfl

/-- Complex conjugation sends `ω^k` to `ω^{-k}` (values on the unit circle). -/
theorem star_omegaPow (k : Fin 5) :
    (starRingEnd ℂ) (omegaPow k) = omegaPow (-k) := by
  rw [omegaPow_neg]
  unfold omegaPow
  rw [map_pow, star_omega, inv_pow]

/-! ### Rotation value functions (in `Fin 5`, where the omega calculus lives) -/

/-- Golden rotation value `ω^k + ω^{-k} = 2cos(2πk/5)`. -/
noncomputable def goldenRot (k : Fin 5) : ℂ := omegaPow k + omegaPow (-k)

/-- Conjugate rotation value `ω^{2k} + ω^{-2k} = 2cos(4πk/5)`. -/
noncomputable def conjRot (k : Fin 5) : ℂ := omegaPow (2 * k) + omegaPow (-(2 * k))

/-- The golden rotation value IS the pentagon adjacency eigenvalue. -/
theorem goldenRot_eq_adjEigenvalue (k : Fin 5) :
    goldenRot k = Brockian.PentagonIsotypic.adjEigenvalue k := rfl

theorem goldenRot_zero : goldenRot (0 : Fin 5) = 2 := by
  simp only [goldenRot, neg_zero, omegaPow_zero]; norm_num

theorem conjRot_zero : conjRot (0 : Fin 5) = 2 := by
  simp only [conjRot, mul_zero, neg_zero, omegaPow_zero]; norm_num

theorem goldenRot_one : goldenRot (1 : Fin 5) = ((Real.goldenRatio - 1 : ℝ) : ℂ) := by
  have h : goldenRot 1 = Brockian.PentagonIsotypic.adjEigenvalue 1 := rfl
  rw [h, Brockian.PentagonIsotypic.adjEigenvalue_one]

theorem goldenRot_two : goldenRot (2 : Fin 5) = ((-Real.goldenRatio : ℝ) : ℂ) := by
  have h : goldenRot 2 = Brockian.PentagonIsotypic.adjEigenvalue 2 := rfl
  rw [h, Brockian.PentagonIsotypic.adjEigenvalue_two]

theorem conjRot_one : conjRot (1 : Fin 5) = ((-Real.goldenRatio : ℝ) : ℂ) := by
  have e : (2 * (1 : Fin 5)) = 2 := by decide
  have h : conjRot 1 = Brockian.PentagonIsotypic.adjEigenvalue 2 := by
    show omegaPow (2 * 1) + omegaPow (-(2 * 1)) = omegaPow 2 + omegaPow (-2)
    rw [e]
  rw [h, Brockian.PentagonIsotypic.adjEigenvalue_two]

theorem conjRot_two : conjRot (2 : Fin 5) = ((Real.goldenRatio - 1 : ℝ) : ℂ) := by
  have e : (2 * (2 : Fin 5)) = 4 := by decide
  have h : conjRot 2 = Brockian.PentagonIsotypic.adjEigenvalue 4 := by
    show omegaPow (2 * 2) + omegaPow (-(2 * 2)) = omegaPow 4 + omegaPow (-4)
    rw [e]
  rw [h, Brockian.PentagonIsotypic.adjEigenvalue_four]

/-- Golden rotation values are real (fixed by conjugation). -/
theorem goldenRot_real (k : Fin 5) : (starRingEnd ℂ) (goldenRot k) = goldenRot k := by
  simp only [goldenRot, map_add, star_omegaPow, neg_neg]; rw [add_comm]

/-- Conjugate rotation values are real (fixed by conjugation). -/
theorem conjRot_real (k : Fin 5) : (starRingEnd ℂ) (conjRot k) = conjRot k := by
  simp only [conjRot, map_add, star_omegaPow, neg_neg]; rw [add_comm]

/-! ### The four irreducible characters -/

/-- The trivial character (1-dimensional): `χ(g) = 1`. -/
noncomputable def chiTrivial : DihedralGroup 5 → ℂ := fun _ => 1

/-- The sign character (1-dimensional): `+1` on rotations, `−1` on reflections. -/
noncomputable def chiSign : DihedralGroup 5 → ℂ
  | r _ => 1
  | sr _ => -1

/-- The golden 2-dimensional character `ρ₁`: `goldenRot k` on `rᵏ`, `0` on
reflections. -/
noncomputable def chiGolden : DihedralGroup 5 → ℂ
  | r k => goldenRot k
  | sr _ => 0

/-- The conjugate 2-dimensional character `ρ₂`: `conjRot k` on `rᵏ`, `0` on
reflections. -/
noncomputable def chiConjugate : DihedralGroup 5 → ℂ
  | r k => conjRot k
  | sr _ => 0

/-! #### Values on the constructors (`Fin 5` indices) -/

@[simp] theorem chiTrivial_r (k : Fin 5) : chiTrivial (r k) = 1 := rfl
@[simp] theorem chiTrivial_sr (k : Fin 5) : chiTrivial (sr k) = 1 := rfl
@[simp] theorem chiSign_r (k : Fin 5) : chiSign (r k) = 1 := rfl
@[simp] theorem chiSign_sr (k : Fin 5) : chiSign (sr k) = -1 := rfl
@[simp] theorem chiGolden_r (k : Fin 5) : chiGolden (r k) = goldenRot k := rfl
@[simp] theorem chiGolden_sr (k : Fin 5) : chiGolden (sr k) = 0 := rfl
@[simp] theorem chiConjugate_r (k : Fin 5) : chiConjugate (r k) = conjRot k := rfl
@[simp] theorem chiConjugate_sr (k : Fin 5) : chiConjugate (sr k) = 0 := rfl

/-- The identity is the rotation by `0`, phrased with a `Fin 5` index. -/
theorem one_eq_r0 : (1 : DihedralGroup 5) = r (0 : Fin 5) := one_def

/-! #### The golden tie to the pentagon cosine spectrum -/

/-- The golden character's value on the rotation class `{r, r⁴}` is `φ − 1`. -/
theorem golden_char_rotation_class :
    chiGolden (r (1 : Fin 5)) = ((Real.goldenRatio - 1 : ℝ) : ℂ) := goldenRot_one

/-- Explicit trigonometric form: `χ_golden(r) = 2cos(2π/5)`, tying the table to
`Brockian.CycleSpectrumFamily.two_cos_two_pi_div_five_eq_golden_sub_one`
(via `Brockian.PentagonIsotypic.adjEigenvalue_eq_two_cos`). -/
theorem golden_char_eq_two_cos :
    chiGolden (r (1 : Fin 5))
      = ((2 * Real.cos (2 * Real.pi * ((1 : Fin 5).val : ℝ) / 5) : ℝ) : ℂ) := by
  rw [chiGolden_r, goldenRot_eq_adjEigenvalue,
    Brockian.PentagonIsotypic.adjEigenvalue_eq_two_cos]

/-! ### The characters are real-valued (fixed by conjugation) -/

theorem chiTrivial_real (g : DihedralGroup 5) :
    (starRingEnd ℂ) (chiTrivial g) = chiTrivial g := by
  show (starRingEnd ℂ) (1 : ℂ) = 1
  rw [map_one]

theorem chiSign_real (g : DihedralGroup 5) :
    (starRingEnd ℂ) (chiSign g) = chiSign g := by
  cases g with
  | r k => show (starRingEnd ℂ) (1 : ℂ) = 1; rw [map_one]
  | sr k => show (starRingEnd ℂ) (-1 : ℂ) = -1; rw [map_neg, map_one]

theorem chiGolden_real (g : DihedralGroup 5) :
    (starRingEnd ℂ) (chiGolden g) = chiGolden g := by
  cases g with
  | r k => exact goldenRot_real k
  | sr k => show (starRingEnd ℂ) (0 : ℂ) = 0; rw [map_zero]

theorem chiConjugate_real (g : DihedralGroup 5) :
    (starRingEnd ℂ) (chiConjugate g) = chiConjugate g := by
  cases g with
  | r k => exact conjRot_real k
  | sr k => show (starRingEnd ℂ) (0 : ℂ) = 0; rw [map_zero]

/-! ### Summing over `DihedralGroup 5`: rotations plus reflections -/

/-- Any sum over `D₅` splits into the five rotations and the five reflections. -/
theorem sum_dihedral5 (F : DihedralGroup 5 → ℂ) :
    ∑ g : DihedralGroup 5, F g
      = (∑ k : Fin 5, F (r k)) + (∑ k : Fin 5, F (sr k)) := by
  rw [← Equiv.sum_comp equivSum.symm F, Fintype.sum_sum_type]
  rfl

/-! ### Geometric-sum engine for the rotation blocks -/

/-- Column-wise multiplicativity: `ω^{ak}·ω^{bk} = ω^{(a+b)k}`. -/
theorem omegaPow_col_mul (a b k : Fin 5) :
    omegaPow (a * k) * omegaPow (b * k) = omegaPow ((a + b) * k) := by
  rw [← omegaPow_add, ← add_mul]

/-- Sum of a "binomial character" `ω^{ak} + ω^{bk}` over the five rotations. -/
theorem sum_omega_binom (a b : Fin 5) :
    ∑ k : Fin 5, (omegaPow (a * k) + omegaPow (b * k))
      = (if a = 0 then (5 : ℂ) else 0) + (if b = 0 then (5 : ℂ) else 0) := by
  rw [Finset.sum_add_distrib, sum_omegaPow a, sum_omegaPow b]

/-- Sum of a product of two binomial characters over the five rotations. -/
theorem sum_omega_binom_prod (a b c d : Fin 5) :
    ∑ k : Fin 5,
        (omegaPow (a * k) + omegaPow (b * k)) * (omegaPow (c * k) + omegaPow (d * k))
      = (if a + c = 0 then (5 : ℂ) else 0) + (if a + d = 0 then (5 : ℂ) else 0)
        + (if b + c = 0 then (5 : ℂ) else 0) + (if b + d = 0 then (5 : ℂ) else 0) := by
  have hexp : ∀ k : Fin 5,
      (omegaPow (a * k) + omegaPow (b * k)) * (omegaPow (c * k) + omegaPow (d * k))
        = omegaPow ((a + c) * k) + omegaPow ((a + d) * k)
          + omegaPow ((b + c) * k) + omegaPow ((b + d) * k) := by
    intro k
    rw [add_mul, mul_add, mul_add, omegaPow_col_mul, omegaPow_col_mul,
      omegaPow_col_mul, omegaPow_col_mul]
    ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_omegaPow (a + c), sum_omegaPow (a + d), sum_omegaPow (b + c),
    sum_omegaPow (b + d)]

/-! #### The golden / conjugate rotation values in column form -/

theorem goldenRot_col (k : Fin 5) :
    goldenRot k = omegaPow (1 * k) + omegaPow ((-1) * k) := by
  show omegaPow k + omegaPow (-k) = omegaPow (1 * k) + omegaPow ((-1) * k)
  rw [one_mul, neg_one_mul]

theorem conjRot_col (k : Fin 5) :
    conjRot k = omegaPow (2 * k) + omegaPow ((-2) * k) := by
  show omegaPow (2 * k) + omegaPow (-(2 * k)) = omegaPow (2 * k) + omegaPow ((-2) * k)
  rw [neg_mul]

/-! #### The five rotation-block sums -/

theorem rot_G_sum : ∑ k : Fin 5, chiGolden (r k) = 0 := by
  simp only [chiGolden_r]
  simp_rw [goldenRot_col]
  rw [sum_omega_binom 1 (-1), if_neg (by decide), if_neg (by decide), add_zero]

theorem rot_C_sum : ∑ k : Fin 5, chiConjugate (r k) = 0 := by
  simp only [chiConjugate_r]
  simp_rw [conjRot_col]
  rw [sum_omega_binom 2 (-2), if_neg (by decide), if_neg (by decide), add_zero]

theorem rot_GG : ∑ k : Fin 5, chiGolden (r k) * chiGolden (r k) = 10 := by
  simp only [chiGolden_r]
  simp_rw [goldenRot_col]
  rw [sum_omega_binom_prod 1 (-1) 1 (-1), if_neg (by decide), if_pos (by decide),
    if_pos (by decide), if_neg (by decide)]
  norm_num

theorem rot_GC : ∑ k : Fin 5, chiGolden (r k) * chiConjugate (r k) = 0 := by
  simp only [chiGolden_r, chiConjugate_r]
  simp_rw [goldenRot_col, conjRot_col]
  rw [sum_omega_binom_prod 1 (-1) 2 (-2), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide)]
  norm_num

theorem rot_CC : ∑ k : Fin 5, chiConjugate (r k) * chiConjugate (r k) = 10 := by
  simp only [chiConjugate_r]
  simp_rw [conjRot_col]
  rw [sum_omega_binom_prod 2 (-2) 2 (-2), if_neg (by decide), if_pos (by decide),
    if_pos (by decide), if_neg (by decide)]
  norm_num

/-! ### The class-function inner product and ROW orthogonality -/

/-- The unnormalized character pairing `Σ_g χ(g)·ψ(g)`. -/
noncomputable def pairSum (χ ψ : DihedralGroup 5 → ℂ) : ℂ :=
  ∑ g : DihedralGroup 5, χ g * ψ g

theorem pairSum_split (χ ψ : DihedralGroup 5 → ℂ) :
    pairSum χ ψ
      = (∑ k : Fin 5, χ (r k) * ψ (r k)) + (∑ k : Fin 5, χ (sr k) * ψ (sr k)) := by
  unfold pairSum
  rw [sum_dihedral5 (fun g => χ g * ψ g)]

/-- The class-function inner product
`⟨χ, ψ⟩ = (1/|G|) Σ_g χ(g)·conj(ψ(g))`, with `|G| = 10`. -/
noncomputable def charInner (χ ψ : DihedralGroup 5 → ℂ) : ℂ :=
  (10 : ℂ)⁻¹ * ∑ g : DihedralGroup 5, χ g * (starRingEnd ℂ) (ψ g)

/-- For a real-valued second character the conjugation is inert. -/
theorem charInner_eq_pairSum (χ ψ : DihedralGroup 5 → ℂ)
    (hψ : ∀ g, (starRingEnd ℂ) (ψ g) = ψ g) :
    charInner χ ψ = (10 : ℂ)⁻¹ * pairSum χ ψ := by
  unfold charInner pairSum
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [hψ]

theorem row_TT : charInner chiTrivial chiTrivial = 1 := by
  rw [charInner_eq_pairSum _ _ chiTrivial_real, pairSum_split]
  have hr : ∑ k : Fin 5, chiTrivial (r k) * chiTrivial (r k) = 5 := by
    simp only [Fin.sum_univ_five, chiTrivial_r]; norm_num
  have hs : ∑ k : Fin 5, chiTrivial (sr k) * chiTrivial (sr k) = 5 := by
    simp only [Fin.sum_univ_five, chiTrivial_sr]; norm_num
  rw [hr, hs]; norm_num

theorem row_SS : charInner chiSign chiSign = 1 := by
  rw [charInner_eq_pairSum _ _ chiSign_real, pairSum_split]
  have hr : ∑ k : Fin 5, chiSign (r k) * chiSign (r k) = 5 := by
    simp only [Fin.sum_univ_five, chiSign_r]; norm_num
  have hs : ∑ k : Fin 5, chiSign (sr k) * chiSign (sr k) = 5 := by
    simp only [Fin.sum_univ_five, chiSign_sr]; norm_num
  rw [hr, hs]; norm_num

theorem row_GG : charInner chiGolden chiGolden = 1 := by
  rw [charInner_eq_pairSum _ _ chiGolden_real, pairSum_split]
  have hs : ∑ k : Fin 5, chiGolden (sr k) * chiGolden (sr k) = 0 := by
    simp [chiGolden_sr]
  rw [rot_GG, hs]; norm_num

theorem row_CC : charInner chiConjugate chiConjugate = 1 := by
  rw [charInner_eq_pairSum _ _ chiConjugate_real, pairSum_split]
  have hs : ∑ k : Fin 5, chiConjugate (sr k) * chiConjugate (sr k) = 0 := by
    simp [chiConjugate_sr]
  rw [rot_CC, hs]; norm_num

theorem row_TS : charInner chiTrivial chiSign = 0 := by
  rw [charInner_eq_pairSum _ _ chiSign_real, pairSum_split]
  have hr : ∑ k : Fin 5, chiTrivial (r k) * chiSign (r k) = 5 := by
    simp only [Fin.sum_univ_five, chiTrivial_r, chiSign_r]; norm_num
  have hs : ∑ k : Fin 5, chiTrivial (sr k) * chiSign (sr k) = -5 := by
    simp only [Fin.sum_univ_five, chiTrivial_sr, chiSign_sr]; norm_num
  rw [hr, hs]; norm_num

theorem row_TG : charInner chiTrivial chiGolden = 0 := by
  rw [charInner_eq_pairSum _ _ chiGolden_real, pairSum_split]
  have hr : ∑ k : Fin 5, chiTrivial (r k) * chiGolden (r k) = 0 := by
    simp only [chiTrivial_r, one_mul]; exact rot_G_sum
  have hs : ∑ k : Fin 5, chiTrivial (sr k) * chiGolden (sr k) = 0 := by
    simp [chiGolden_sr]
  rw [hr, hs]; norm_num

theorem row_TC : charInner chiTrivial chiConjugate = 0 := by
  rw [charInner_eq_pairSum _ _ chiConjugate_real, pairSum_split]
  have hr : ∑ k : Fin 5, chiTrivial (r k) * chiConjugate (r k) = 0 := by
    simp only [chiTrivial_r, one_mul]; exact rot_C_sum
  have hs : ∑ k : Fin 5, chiTrivial (sr k) * chiConjugate (sr k) = 0 := by
    simp [chiConjugate_sr]
  rw [hr, hs]; norm_num

theorem row_SG : charInner chiSign chiGolden = 0 := by
  rw [charInner_eq_pairSum _ _ chiGolden_real, pairSum_split]
  have hr : ∑ k : Fin 5, chiSign (r k) * chiGolden (r k) = 0 := by
    simp only [chiSign_r, one_mul]; exact rot_G_sum
  have hs : ∑ k : Fin 5, chiSign (sr k) * chiGolden (sr k) = 0 := by
    simp [chiGolden_sr]
  rw [hr, hs]; norm_num

theorem row_SC : charInner chiSign chiConjugate = 0 := by
  rw [charInner_eq_pairSum _ _ chiConjugate_real, pairSum_split]
  have hr : ∑ k : Fin 5, chiSign (r k) * chiConjugate (r k) = 0 := by
    simp only [chiSign_r, one_mul]; exact rot_C_sum
  have hs : ∑ k : Fin 5, chiSign (sr k) * chiConjugate (sr k) = 0 := by
    simp [chiConjugate_sr]
  rw [hr, hs]; norm_num

theorem row_GC : charInner chiGolden chiConjugate = 0 := by
  rw [charInner_eq_pairSum _ _ chiConjugate_real, pairSum_split]
  have hs : ∑ k : Fin 5, chiGolden (sr k) * chiConjugate (sr k) = 0 := by
    simp [chiConjugate_sr]
  rw [rot_GC, hs]; norm_num

/-- **First orthogonality relation (row orthonormality).**  The four irreducible
characters of `D₅` form an orthonormal system: `⟨χ_i, χ_j⟩ = δ_ij`.  (The six
omitted pairs equal these by symmetry of the real character table.) -/
theorem row_orthonormal :
    charInner chiTrivial chiTrivial = 1 ∧ charInner chiSign chiSign = 1 ∧
    charInner chiGolden chiGolden = 1 ∧ charInner chiConjugate chiConjugate = 1 ∧
    charInner chiTrivial chiSign = 0 ∧ charInner chiTrivial chiGolden = 0 ∧
    charInner chiTrivial chiConjugate = 0 ∧ charInner chiSign chiGolden = 0 ∧
    charInner chiSign chiConjugate = 0 ∧ charInner chiGolden chiConjugate = 0 :=
  ⟨row_TT, row_SS, row_GG, row_CC, row_TS, row_TG, row_TC, row_SG, row_SC, row_GC⟩

/-! ### COLUMN orthogonality (second relation) -/

/-- The column pairing at two group elements: `Σ_i χ_i(g)·conj(χ_i(h))` summed
over the four irreducible characters. -/
noncomputable def colInner (g h : DihedralGroup 5) : ℂ :=
  chiTrivial g * (starRingEnd ℂ) (chiTrivial h)
    + chiSign g * (starRingEnd ℂ) (chiSign h)
    + chiGolden g * (starRingEnd ℂ) (chiGolden h)
    + chiConjugate g * (starRingEnd ℂ) (chiConjugate h)

/-- Golden-ratio square identity, cast to `ℂ`: `φ² = φ + 1`. -/
theorem goldenRatio_sq_complex :
    (Real.goldenRatio : ℂ) ^ 2 = (Real.goldenRatio : ℂ) + 1 := by
  exact_mod_cast Real.goldenRatio_sq

/-- Column `{1}` self-pairing: `Σ_i dᵢ² = 10 = |G|`. -/
theorem colInner_one_one : colInner 1 1 = 10 := by
  simp only [colInner, one_eq_r0, chiTrivial_r, chiSign_r, chiGolden_r,
    chiConjugate_r, goldenRot_zero, conjRot_zero, map_one, map_ofNat]
  norm_num

/-- Column `{r,r⁴}` self-pairing: `Σ_i |χ_i(r)|² = 5 = |G|/2`. -/
theorem colInner_r1_r1 : colInner (r (1 : Fin 5)) (r (1 : Fin 5)) = 5 := by
  simp only [colInner, chiTrivial_r, chiSign_r, chiGolden_r, chiConjugate_r,
    goldenRot_one, conjRot_one, Complex.conj_ofReal, map_one, map_sub, map_neg,
    Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one]
  linear_combination 2 * goldenRatio_sq_complex

/-- Column `{r²,r³}` self-pairing: `Σ_i |χ_i(r²)|² = 5 = |G|/2`. -/
theorem colInner_r2_r2 : colInner (r (2 : Fin 5)) (r (2 : Fin 5)) = 5 := by
  simp only [colInner, chiTrivial_r, chiSign_r, chiGolden_r, chiConjugate_r,
    goldenRot_two, conjRot_two, Complex.conj_ofReal, map_one, map_sub, map_neg,
    Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one]
  linear_combination 2 * goldenRatio_sq_complex

/-- Column `{reflections}` self-pairing: `Σ_i |χ_i(sr)|² = 2 = |G|/5`. -/
theorem colInner_sr0_sr0 : colInner (sr (0 : Fin 5)) (sr (0 : Fin 5)) = 2 := by
  simp only [colInner, chiTrivial_sr, chiSign_sr, chiGolden_sr, chiConjugate_sr,
    map_one, map_neg, map_zero]
  norm_num

theorem colInner_one_r1 : colInner 1 (r (1 : Fin 5)) = 0 := by
  simp only [colInner, one_eq_r0, chiTrivial_r, chiSign_r, chiGolden_r,
    chiConjugate_r, goldenRot_zero, conjRot_zero, goldenRot_one, conjRot_one,
    Complex.conj_ofReal, map_one, map_ofNat]
  push_cast
  ring

theorem colInner_one_r2 : colInner 1 (r (2 : Fin 5)) = 0 := by
  simp only [colInner, one_eq_r0, chiTrivial_r, chiSign_r, chiGolden_r,
    chiConjugate_r, goldenRot_zero, conjRot_zero, goldenRot_two, conjRot_two,
    Complex.conj_ofReal, map_one, map_ofNat]
  push_cast
  ring

theorem colInner_one_sr0 : colInner 1 (sr (0 : Fin 5)) = 0 := by
  simp only [colInner, one_eq_r0, chiTrivial_r, chiSign_r, chiGolden_r,
    chiConjugate_r, goldenRot_zero, conjRot_zero, chiTrivial_sr, chiSign_sr,
    chiGolden_sr, chiConjugate_sr, map_one, map_neg, map_zero, map_ofNat]
  norm_num

theorem colInner_r1_r2 : colInner (r (1 : Fin 5)) (r (2 : Fin 5)) = 0 := by
  simp only [colInner, chiTrivial_r, chiSign_r, chiGolden_r, chiConjugate_r,
    goldenRot_one, conjRot_one, goldenRot_two, conjRot_two, Complex.conj_ofReal,
    map_one, map_sub, map_neg, Complex.ofReal_sub, Complex.ofReal_neg,
    Complex.ofReal_one]
  linear_combination (-2) * goldenRatio_sq_complex

theorem colInner_r1_sr0 : colInner (r (1 : Fin 5)) (sr (0 : Fin 5)) = 0 := by
  simp only [colInner, chiTrivial_r, chiSign_r, chiGolden_r, chiConjugate_r,
    goldenRot_one, conjRot_one, chiTrivial_sr, chiSign_sr, chiGolden_sr,
    chiConjugate_sr, Complex.conj_ofReal, map_one, map_neg, map_zero]
  ring

theorem colInner_r2_sr0 : colInner (r (2 : Fin 5)) (sr (0 : Fin 5)) = 0 := by
  simp only [colInner, chiTrivial_r, chiSign_r, chiGolden_r, chiConjugate_r,
    goldenRot_two, conjRot_two, chiTrivial_sr, chiSign_sr, chiGolden_sr,
    chiConjugate_sr, Complex.conj_ofReal, map_one, map_neg, map_zero]
  ring

/-- **Second orthogonality relation (column orthogonality).**  The columns of
the character table indexed by the four class representatives `1, r, r², sr` are
orthogonal, with each diagonal entry equal to the centralizer order
`|G|/|class| = 10, 5, 5, 2`. -/
theorem col_orthogonal :
    colInner 1 1 = 10 ∧ colInner (r (1 : Fin 5)) (r (1 : Fin 5)) = 5 ∧
    colInner (r (2 : Fin 5)) (r (2 : Fin 5)) = 5 ∧
    colInner (sr (0 : Fin 5)) (sr (0 : Fin 5)) = 2 ∧
    colInner 1 (r (1 : Fin 5)) = 0 ∧ colInner 1 (r (2 : Fin 5)) = 0 ∧
    colInner 1 (sr (0 : Fin 5)) = 0 ∧
    colInner (r (1 : Fin 5)) (r (2 : Fin 5)) = 0 ∧
    colInner (r (1 : Fin 5)) (sr (0 : Fin 5)) = 0 ∧
    colInner (r (2 : Fin 5)) (sr (0 : Fin 5)) = 0 :=
  ⟨colInner_one_one, colInner_r1_r1, colInner_r2_r2, colInner_sr0_sr0,
    colInner_one_r1, colInner_one_r2, colInner_one_sr0, colInner_r1_r2,
    colInner_r1_sr0, colInner_r2_sr0⟩

/-! ### The dimension identity -/

theorem chiTrivial_one : chiTrivial (1 : DihedralGroup 5) = 1 := rfl

theorem chiSign_one : chiSign (1 : DihedralGroup 5) = 1 := by
  rw [one_eq_r0, chiSign_r]

theorem chiGolden_one : chiGolden (1 : DihedralGroup 5) = 2 := by
  rw [one_eq_r0, chiGolden_r]; exact goldenRot_zero

theorem chiConjugate_one : chiConjugate (1 : DihedralGroup 5) = 2 := by
  rw [one_eq_r0, chiConjugate_r]; exact conjRot_zero

/-- **`Σ dᵢ² = 1² + 1² + 2² + 2² = 10`**, the dimensions being the character
values at the identity. -/
theorem dimension_identity :
    (chiTrivial 1) ^ 2 + (chiSign 1) ^ 2 + (chiGolden 1) ^ 2
        + (chiConjugate 1) ^ 2 = 10 := by
  rw [chiTrivial_one, chiSign_one, chiGolden_one, chiConjugate_one]
  norm_num

/-- The dimension identity equals the group order `|D₅| = 10`. -/
theorem dimension_identity_card :
    (chiTrivial 1) ^ 2 + (chiSign 1) ^ 2 + (chiGolden 1) ^ 2
        + (chiConjugate 1) ^ 2 = (Fintype.card (DihedralGroup 5) : ℂ) := by
  rw [dimension_identity, DihedralGroup.card]
  norm_num

end Brockian.D5CharacterComplete
