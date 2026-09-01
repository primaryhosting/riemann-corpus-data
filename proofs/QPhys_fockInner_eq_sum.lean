import Mathlib
import RequestProject.Main

/-!
# A concrete model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are *consistent* with a
nonzero `ℏ`: we build the (algebraic) Fock space of finitely supported sequences `ℕ →₀ ℂ`
with the Bargmann inner product `⟪eₘ, eₙ⟫ = n! δₘₙ`, the annihilation and creation operators,
and the resulting position and momentum operators `X`, `P`, which are symmetric and satisfy
`X P - P X = i` (i.e. `ℏ = 1`).
-/

open scoped ComplexConjugate InnerProductSpace
open Finsupp

namespace QPhys

/-! ## The Bargmann inner product on `ℕ →₀ ℂ` -/

/-- The Bargmann inner product: `⟪f, g⟫ = ∑ₙ conj (f n) * g n * n!`. -/
noncomputable def fockInner (f g : ℕ →₀ ℂ) : ℂ :=
  g.sum fun n c => conj (f n) * c * (n.factorial : ℂ)

lemma fockInner_eq_sum (f g : ℕ →₀ ℂ) {s : Finset ℕ} (hs : g.support ⊆ s) :
    fockInner f g = ∑ n ∈ s, conj (f n) * g n * (n.factorial : ℂ) := by
  refine Finsupp.sum_of_support_subset g hs _ ?_
  intro i _; ring

lemma fockInner_single_right (f : ℕ →₀ ℂ) (n : ℕ) (c : ℂ) :
    fockInner f (Finsupp.single n c) = conj (f n) * c * (n.factorial : ℂ) := by
  rw [fockInner_eq_sum f _ (Finsupp.support_single_subset (a := n) (b := c))]
  simp

lemma fockInner_conj_symm (f g : ℕ →₀ ℂ) : conj (fockInner g f) = fockInner f g := by
  rw [fockInner_eq_sum g f (s := f.support ∪ g.support) Finset.subset_union_left,
      fockInner_eq_sum f g (s := f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring_nf
  simp

lemma fockInner_add_left (f g h : ℕ →₀ ℂ) :
    fockInner (f + g) h = fockInner f h + fockInner g h := by
  simp only [fockInner_eq_sum _ h (le_refl h.support), Finsupp.add_apply, map_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma fockInner_smul_left (f g : ℕ →₀ ℂ) (r : ℂ) :
    fockInner (r • f) g = conj r * fockInner f g := by
  simp only [fockInner_eq_sum _ g (le_refl g.support), Finsupp.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma fockInner_self_re (f : ℕ →₀ ℂ) :
    (fockInner f f).re = ∑ n ∈ f.support, Complex.normSq (f n) * (n.factorial : ℝ) := by
  rw [fockInner_eq_sum f f (le_refl f.support), Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

lemma fockInner_self_nonneg (f : ℕ →₀ ℂ) : 0 ≤ (fockInner f f).re := by
  rw [fockInner_self_re]
  exact Finset.sum_nonneg fun n _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

lemma fockInner_definite (f : ℕ →₀ ℂ) (h : fockInner f f = 0) : f = 0 := by
  have hre : ∑ n ∈ f.support, Complex.normSq (f n) * (n.factorial : ℝ) = 0 := by
    rw [← fockInner_self_re, h]; simp
  have hall : ∀ n ∈ f.support, Complex.normSq (f n) * (n.factorial : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun n _ =>
      mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))).mp hre
  ext n
  by_cases hn : n ∈ f.support
  · have h1 := hall n hn
    have hfact : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hns : Complex.normSq (f n) = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hfact
    simpa using Complex.normSq_eq_zero.mp hns
  · simpa using (Finsupp.notMem_support_iff.mp hn)

/-- The Bargmann inner product core on the algebraic Fock space. -/
noncomputable def fockCore : InnerProductSpace.Core ℂ (ℕ →₀ ℂ) where
  inner := fockInner
  conj_inner_symm := fockInner_conj_symm
  re_inner_nonneg := fockInner_self_nonneg
  add_left := fockInner_add_left
  smul_left := fockInner_smul_left
  definite := fockInner_definite

noncomputable instance instFockNormedAddCommGroup : NormedAddCommGroup (ℕ →₀ ℂ) :=
  fockCore.toNormedAddCommGroup

noncomputable instance instFockInnerProductSpace : InnerProductSpace ℂ (ℕ →₀ ℂ) :=
  InnerProductSpace.ofCore fockCore.toCore

lemma inner_fock (f g : ℕ →₀ ℂ) : ⟪f, g⟫_ℂ = fockInner f g := rfl

/-! ## Creation and annihilation operators -/

/-- Annihilation operator: `eₙ ↦ n • eₙ₋₁`. -/
noncomputable def annih : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => (n : ℂ) • Finsupp.lsingle (n - 1)

/-- Creation operator: `eₙ ↦ eₙ₊₁`. -/
noncomputable def creat : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => Finsupp.lsingle (n + 1)

lemma annih_single (n : ℕ) (c : ℂ) :
    annih (Finsupp.single n c) = Finsupp.single (n - 1) ((n : ℂ) * c) := by
  simp [annih, Finsupp.lsum_single, Finsupp.smul_single]

lemma creat_single (n : ℕ) (c : ℂ) :
    creat (Finsupp.single n c) = Finsupp.single (n + 1) c := by
  simp [creat, Finsupp.lsum_single]

/-- `creat` is the adjoint of `annih`. -/
lemma inner_annih_left (f g : ℕ →₀ ℂ) : ⟪annih f, g⟫_ℂ = ⟪f, creat g⟫_ℂ := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | single n d =>
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂]
      | single m c =>
          rw [annih_single, creat_single, inner_fock, inner_fock, fockInner_single_right,
            fockInner_single_right]
          rcases m with _ | k
          · simp
          · simp only [Nat.add_sub_cancel, Finsupp.single_apply]
            by_cases hnk : n = k
            · subst hnk
              rw [Nat.factorial_succ]
              simp only [if_true, map_mul, Complex.conj_natCast]
              push_cast
              ring
            · rw [if_neg (by omega), if_neg (by omega)]
              simp

/-- `annih` is the adjoint of `creat`. -/
lemma inner_creat_left (f g : ℕ →₀ ℂ) : ⟪creat f, g⟫_ℂ = ⟪f, annih g⟫_ℂ := by
  rw [← inner_conj_symm, ← inner_conj_symm f]
  exact congrArg conj (inner_annih_left g f).symm

/-- The canonical commutation relation `[annih, creat] = 1`. -/
lemma annih_creat_sub_creat_annih (f : ℕ →₀ ℂ) : annih (creat f) - creat (annih f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      simp only [map_add]
      rw [show annih (creat f₁) + annih (creat f₂) - (creat (annih f₁) + creat (annih f₂))
            = (annih (creat f₁) - creat (annih f₁)) + (annih (creat f₂) - creat (annih f₂)) by
          abel, h₁, h₂]
  | single n c =>
      rw [creat_single, annih_single, annih_single, creat_single]
      rcases n with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]
        rw [← Finsupp.single_sub]
        congr 1
        push_cast
        ring

/-! ## Position and momentum -/

/-- Position operator `X = a + a†`. -/
noncomputable def posOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) := annih + creat

/-- Momentum operator `P = (i/2) (a† - a)`, so that `[X, P] = i`. -/
noncomputable def momOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) := (Complex.I / 2) • (creat - annih)

lemma posOp_symmetric (f g : ℕ →₀ ℂ) : ⟪posOp f, g⟫_ℂ = ⟪f, posOp g⟫_ℂ := by
  simp only [posOp, LinearMap.add_apply, inner_add_left, inner_add_right,
    inner_annih_left, inner_creat_left]
  ring

lemma momOp_symmetric (f g : ℕ →₀ ℂ) : ⟪momOp f, g⟫_ℂ = ⟪f, momOp g⟫_ℂ := by
  simp only [momOp, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, inner_annih_left, inner_creat_left]
  simp only [map_div₀, Complex.conj_I, map_ofNat]
  ring

lemma posOp_momOp_commutator (f : ℕ →₀ ℂ) :
    posOp (momOp f) - momOp (posOp f) = Complex.I • f := by
  have hccr : annih (creat f) = creat (annih f) + f := by
    have := annih_creat_sub_creat_annih f
    linear_combination (norm := abel) this
  simp only [posOp, momOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    map_smul, map_sub, map_add, hccr]
  module

/-- The vacuum state `e₀`. -/
noncomputable def vacuum : ℕ →₀ ℂ := Finsupp.single 0 1

lemma inner_vacuum_self : ⟪vacuum, vacuum⟫_ℂ = 1 := by
  rw [inner_fock, vacuum, fockInner_single_right]
  simp

lemma norm_vacuum : ‖vacuum‖ = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) vacuum
  rw [inner_vacuum_self] at h
  have h' : ((‖vacuum‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h.symm
  have h'' : ‖vacuum‖ ^ 2 = 1 := by exact_mod_cast h'
  nlinarith [norm_nonneg vacuum, h'']

/-- The hypotheses of `QPhys.heisenberg_uncertainty` are satisfiable with `ℏ = 1`:
the algebraic Fock space carries symmetric position and momentum operators obeying the
canonical commutation relation at the (normalized) vacuum state. -/
theorem canonical_commutation_satisfiable :
    ∃ (X P : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ)) (psi : ℕ →₀ ℂ),
      (∀ u v, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ) ∧ (∀ u v, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ) ∧
      ‖psi‖ = 1 ∧ X (P psi) - P (X psi) = ((Complex.I * ((1 : ℝ) : ℂ))) • psi := by
  refine ⟨posOp, momOp, vacuum, posOp_symmetric, momOp_symmetric, norm_vacuum, ?_⟩
  rw [posOp_momOp_commutator]
  norm_num

/-- In this concrete model (with `ℏ = 1`), the uncertainty principle applies to the vacuum
state and gives `Δx · Δp ≥ 1/2`. -/
theorem heisenberg_uncertainty_vacuum :
    ‖posOp vacuum - ⟪vacuum, posOp vacuum⟫_ℂ • vacuum‖ *
      ‖momOp vacuum - ⟪vacuum, momOp vacuum⟫_ℂ • vacuum‖ ≥ 1 / 2 := by
  have h := QPhys.heisenberg_uncertainty posOp momOp posOp_symmetric momOp_symmetric 1 vacuum
    norm_vacuum (by rw [posOp_momOp_commutator]; norm_num)
  simpa using h

end QPhys

#print axioms QPhys.canonical_commutation_satisfiable
#print axioms QPhys.heisenberg_uncertainty_vacuum

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QPhys

/-!
## Setting

We work in an arbitrary complex inner product space `E` (the space of states).
Observables are symmetric (formally self-adjoint) `ℂ`-linear operators `X`, `P : E →ₗ[ℂ] E`.

For a state `psi`, the expectation value of an observable `X` is `⟪psi, X psi⟫_ℂ`, and the
standard deviation (the "uncertainty") is

`Δ X = ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖`,

which is the usual `√(⟪X²⟫ - ⟪X⟫²)` for a normalized state.

The only input beyond symmetry is the canonical commutation relation `[X, P] = i ℏ`
evaluated at the state, i.e. `X (P psi) - P (X psi) = (i * ℏ) • psi`.

Mathlib has no uncertainty principle; the proof below is the classical Robertson argument,
whose analytic core is the Cauchy–Schwarz inequality `norm_inner_le_norm`
(`Mathlib.Analysis.InnerProductSpace.Basic`).
-/

section Uncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expectation values of a symmetric operator are real. -/
theorem conj_inner_self_of_symmetric (X : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ) (psi : E) :
    (starRingEnd ℂ) ⟪psi, X psi⟫_ℂ = ⟪psi, X psi⟫_ℂ := by
  rw [inner_conj_symm]
  exact hX psi psi

/-- Expansion of the inner product of two centred vectors. -/
theorem inner_centered (X P : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (psi : E) (hnorm : ‖psi‖ = 1) :
    ⟪X psi - ⟪psi, X psi⟫_ℂ • psi, P psi - ⟪psi, P psi⟫_ℂ • psi⟫_ℂ
      = ⟪psi, X (P psi)⟫_ℂ - ⟪psi, X psi⟫_ℂ * ⟪psi, P psi⟫_ℂ := by
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num
  have ha : (starRingEnd ℂ) ⟪psi, X psi⟫_ℂ = ⟪psi, X psi⟫_ℂ :=
    conj_inner_self_of_symmetric X hX psi
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hpp, ha, hX psi (P psi)]
  rw [hX psi psi]
  ring

/-- The commutator relation forces the imaginary part of the inner product of the two
centred vectors to be `ℏ / 2`. -/
theorem im_inner_centered (X P : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hbar : ℝ) (psi : E) (hnorm : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = ((Complex.I * hbar) : ℂ) • psi) :
    (⟪X psi - ⟪psi, X psi⟫_ℂ • psi, P psi - ⟪psi, P psi⟫_ℂ • psi⟫_ℂ).im = hbar / 2 := by
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num
  set u : E := X psi - ⟪psi, X psi⟫_ℂ • psi
  set v : E := P psi - ⟪psi, P psi⟫_ℂ • psi
  have h1 : ⟪u, v⟫_ℂ = ⟪psi, X (P psi)⟫_ℂ - ⟪psi, X psi⟫_ℂ * ⟪psi, P psi⟫_ℂ :=
    inner_centered X P hX psi hnorm
  have h2 : ⟪v, u⟫_ℂ = ⟪psi, P (X psi)⟫_ℂ - ⟪psi, P psi⟫_ℂ * ⟪psi, X psi⟫_ℂ :=
    inner_centered P X hP psi hnorm
  have hcomm' : ⟪psi, X (P psi)⟫_ℂ - ⟪psi, P (X psi)⟫_ℂ = (Complex.I * hbar : ℂ) := by
    rw [← inner_sub_right, hcomm, inner_smul_right, hpp, mul_one]
  have hkey : ⟪u, v⟫_ℂ - (starRingEnd ℂ) ⟪u, v⟫_ℂ = (Complex.I * hbar : ℂ) := by
    have hconj : (starRingEnd ℂ) ⟪u, v⟫_ℂ = ⟪v, u⟫_ℂ := inner_conj_symm v u
    rw [hconj, h1, h2, ← hcomm']
    ring
  have := congrArg Complex.im hkey
  simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im] at this
  linarith

/-- **Heisenberg uncertainty principle** (Robertson form for the canonical commutator).

Let `E` be a complex inner product space of states, and let `X` and `P` be symmetric
(formally self-adjoint) linear operators — position and momentum — satisfying the canonical
commutation relation `X P psi - P X psi = i ℏ psi` at a normalized state `psi`.

Then the product of the uncertainties `Δx = ‖(X - ⟪X⟫) psi‖` and `Δp = ‖(P - ⟪P⟫) psi‖`
is at least `ℏ / 2`.

The analytic ingredient is Cauchy–Schwarz, `norm_inner_le_norm`. -/
theorem heisenberg_uncertainty (X P : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hbar : ℝ) (psi : E) (hnorm : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = ((Complex.I * hbar) : ℂ) • psi) :
    ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ hbar / 2 := by
  set u : E := X psi - ⟪psi, X psi⟫_ℂ • psi
  set v : E := P psi - ⟪psi, P psi⟫_ℂ • psi
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := im_inner_centered X P hX hP hbar psi hnorm hcomm
  have hcs : ‖(⟪u, v⟫_ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hle : (⟪u, v⟫_ℂ).im ≤ ‖(⟪u, v⟫_ℂ)‖ := Complex.im_le_norm _
  rw [ge_iff_le, ← him]
  exact hle.trans hcs

end Uncertainty

end QPhys

#print axioms QPhys.heisenberg_uncertainty

