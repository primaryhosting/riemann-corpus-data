import Mathlib

namespace Brockian.RiemannScaffold

open Complex

/-! ## Part 1 — The ξ-bridge (UNCONDITIONAL, genuinely proved) -/

/-- **The Riemann ξ-function** in the classical normalization
`ξ(s) = s (s-1) Λ(s)`, where `Λ = completedRiemannZeta` is Mathlib's completed
zeta `π^(-s/2) Γ(s/2) ζ(s)`.  The `s (s-1)` factor is the classical one that (over
`ℂ`) cancels the simple poles of `Λ` at `s = 0, 1`. -/
noncomputable def riemannXi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta s

/-- **The Γ-factor is nonvanishing away from `0` and the trivial-zero lattice.**
`Gammaℝ s = π^(-s/2) Γ(s/2)`; the `cpow` factor is never zero, and `Γ(s/2) ≠ 0`
exactly when `s/2 ∉ {0, -1, -2, …}`, i.e. `s ∉ {0, -2, -4, …}`.  We exclude `s = 0`
and the trivial-zero lattice `{-2(n+1) : n ∈ ℕ}` and get `Gammaℝ s ≠ 0`. -/
theorem Gammaℝ_ne_zero_of_nontrivial {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) : s.Gammaℝ ≠ 0 := by
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  · apply Complex.Gamma_ne_zero
    intro m hm
    -- hm : s / 2 = -↑m  ⇒  s = -2 * m
    have hs : s = -2 * (m : ℂ) := by linear_combination 2 * hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp only [Nat.cast_zero, mul_zero] at hs
      exact hs0 hs
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      exact htriv ⟨k, by push_cast at hs ⊢; linear_combination hs⟩

/-- **Nontrivial ζ-zero ⇒ ξ-zero (UNCONDITIONAL).**  If `ζ(s) = 0` at a point that
is not the trivial-zero lattice and not `s = 1`, then `ξ(s) = 0`.  The real work:
`s ≠ 0` (since `ζ(0) = -1/2`), the Γ-factor is nonvanishing there, and
`ζ = Λ / Gammaℝ` forces `Λ(s) = 0`, hence `ξ(s) = s (s-1) · 0 = 0`. -/
theorem riemannXi_eq_zero_of_nontrivial_zeta_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (_hs1 : s ≠ 1) : riemannXi s = 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hΓ : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_nontrivial hs0 htriv
  have hΛ : completedRiemannZeta s = 0 := by
    have hdef : riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
      riemannZeta_def_of_ne_zero hs0
    rw [hz] at hdef
    exact (div_eq_zero_iff.mp hdef.symm).resolve_right hΓ
  unfold riemannXi
  rw [hΛ]
  ring

/-- **The ξ-bridge (UNCONDITIONAL).**  If every zero of `ξ` other than the two
lattice artifacts `s = 0, 1` (which come from the explicit `s (s-1)` factor over
`ℂ`, not from `Λ`) lies on the critical line, then the Riemann Hypothesis holds
as Mathlib states it.

The hypothesis is the honest ξ-form of RH: it is NOT assumed, and it is not
vacuous — it is exactly the (open) assertion that the nontrivial zeros lie on the
line.  The implication does real work through
`riemannXi_eq_zero_of_nontrivial_zeta_zero`. -/
theorem RiemannHypothesis_of_forall_xi_zero
    (h : ∀ s : ℂ, riemannXi s = 0 → s ≠ 0 → s ≠ 1 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  exact h s (riemannXi_eq_zero_of_nontrivial_zeta_zero hz htriv hs1) hs0 hs1

/-! ## Part 2 — The Brockian conditional chain (CONDITIONAL, rung OPEN)

This part formalizes the *Hilbert–Pólya shape* of the Brockian program: a
densely-defined **symmetric** (formal self-adjoint) operator on a Hilbert space
whose point spectrum realizes the nontrivial zeros through `t = -i(s - 1/2)`.
The implication `BrockianSystem → RiemannHypothesis` is proved for real; but
**no `BrockianSystem` is constructed** — constructing one is RH-strength
(Gate-0, see the note at the end). -/

/-- **Symmetric operators have real eigenvalues (UNCONDITIONAL).**  For a formal
self-adjoint (symmetric) `LinearPMap` `T`, any eigenvalue `μ` attached to a
nonzero eigenvector is real.  Proof: `⟪T v, v⟫ = ⟪v, T v⟫` (symmetry) becomes
`conj μ · ⟪v,v⟫ = μ · ⟪v,v⟫`; cancel `⟪v,v⟫ ≠ 0` to get `conj μ = μ`.

This is the theorem that *grounds* the `spectrum_real` obligation of a
`BrockianSystem`: a genuine symmetric operator discharges it on its point
spectrum.  Reality is therefore not an ex-falso gadget — it is the real spectral
content of symmetry. -/
theorem symmetric_eigenvalue_im_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T)
    {μ : ℂ} {v : T.domain} (hv : (v : H) ≠ 0)
    (heig : (T v : H) = μ • (v : H)) : μ.im = 0 := by
  have hkey := hsymm v v
  rw [heig, inner_smul_left, inner_smul_right] at hkey
  have hvv : inner ℂ (v : H) (v : H) ≠ 0 := inner_self_ne_zero.mpr hv
  have hconj : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hvv hkey
  exact Complex.conj_eq_iff_im.mp hconj

/-- **A `BrockianSystem`** — the Hilbert–Pólya operator-theoretic hypothesis, made
into an honest bundle of obligations over a Hilbert space `H`.

Fields:
* `T` — a **densely-defined, unbounded** operator, modelled as a partial linear
  map `H →ₗ.[ℂ] H` (a `LinearPMap`, *not* a bounded `H →L[ℂ] H`; the bounded
  route is spectrally vacuous for this problem).
* `dense_domain` — `T` is densely defined.
* `symm` — `T` is **symmetric** (formal self-adjoint, `T.IsFormalAdjoint T`).
* `spectrum_real` — the **explicit spectral-reality obligation**: every eigenvalue
  of `T` (nonzero eigenvector) is real.  (Grounded by `symm` via
  `symmetric_eigenvalue_im_zero`; carried as an explicit field so the obligation
  is visible.)
* `eigen_of_zero` — the **zeros ↔ spectrum** correspondence: every nontrivial
  zero `s` of `ζ` is realized as an eigenvalue `t = -i(s - 1/2)` of `T`.

No such system is exhibited here; see the Gate-0 note. -/
structure BrockianSystem (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- the densely-defined unbounded operator (partial linear map, not bounded). -/
  T : H →ₗ.[ℂ] H
  /-- `T` is densely defined. -/
  dense_domain : Dense (T.domain : Set H)
  /-- `T` is symmetric (formal self-adjoint). -/
  symm : T.IsFormalAdjoint T
  /-- **Spectral-reality obligation**: eigenvalues of `T` are real. -/
  spectrum_real : ∀ (μ : ℂ) (v : T.domain),
    (v : H) ≠ 0 → (T v : H) = μ • (v : H) → μ.im = 0
  /-- **Zeros ↔ spectrum**: each nontrivial `ζ`-zero `s` is an eigenvalue
  `t = -i(s - 1/2)` of `T`, on a nonzero eigenvector. -/
  eigen_of_zero : ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 → ∃ v : T.domain, (v : H) ≠ 0 ∧
      (T v : H) = (-Complex.I * (s - 1 / 2)) • (v : H)

/-- **`RH_of_BrockianSystem` — the Brockian conditional (CONDITIONAL, rung OPEN).**
If a `BrockianSystem` exists on some Hilbert space, then the Riemann Hypothesis
holds (as Mathlib states it).

The implication does genuine work: for a nontrivial zero `s`, the correspondence
`eigen_of_zero` produces an eigenvector at eigenvalue `t = -i(s - 1/2)`;
`spectrum_real` forces `t` real, i.e. `t.im = 0`; and the complex algebra of
`t = -i(s - 1/2)` turns `t.im = 0` into `s.re = 1/2`.

This is a *conditional* result.  `BrockianSystem` is **not shown instantiable**
(Gate-0). -/
theorem RH_of_BrockianSystem {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : BrockianSystem H) : RiemannHypothesis := by
  intro s hz htriv hs1
  obtain ⟨v, hv, heig⟩ := B.eigen_of_zero s hz htriv hs1
  -- the eigenvalue realizing the zero
  have him : (-Complex.I * (s - 1 / 2)).im = 0 := B.spectrum_real _ v hv heig
  -- turn `t = -i(s - 1/2)`, `t.im = 0` into `Re s = 1/2`
  have h2 : ((1 : ℂ) / 2).im = 0 := by simp
  have h3 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.sub_re, Complex.sub_im, h2, h3] at him
  linarith

/-! ### Gate-0 note (honesty register)

`BrockianSystem` is **NOT shown instantiable** in this file: no term of type
`BrockianSystem H` is constructed for any `H`.  This is deliberate and is the
crux of the honesty contract — exhibiting such a symmetric operator whose point
spectrum encodes the nontrivial zeros *is itself of Riemann-Hypothesis strength*
(indeed `RH_of_BrockianSystem` shows any instance would prove RH outright).

Concretely, the contrapositive of `RH_of_BrockianSystem` says: **if RH is false,
then no Hilbert space carries a `BrockianSystem`.**  So the type is at least as
hard to inhabit as RH is to prove.  We therefore leave it as an OPEN schema and
claim only the *conditional* `RH_of_BrockianSystem` and the *unconditional*
ξ-bridge of Part 1.  RH itself is **not** claimed. -/

end Brockian.RiemannScaffold
