/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header is repeated below as a module docstring: Lean 4 requires `import`
commands to come before any doc comment.)
-/

import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Mathlib contains no theory of curves, divisors, genus or Riemann–Roch, so the
whole framework is developed here from scratch, in the classical
function-field (Weil) formulation.

A smooth projective geometrically connected curve over a field `k` is encoded by
its function field: a field `F ⊇ k` together with a family of normalized
valuations `val p : F → ℤ ∪ {∞}` indexed by the closed points `p : P` of the
curve, subject to the axioms in `Math2.FFBase` and `Math2.FFCurve`.  From these
we build

* `U`, the local filtration, and `degPlace p`, the degree of a point;
* `RRSpace D = L(D)` and `ell D = ℓ(D) = dim_k L(D)`;
* the adeles `AdeleSpace`, the subspaces `ADiv D = A(D)`, the diagonal `FDiag`,
  the cohomology group `H1 D = A/(A(D) + F)` and its dimension `index D = i(D)`;
* the genus `genus = i(0) = dim_k H¹(X, 𝒪_X)` and `degDiv D = deg D`.

The main *unconditional* theorem proved here is Riemann–Roch in index form,
`Math2.FFBase.riemann_roch_index`:

  `ℓ(D) - i(D) = deg D + 1 - g`   for every divisor `D`,

together with the finite dimensionality of `L(D)` and `H¹(D)`.  It is proved by
induction over divisors from the four term exact sequence

  `0 → L(D)/L(D-p) → A(D)/A(D-p) → H¹(D-p) → H¹(D) → 0`

(`Math2.FFBase.step_core`), whose middle term has dimension `deg p`.

The headline statement `Math2.riemann_roch_curve` is the usual form
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`; here `K` is a canonical divisor, which is
characterised — and supplied as an explicit hypothesis — by Serre duality
`i(D) = ℓ(K - D)`.  Consequences `ℓ(K) = g` and `deg K = 2g - 2` are derived, as
is Riemann's inequality `ℓ(D) ≥ deg D + 1 - g` (unconditional) and the vanishing
`ℓ(D) = 0` for `deg D < 0`.
-/

namespace Math2

universe u v w

/-!
## The axioms of an algebraic function field of one variable

A smooth projective geometrically connected curve `X` over a field `k` is the
same thing as its function field `F = k(X)`, an algebraic function field of one
variable over `k`.  Under this dictionary:

* closed points of `X` = places `p` of `F/k`, each carrying a normalized
  (surjective onto `ℤ`) additive valuation `val p : F → ℤ ∪ {∞}`;
* divisors on `X` = finitely supported functions `P →₀ ℤ`;
* the degree of a closed point is the degree of its residue field over `k`;
* `H⁰(X, 𝒪_X) = k` says that a function without poles is constant;
* `deg (div f) = 0` for `f ≠ 0`.
-/

/-- The basic axioms for the valuations of an algebraic function field of one
variable `F/k` with set of places `P`. -/
class FFBase (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F] {P : Type w}
    (val : P → AddValuation F (WithTop ℤ)) : Prop where
  /-- Each valuation is normalized: it takes the value `1` somewhere. -/
  exists_uniformizer : ∀ p : P, ∃ t : F, val p t = ((1 : ℤ) : WithTop ℤ)
  /-- The valuations are trivial on the field of constants. -/
  val_algebraMap : ∀ (p : P) (c : k), c ≠ 0 → val p (algebraMap k F c) = 0
  /-- A nonzero function has finitely many zeroes and poles. -/
  finite_support : ∀ x : F, x ≠ 0 → {p : P | val p x ≠ 0}.Finite
  /-- `H⁰(X, 𝒪_X) = k`: a function without poles is a constant. -/
  constants : ∀ x : F, (∀ p : P, 0 ≤ val p x) → ∃ c : k, algebraMap k F c = x

namespace FFBase

variable (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F] {P : Type w}
variable (val : P → AddValuation F (WithTop ℤ)) [FFBase k val]

/-- `U k val p n = {x : F | v_p (x) ≥ n}`, a `k`-subspace of `F`. -/
def U (p : P) (n : ℤ) : Submodule k F where
  carrier := {x : F | ((n : ℤ) : WithTop ℤ) ≤ val p x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact le_trans (le_min ha hb) (AddValuation.map_add _ _ _)
  zero_mem' := by
    simp [Set.mem_setOf_eq]
  smul_mem' := by
    intro c x hx
    rcases eq_or_ne c 0 with rfl | hc
    · simp [Set.mem_setOf_eq]
    · have : (c • x) = algebraMap k F c * x := by rw [Algebra.smul_def]
      simp only [Set.mem_setOf_eq, this, AddValuation.map_mul,
        FFBase.val_algebraMap (val := val) p c hc, zero_add]
      exact hx

lemma mem_U {p : P} {n : ℤ} {x : F} : x ∈ U k val p n ↔ ((n : ℤ) : WithTop ℤ) ≤ val p x := Iff.rfl

lemma U_antitone {p : P} {m n : ℤ} (h : m ≤ n) : U k val p n ≤ U k val p m := by
  intro x hx
  rw [mem_U] at hx ⊢
  exact le_trans (by exact_mod_cast h) hx

/-- The residue space `U p n / U p (n+1)`.  For `n = 0` this is the residue field
of the place `p`, regarded as a `k`-vector space. -/
abbrev ResQuot (p : P) (n : ℤ) : Type v :=
  (U k val p n) ⧸ ((U k val p (n + 1)).comap (U k val p n).subtype)

/-- The degree of a place: the dimension over `k` of its residue field. -/
noncomputable def degPlace (p : P) : ℕ := Module.finrank k (ResQuot k val p 0)

/-- The Riemann–Roch space `L(D) = {x : F | v_p(x) ≥ -D(p) for all p}`. -/
def RRSpace (D : P →₀ ℤ) : Submodule k F := ⨅ p : P, U k val p (-(D p))

lemma mem_RRSpace {D : P →₀ ℤ} {x : F} :
    x ∈ RRSpace k val D ↔ ∀ p : P, ((-(D p) : ℤ) : WithTop ℤ) ≤ val p x := by
  simp [RRSpace, Submodule.mem_iInf, mem_U]

/-- `ℓ(D) = dim_k L(D)`. -/
noncomputable def ell (D : P →₀ ℤ) : ℕ := Module.finrank k (RRSpace k val D)

/-- The ring of adeles, as a `k`-subspace of `∏_p F`. -/
def AdeleSpace : Submodule k (P → F) where
  carrier := {a : P → F | {p : P | ¬ (0 : WithTop ℤ) ≤ val p (a p)}.Finite}
  add_mem' := by
    intro a b ha hb
    refine Set.Finite.subset (ha.union hb) ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    exact hp (le_trans (le_min hcon.1 hcon.2) (AddValuation.map_add _ _ _))
  zero_mem' := by
    simp
  smul_mem' := by
    intro c a ha
    refine Set.Finite.subset ha ?_
    intro p hp
    simp only [Set.mem_setOf_eq, Pi.smul_apply] at hp ⊢
    rcases eq_or_ne c 0 with rfl | hc
    · simp at hp
    · rw [Algebra.smul_def, AddValuation.map_mul, FFBase.val_algebraMap (val := val) p c hc,
        zero_add] at hp
      exact hp

lemma mem_AdeleSpace {a : P → F} :
    a ∈ AdeleSpace k val ↔ {p : P | ¬ (0 : WithTop ℤ) ≤ val p (a p)}.Finite := Iff.rfl

/-- The `k`-subspace `A(D) = {a | v_p(a_p) ≥ -D(p) for all p}` of `∏_p F`. -/
def ADiv (D : P →₀ ℤ) : Submodule k (P → F) :=
  ⨅ p : P, (U k val p (-(D p))).comap (LinearMap.proj p)

lemma mem_ADiv {D : P →₀ ℤ} {a : P → F} :
    a ∈ ADiv k val D ↔ ∀ p : P, ((-(D p) : ℤ) : WithTop ℤ) ≤ val p (a p) := by
  simp [ADiv, Submodule.mem_iInf, mem_U]

/-- The diagonal embedding of `F` into `∏_p F`. -/
def diagLM (F : Type v) [Field F] [Algebra k F] (P : Type w) : F →ₗ[k] (P → F) where
  toFun x := fun _ => x
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The image of the diagonal embedding `F → ∏_p F`. -/
def FDiag (F : Type v) [Field F] [Algebra k F] (P : Type w) : Submodule k (P → F) :=
  LinearMap.range (diagLM k F P)

lemma ADiv_le_AdeleSpace (D : P →₀ ℤ) : ADiv k val D ≤ AdeleSpace k val := by
  intro a ha
  rw [mem_ADiv] at ha
  refine Set.Finite.subset (D.finite_support) ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  simp only [Function.mem_support, ne_eq]
  intro hcon
  exact hp (by simpa [hcon] using ha p)

lemma FDiag_le_AdeleSpace : FDiag k F P ≤ AdeleSpace k val := by
  rintro a ⟨x, rfl⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [mem_AdeleSpace, diagLM]
  · refine Set.Finite.subset (FFBase.finite_support (k := k) (val := val) x hx) ?_
    intro p hp
    simp only [Set.mem_setOf_eq, diagLM, LinearMap.coe_mk, AddHom.coe_mk] at hp ⊢
    intro hz
    exact hp (le_of_eq hz.symm)

/-- The subspace `A(D) + F` of the adeles. -/
def HSub (D : P →₀ ℤ) : Submodule k (AdeleSpace k val) :=
  (ADiv k val D ⊔ FDiag k F P).comap (AdeleSpace k val).subtype

/-- `H¹(D) = A / (A(D) + F)`. -/
abbrev H1 (D : P →₀ ℤ) : Type (max v w) := (AdeleSpace k val) ⧸ HSub k val D

/-- The index of speciality `i(D) = dim_k A/(A(D)+F)`. -/
noncomputable def index (D : P →₀ ℤ) : ℕ := Module.finrank k (H1 k val D)

/-- The genus `g = i(0) = dim_k H¹(X, 𝒪_X)`. -/
noncomputable def genus : ℕ := index k val 0

/-- The degree of a divisor. -/
noncomputable def degDiv (D : P →₀ ℤ) : ℤ := D.sum fun p n => n * (degPlace k val p : ℤ)

/-- `ord p x` is the integer valuation of `x ≠ 0` at `p`. -/
noncomputable def ord (p : P) (x : F) : ℤ := (val p x).untopD 0

end FFBase

open FFBase

/-- The remaining axioms of a smooth projective (geometrically connected) curve:
the residue fields of the places are finite over `k`, the cohomology group
`H¹(X, 𝒪_X)` is finite dimensional (properness), and principal divisors have
degree zero. -/
class FFCurve (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F] {P : Type w}
    (val : P → AddValuation F (WithTop ℤ)) [FFBase k val] : Prop where
  /-- Every place has finite degree. -/
  residue_finite : ∀ p : P, FiniteDimensional k (ResQuot k val p 0)
  /-- Properness: `H¹(X, 𝒪_X)` is finite dimensional. -/
  genus_finite : FiniteDimensional k (H1 k val 0)
  /-- A principal divisor has degree `0`. -/
  degree_principal : ∀ x : F, x ≠ 0 → ∑ᶠ p : P, ord val p x * (degPlace k val p : ℤ) = 0

namespace FFBase

variable (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F] {P : Type w}
variable (val : P → AddValuation F (WithTop ℤ)) [FFBase k val]

/-!
## Local theory: the degree of a place
-/

/-- Multiplication by a fixed element of `F`, as a `k`-linear endomorphism. -/
def mulLM (c : F) : F →ₗ[k] F where
  toFun x := c * x
  map_add' := by intro x y; ring
  map_smul' := by
    intro a x
    simp only [Algebra.smul_def, RingHom.id_apply]
    ring

@[simp] lemma mulLM_apply (c x : F) : mulLM k c x = c * x := rfl

lemma coe_add_le_iff {d m : ℤ} {a : WithTop ℤ} :
    ((d + m : ℤ) : WithTop ℤ) ≤ ((d : ℤ) : WithTop ℤ) + a ↔ ((m : ℤ) : WithTop ℤ) ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe b =>
    rw [← WithTop.coe_add]
    simp only [WithTop.coe_le_coe]
    omega

/-- Every integer occurs as the value of some element of `F` at a given place. -/
lemma exists_val_eq (k : Type u) [Field k] [Algebra k F] [FFBase k val] (p : P) (d : ℤ) :
    ∃ c : F, val p c = ((d : ℤ) : WithTop ℤ) := by
  obtain ⟨t, ht⟩ := FFBase.exists_uniformizer (k := k) (val := val) p
  induction d using Int.induction_on with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨c * t, by rw [AddValuation.map_mul, hc, ht, ← WithTop.coe_add]⟩
  | pred m ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c / t, ?_⟩
      rw [AddValuation.map_div, hc, ht, ← WithTop.LinearOrderedAddCommGroup.coe_sub]

/-- Multiplication by an element of valuation `n - m` identifies the graded piece
at `m` with the graded piece at `n`. -/
lemma resQuotEquiv_shift (p : P) (m n : ℤ) :
    Nonempty (ResQuot k val p m ≃ₗ[k] ResQuot k val p n) := by
  obtain ⟨c, hc⟩ := exists_val_eq val k p (n - m)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hc
    exact WithTop.top_ne_coe hc
  have key : ∀ (x : F) (j : ℤ),
      ((n - m + j : ℤ) : WithTop ℤ) ≤ val p (c * x) ↔ ((j : ℤ) : WithTop ℤ) ≤ val p x := by
    intro x j
    rw [AddValuation.map_mul, hc]
    exact coe_add_le_iff
  have hmem : ∀ x : F, x ∈ U k val p m → c * x ∈ U k val p n := by
    intro x hx
    rw [mem_U] at hx ⊢
    have h2 := (key x m).2 hx
    rwa [show n - m + m = n by ring] at h2
  set g : U k val p m →ₗ[k] U k val p n :=
    LinearMap.codRestrict _ ((mulLM k c).comp (U k val p m).subtype)
      (fun x => hmem x.1 x.2) with hg
  set f : U k val p m →ₗ[k] ResQuot k val p n := (Submodule.mkQ _).comp g with hf
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hy : ((n : ℤ) : WithTop ℤ) ≤ val p (y : F) := y.2
    have hcy : c * (c⁻¹ * (y : F)) = (y : F) := by field_simp
    have hx : c⁻¹ * (y : F) ∈ U k val p m := by
      rw [mem_U]
      have h2 := key (c⁻¹ * (y : F)) m
      rw [show n - m + m = n by ring, hcy] at h2
      exact h2.1 hy
    refine ⟨⟨c⁻¹ * (y : F), hx⟩, ?_⟩
    have hgy : g ⟨c⁻¹ * (y : F), hx⟩ = y := by
      apply Subtype.ext
      simpa [hg] using hcy
    rw [hf]
    simp [hgy]
  have hker : LinearMap.ker f = (U k val p (m + 1)).comap (U k val p m).subtype := by
    ext x
    simp only [hf, hg, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      LinearMap.codRestrict_apply, mulLM_apply, mem_U]
    have h2 := key (x : F) (m + 1)
    rw [show n - m + (m + 1) = n + 1 by ring] at h2
    exact h2
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)⟩

lemma finrank_ResQuot (p : P) (n : ℤ) :
    Module.finrank k (ResQuot k val p n) = degPlace k val p := by
  obtain ⟨e⟩ := resQuotEquiv_shift k val p n 0
  exact e.finrank_eq

lemma finiteDimensional_ResQuot [FFCurve k val] (p : P) (n : ℤ) :
    FiniteDimensional k (ResQuot k val p n) := by
  haveI : FiniteDimensional k (ResQuot k val p 0) := FFCurve.residue_finite (val := val) p
  obtain ⟨e⟩ := resQuotEquiv_shift k val p 0 n
  exact e.finiteDimensional

/-!
## The key exact sequence
-/

/-- Adding one point to a divisor enlarges `A(D)` by the residue space. -/
lemma ADiv_mono {D D' : P →₀ ℤ} (h : D ≤ D') : ADiv k val D ≤ ADiv k val D' := by
  intro a ha
  rw [mem_ADiv] at ha ⊢
  intro q
  refine le_trans ?_ (ha q)
  exact_mod_cast neg_le_neg (Finsupp.le_def.mp h q)

lemma RRSpace_mono {D D' : P →₀ ℤ} (h : D ≤ D') : RRSpace k val D ≤ RRSpace k val D' := by
  intro x hx
  rw [mem_RRSpace] at hx ⊢
  intro q
  refine le_trans ?_ (hx q)
  exact_mod_cast neg_le_neg (Finsupp.le_def.mp h q)

lemma HSub_mono {D D' : P →₀ ℤ} (h : D ≤ D') : HSub k val D ≤ HSub k val D' :=
  Submodule.comap_mono (sup_le_sup_right (ADiv_mono k val h) _)

set_option maxHeartbeats 1000000 in
/-- The core of the Riemann–Roch induction: the four term exact sequence
`0 → L(D')/L(D) → A(D')/A(D) → H¹(D) → H¹(D') → 0` for `D' = D + p`. -/
lemma step_core [FFCurve k val] (D : P →₀ ℤ) (p : P) :
    ∃ n₁ n₂ : ℕ,
      n₁ + n₂ = degPlace k val p ∧
      (FiniteDimensional k (RRSpace k val D) →
        FiniteDimensional k (RRSpace k val (D + Finsupp.single p 1)) ∧
          ell k val (D + Finsupp.single p 1) = n₁ + ell k val D) ∧
      (FiniteDimensional k (H1 k val D) →
        FiniteDimensional k (H1 k val (D + Finsupp.single p 1)) ∧
          index k val D = index k val (D + Finsupp.single p 1) + n₂) ∧
      (FiniteDimensional k (H1 k val (D + Finsupp.single p 1)) →
        FiniteDimensional k (H1 k val D)) := by
  classical
  set D' := D + Finsupp.single p 1 with hD'def
  have hDp : D' p = D p + 1 := by simp [hD'def]
  have hDq : ∀ q, q ≠ p → D' q = D q := by
    intro q hq
    simp [hD'def, Ne.symm hq]
  have hle : D ≤ D' := by
    refine Finsupp.le_def.mpr fun i => ?_
    rcases eq_or_ne i p with rfl | hi
    · simp [hDp]
    · simp [hDq i hi]
  have hADle : ADiv k val D ≤ ADiv k val D' := ADiv_mono k val hle
  set Qsub : Submodule k (ADiv k val D') :=
    (ADiv k val D).comap (ADiv k val D').subtype with hQsub
  -- ### The quotient `A(D')/A(D)` is the residue space at `p`
  have hev : ∀ a : ADiv k val D', (a : P → F) p ∈ U k val p (-(D p) - 1) := by
    intro a
    rw [mem_U, show (-(D p) - 1 : ℤ) = -(D' p) by rw [hDp]; ring]
    exact (mem_ADiv (k := k) (val := val)).1 a.2 p
  set ev : (ADiv k val D') →ₗ[k] U k val p (-(D p) - 1) :=
    LinearMap.codRestrict _
      ((LinearMap.proj p : (P → F) →ₗ[k] F).comp (ADiv k val D').subtype) hev with hevdef
  set res : (ADiv k val D') →ₗ[k] ResQuot k val p (-(D p) - 1) :=
    (Submodule.mkQ _).comp ev with hresdef
  have hres_surj : Function.Surjective res := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hmem : (Pi.single p (y : F)) ∈ ADiv k val D' := by
      rw [mem_ADiv]
      intro q
      rcases eq_or_ne q p with rfl | hq
      · have hy : ((-(D q) - 1 : ℤ) : WithTop ℤ) ≤ val q (y : F) := y.2
        rw [show (-(D' q) : ℤ) = -(D q) - 1 by rw [hDp]; ring]
        simpa using hy
      · simp [Pi.single_eq_of_ne hq]
    refine ⟨⟨_, hmem⟩, ?_⟩
    have hey : ev ⟨Pi.single p (y : F), hmem⟩ = y := Subtype.ext (by simp [hevdef])
    rw [hresdef]
    simp [hey]
  have hres_ker : LinearMap.ker res = Qsub := by
    ext a
    simp only [hresdef, hevdef, hQsub, LinearMap.mem_ker, LinearMap.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype, LinearMap.codRestrict_apply, LinearMap.proj_apply, mem_U]
    constructor
    · intro h
      have h' : ((-(D p) - 1 + 1 : ℤ) : WithTop ℤ) ≤ val p ((a : P → F) p) := h
      rw [show (-(D p) - 1 + 1 : ℤ) = -(D p) by ring] at h'
      rw [mem_ADiv]
      intro q
      rcases eq_or_ne q p with rfl | hq
      · exact h'
      · have := (mem_ADiv (k := k) (val := val)).1 a.2 q
        rwa [hDq q hq] at this
    · intro h
      show ((-(D p) - 1 + 1 : ℤ) : WithTop ℤ) ≤ val p ((a : P → F) p)
      rw [show (-(D p) - 1 + 1 : ℤ) = -(D p) by ring]
      exact (mem_ADiv (k := k) (val := val)).1 h p
  have eQ : ((ADiv k val D') ⧸ Qsub) ≃ₗ[k] ResQuot k val p (-(D p) - 1) :=
    (Submodule.quotEquivOfEq _ _ hres_ker.symm).trans (res.quotKerEquivOfSurjective hres_surj)
  haveI : FiniteDimensional k (ResQuot k val p (-(D p) - 1)) :=
    finiteDimensional_ResQuot k val p _
  haveI hQfin : FiniteDimensional k ((ADiv k val D') ⧸ Qsub) := eQ.symm.finiteDimensional
  have hQrank : Module.finrank k ((ADiv k val D') ⧸ Qsub) = degPlace k val p := by
    rw [eQ.finrank_eq, finrank_ResQuot]
  -- ### The connecting map `A(D')/A(D) → H¹(D)`
  have hincl : ADiv k val D' ≤ AdeleSpace k val := ADiv_le_AdeleSpace k val D'
  set delta : (ADiv k val D') →ₗ[k] H1 k val D :=
    (HSub k val D).mkQ.comp (Submodule.inclusion hincl) with hdeltadef
  have hdker : Qsub ≤ LinearMap.ker delta := by
    intro a ha
    simp only [hdeltadef, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_left ha
  set dbar : ((ADiv k val D') ⧸ Qsub) →ₗ[k] H1 k val D :=
    Submodule.liftQ Qsub delta hdker with hdbardef
  -- ### The surjection `H¹(D) → H¹(D')`
  have hHle : HSub k val D ≤ HSub k val D' := HSub_mono k val hle
  set gam : H1 k val D →ₗ[k] H1 k val D' :=
    Submodule.mapQ _ _ LinearMap.id (by simpa using hHle) with hgamdef
  have hgam_mk : ∀ a : AdeleSpace k val,
      gam (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := by
    intro a
    rw [hgamdef]
    simp
  have hgam_surj : Function.Surjective gam := by
    intro z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk a, hgam_mk a⟩
  have hdbar_mk : ∀ a : ADiv k val D',
      dbar (Submodule.Quotient.mk a) =
        Submodule.Quotient.mk (⟨(a : P → F), hincl a.2⟩ : AdeleSpace k val) := by
    intro a
    rw [hdbardef]
    rfl
  have hrange : LinearMap.range dbar = LinearMap.ker gam := by
    apply le_antisymm
    · rintro z ⟨w, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      rw [LinearMap.mem_ker, hdbar_mk a, hgam_mk]
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left a.2
    · intro z hz
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker, hgam_mk a, Submodule.Quotient.mk_eq_zero] at hz
      have hz' : (a : P → F) ∈ ADiv k val D' ⊔ FDiag k F P := hz
      obtain ⟨b, hb, f, hf, hab⟩ := Submodule.mem_sup.1 hz'
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      rw [hdbar_mk ⟨b, hb⟩, Submodule.Quotient.eq]
      have hba : (((⟨b, hincl hb⟩ : AdeleSpace k val) - a : AdeleSpace k val) : P → F) = -f := by
        simp only [AddSubgroupClass.coe_sub]
        rw [← hab]
        ring
      show (((⟨b, hincl hb⟩ : AdeleSpace k val) - a : AdeleSpace k val) : P → F)
        ∈ ADiv k val D ⊔ FDiag k F P
      rw [hba]
      exact Submodule.neg_mem _ (Submodule.mem_sup_right hf)
  -- ### The map `L(D') → A(D')/A(D)`
  have hphi_mem : ∀ x : RRSpace k val D', (diagLM k F P) (x : F) ∈ ADiv k val D' := by
    intro x
    rw [mem_ADiv]
    intro q
    exact (mem_RRSpace (k := k) (val := val)).1 x.2 q
  set phi : (RRSpace k val D') →ₗ[k] ((ADiv k val D') ⧸ Qsub) :=
    (Submodule.mkQ Qsub).comp
      (LinearMap.codRestrict _ ((diagLM k F P).comp (RRSpace k val D').subtype) hphi_mem)
    with hphidef
  have hphi_mk : ∀ x : RRSpace k val D',
      phi x = Submodule.Quotient.mk ⟨diagLM k F P (x : F), hphi_mem x⟩ := by
    intro x
    rw [hphidef]
    rfl
  have hphi_ker : LinearMap.ker phi = (RRSpace k val D).comap (RRSpace k val D').subtype := by
    ext x
    rw [LinearMap.mem_ker, hphi_mk, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      have hx' : (diagLM k F P (x : F)) ∈ ADiv k val D := hx
      rw [mem_ADiv] at hx'
      exact (mem_RRSpace (k := k) (val := val)).2 (fun q => hx' q)
    · intro hx
      have hx' : (x : F) ∈ RRSpace k val D := hx
      rw [mem_RRSpace] at hx'
      show (diagLM k F P (x : F)) ∈ ADiv k val D
      rw [mem_ADiv]
      exact fun q => hx' q
  have hphi_range : LinearMap.range phi = LinearMap.ker dbar := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      rw [LinearMap.mem_ker, hphi_mk, hdbar_mk, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right ⟨(x : F), rfl⟩
    · intro z hz
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker, hdbar_mk a, Submodule.Quotient.mk_eq_zero] at hz
      have hz' : (a : P → F) ∈ ADiv k val D ⊔ FDiag k F P := hz
      obtain ⟨b, hb, f, hf, hab⟩ := Submodule.mem_sup.1 hz'
      obtain ⟨x, hx⟩ := hf
      have hfa : f = (a : P → F) - b := by rw [← hab]; ring
      have hxmem : x ∈ RRSpace k val D' := by
        rw [mem_RRSpace]
        intro q
        have h1 : ((-(D' q) : ℤ) : WithTop ℤ) ≤ val q ((a : P → F) q) :=
          (mem_ADiv (k := k) (val := val)).1 a.2 q
        have h2 : ((-(D' q) : ℤ) : WithTop ℤ) ≤ val q (b q) :=
          (mem_ADiv (k := k) (val := val)).1 (hADle hb) q
        have h3 : f q = (a : P → F) q - b q := by rw [hfa]; rfl
        have h4 : val q (f q) = val q ((a : P → F) q - b q) := by rw [h3]
        have h5 : ((-(D' q) : ℤ) : WithTop ℤ) ≤ val q ((a : P → F) q - b q) := by
          refine le_trans (le_min h1 h2) ?_
          have := AddValuation.map_sub (val q) ((a : P → F) q) (b q)
          exact this
        have h6 : f q = x := by rw [← hx]; rfl
        rw [← h6, h4]
        exact h5
      refine ⟨⟨x, hxmem⟩, ?_⟩
      rw [hphi_mk]
      rw [Submodule.Quotient.eq]
      have hcoe : ((⟨diagLM k F P x, hphi_mem ⟨x, hxmem⟩⟩ : ADiv k val D') - a).1 = -b := by
        have hdx : diagLM k F P x = f := by rw [← hx]
        show diagLM k F P x - (a : P → F) = -b
        rw [hdx, hfa]
        ring
      show ((⟨diagLM k F P x, hphi_mem ⟨x, hxmem⟩⟩ : ADiv k val D') - a).1 ∈ ADiv k val D
      rw [hcoe]
      exact Submodule.neg_mem _ hb
  -- ### Dimension count
  refine ⟨Module.finrank k (LinearMap.ker dbar), Module.finrank k (LinearMap.ker gam),
    ?_, ?_, ?_, ?_⟩
  · have := LinearMap.finrank_range_add_finrank_ker dbar
    rw [hQrank, hrange] at this
    omega
  · intro hL
    have e1 : (LinearMap.ker phi) ≃ₗ[k] RRSpace k val D :=
      (LinearEquiv.ofEq _ _ hphi_ker).trans
        (Submodule.comapSubtypeEquivOfLe (RRSpace_mono k val hle))
    haveI : FiniteDimensional k (LinearMap.ker phi) := e1.symm.finiteDimensional
    haveI : FiniteDimensional k (RRSpace k val D' ⧸ LinearMap.ker phi) :=
      (phi.quotKerEquivRange).symm.finiteDimensional
    haveI hfd : FiniteDimensional k (RRSpace k val D') :=
      Module.Finite.of_submodule_quotient (LinearMap.ker phi)
    refine ⟨hfd, ?_⟩
    have hrk := LinearMap.finrank_range_add_finrank_ker phi
    rw [hphi_range, e1.finrank_eq] at hrk
    simpa [ell] using hrk.symm
  · intro hH
    haveI := hH
    haveI hfd : FiniteDimensional k (H1 k val D') := Module.Finite.of_surjective gam hgam_surj
    refine ⟨hfd, ?_⟩
    have hrk := LinearMap.finrank_range_add_finrank_ker gam
    rw [LinearMap.range_eq_top.2 hgam_surj, finrank_top] at hrk
    simpa [index] using hrk.symm
  · intro hH'
    haveI := hH'
    haveI : FiniteDimensional k (LinearMap.ker gam) := by
      rw [← hrange]
      infer_instance
    haveI : FiniteDimensional k (H1 k val D ⧸ LinearMap.ker gam) :=
      (gam.quotKerEquivRange).symm.finiteDimensional
    exact Module.Finite.of_submodule_quotient (LinearMap.ker gam)

/-- The key numerical step: passing from `D` to `D + p`. -/
lemma step_up [FFCurve k val] (D : P →₀ ℤ) (p : P)
    (hL : FiniteDimensional k (RRSpace k val D)) (hH : FiniteDimensional k (H1 k val D)) :
    FiniteDimensional k (RRSpace k val (D + Finsupp.single p 1)) ∧
      FiniteDimensional k (H1 k val (D + Finsupp.single p 1)) ∧
      (ell k val (D + Finsupp.single p 1) : ℤ) - index k val (D + Finsupp.single p 1)
        = (ell k val D : ℤ) - index k val D + degPlace k val p := by
  obtain ⟨n₁, n₂, hn, hLstep, hHstep, -⟩ := step_core k val D p
  obtain ⟨hL', hell⟩ := hLstep hL
  obtain ⟨hH', hidx⟩ := hHstep hH
  refine ⟨hL', hH', ?_⟩
  have h1 : (ell k val (D + Finsupp.single p 1) : ℤ) = n₁ + ell k val D := by exact_mod_cast hell
  have h2 : (index k val D : ℤ) = index k val (D + Finsupp.single p 1) + n₂ := by
    exact_mod_cast hidx
  have h3 : (n₁ : ℤ) + n₂ = degPlace k val p := by exact_mod_cast hn
  omega

lemma finiteDimensional_RRSpace_of_le {D D' : P →₀ ℤ} (h : D ≤ D')
    (hL : FiniteDimensional k (RRSpace k val D')) : FiniteDimensional k (RRSpace k val D) :=
  FiniteDimensional.of_injective (Submodule.inclusion (RRSpace_mono k val h))
    (Submodule.inclusion_injective _)

lemma finiteDimensional_H1_down [FFCurve k val] (D : P →₀ ℤ) (p : P)
    (hH : FiniteDimensional k (H1 k val (D + Finsupp.single p 1))) :
    FiniteDimensional k (H1 k val D) := by
  obtain ⟨n₁, n₂, -, -, -, hdown⟩ := step_core k val D p
  exact hdown hH

/-!
## Riemann–Roch in index form
-/

/-- `H⁰(X, 𝒪_X) = k`: the Riemann–Roch space of the zero divisor is the field of
constants. -/
lemma rrSpaceZeroEquiv : Nonempty (k ≃ₗ[k] RRSpace k val 0) := by
  have hmem : ∀ c : k, algebraMap k F c ∈ RRSpace k val 0 := by
    intro c
    rw [mem_RRSpace]
    intro q
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [FFBase.val_algebraMap (val := val) q c hc]
      simp
  set f : k →ₗ[k] RRSpace k val 0 :=
    LinearMap.codRestrict _ (Algebra.linearMap k F) hmem with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have : algebraMap k F a = algebraMap k F b := congrArg Subtype.val hab
    exact (algebraMap k F).injective this
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [mem_RRSpace] at hy
    obtain ⟨c, hc⟩ := FFBase.constants (k := k) (val := val) y (by simpa using hy)
    exact ⟨c, Subtype.ext hc⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

lemma ell_zero : ell k val 0 = 1 := by
  obtain ⟨e⟩ := rrSpaceZeroEquiv k val
  rw [ell, ← e.finrank_eq, Module.finrank_self]

lemma finiteDimensional_RRSpace_zero : FiniteDimensional k (RRSpace k val 0) := by
  obtain ⟨e⟩ := rrSpaceZeroEquiv k val
  exact e.finiteDimensional

lemma degDiv_add_single (D : P →₀ ℤ) (p : P) :
    degDiv k val (D + Finsupp.single p 1) = degDiv k val D + degPlace k val p := by
  classical
  simp only [degDiv]
  rw [Finsupp.sum_add_index' (by intro q; simp) (by intro q b₁ b₂; ring),
    Finsupp.sum_single_index (by simp)]
  simp

/-!
## Vanishing of `ℓ(D)` for divisors of negative degree
-/

lemma val_eq_ord {p : P} {x : F} (hx : x ≠ 0) : val p x = ((ord val p x : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff (val p)).2 hx)
  rw [ord, ← hm]
  simp

lemma degDiv_eq_finsum (D : P →₀ ℤ) :
    degDiv k val D = ∑ᶠ p : P, D p * (degPlace k val p : ℤ) := by
  classical
  rw [degDiv, Finsupp.sum, eq_comm]
  apply finsum_eq_sum_of_support_subset
  intro q hq
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hq
  simpa using hq.1

/-- A divisor of negative degree has no nonzero global sections. -/
lemma RRSpace_eq_bot_of_degDiv_neg [FFCurve k val] (D : P →₀ ℤ)
    (hD : degDiv k val D < 0) : RRSpace k val D = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  rw [mem_RRSpace] at hx
  have hord : ∀ q : P, -(D q) ≤ ord val q x := by
    intro q
    have := hx q
    rw [val_eq_ord val hx0] at this
    exact_mod_cast this
  have hsupp₁ : (Function.support fun q : P => D q * (degPlace k val q : ℤ)).Finite := by
    refine Set.Finite.subset D.finite_support ?_
    intro q hq
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hq
    simpa using hq.1
  have hsupp₂ : (Function.support fun q : P => ord val q x * (degPlace k val q : ℤ)).Finite := by
    refine Set.Finite.subset (FFBase.finite_support (k := k) (val := val) x hx0) ?_
    intro q hq
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hq
    simp only [Set.mem_setOf_eq, ne_eq]
    rw [val_eq_ord val hx0]
    simpa using hq.1
  have hsum : ∑ᶠ q : P, (D q * (degPlace k val q : ℤ) + ord val q x * (degPlace k val q : ℤ))
      = degDiv k val D + 0 := by
    rw [finsum_add_distrib hsupp₁ hsupp₂, ← degDiv_eq_finsum,
      FFCurve.degree_principal (k := k) (val := val) x hx0]
  have hnonneg : (0 : ℤ) ≤ ∑ᶠ q : P,
      (D q * (degPlace k val q : ℤ) + ord val q x * (degPlace k val q : ℤ)) := by
    refine finsum_nonneg fun q => ?_
    have h1 : (0 : ℤ) ≤ D q + ord val q x := by linarith [hord q]
    have h2 : (0 : ℤ) ≤ (degPlace k val q : ℤ) := Int.natCast_nonneg _
    calc (0 : ℤ) ≤ (D q + ord val q x) * (degPlace k val q : ℤ) := mul_nonneg h1 h2
      _ = D q * (degPlace k val q : ℤ) + ord val q x * (degPlace k val q : ℤ) := by ring
  rw [hsum] at hnonneg
  omega

/-- `ℓ(D) = 0` when `deg D < 0`. -/
lemma ell_eq_zero_of_degDiv_neg [FFCurve k val] (D : P →₀ ℤ)
    (hD : degDiv k val D < 0) : ell k val D = 0 := by
  rw [ell, RRSpace_eq_bot_of_degDiv_neg k val D hD]
  simp

/-- Riemann–Roch in index (Weil) form: `ℓ(D) - i(D) = deg D + 1 - g`, together with
the finiteness of all the spaces involved. -/
theorem riemann_roch_index [FFCurve k val] (D : P →₀ ℤ) :
    FiniteDimensional k (RRSpace k val D) ∧ FiniteDimensional k (H1 k val D) ∧
      (ell k val D : ℤ) - index k val D = degDiv k val D + 1 - genus k val := by
  classical
  let Good : (P →₀ ℤ) → Prop := fun E =>
    FiniteDimensional k (RRSpace k val E) ∧ FiniteDimensional k (H1 k val E) ∧
      (ell k val E : ℤ) - index k val E = degDiv k val E + 1 - genus k val
  have base : Good 0 := by
    refine ⟨finiteDimensional_RRSpace_zero k val, FFCurve.genus_finite (val := val), ?_⟩
    rw [ell_zero]
    simp [genus, degDiv]
  have up : ∀ (E : P →₀ ℤ) (q : P), Good E → Good (E + Finsupp.single q 1) := by
    rintro E q ⟨h1, h2, h3⟩
    obtain ⟨h1', h2', h3'⟩ := step_up k val E q h1 h2
    refine ⟨h1', h2', ?_⟩
    rw [h3', degDiv_add_single, h3]
    ring
  have down : ∀ (E : P →₀ ℤ) (q : P), Good (E + Finsupp.single q 1) → Good E := by
    rintro E q ⟨h1, h2, h3⟩
    have hle : E ≤ E + Finsupp.single q 1 := by
      refine Finsupp.le_def.mpr fun i => ?_
      have : (0 : ℤ) ≤ (Finsupp.single q (1 : ℤ)) i := by
        rcases eq_or_ne q i with rfl | hqi
        · simp
        · simp [hqi]
      simpa using this
    have hL : FiniteDimensional k (RRSpace k val E) :=
      finiteDimensional_RRSpace_of_le k val hle h1
    have hH : FiniteDimensional k (H1 k val E) := finiteDimensional_H1_down k val E q h2
    refine ⟨hL, hH, ?_⟩
    obtain ⟨-, -, h4⟩ := step_up k val E q hL hH
    rw [h4, degDiv_add_single] at h3
    linarith
  have shift : ∀ (b : ℤ) (E : P →₀ ℤ) (q : P), Good E → Good (E + Finsupp.single q b) := by
    intro b
    induction b using Int.induction_on with
    | zero => intro E q hE; simpa using hE
    | succ m ih =>
        intro E q hE
        have : E + Finsupp.single q ((m : ℤ) + 1) = (E + Finsupp.single q (m : ℤ))
            + Finsupp.single q 1 := by
          rw [Finsupp.single_add]
          abel
        rw [this]
        exact up _ q (ih E q hE)
    | pred m ih =>
        intro E q hE
        refine down _ q ?_
        have : E + Finsupp.single q (-(m : ℤ) - 1) + Finsupp.single q 1
            = E + Finsupp.single q (-(m : ℤ)) := by
          rw [add_assoc, ← Finsupp.single_add, show (-(m : ℤ) - 1 + 1) = -(m : ℤ) by ring]
        rw [this]
        exact ih E q hE
  have main : ∀ E : P →₀ ℤ, Good E := by
    intro E
    induction E using Finsupp.induction with
    | zero => exact base
    | single_add a b f _ _ ih =>
        have : Finsupp.single a b + f = f + Finsupp.single a b := by abel
        rw [this]
        exact shift b f a ih
  exact main D

end FFBase

open FFBase in
/-- **Riemann–Roch for a smooth projective curve.**

Let `F/k` be the function field of a smooth projective geometrically connected
curve `X` over `k`, with set of closed points (places) `P` and normalized
valuations `val`.  For a divisor `D` write `ℓ(D) = dim_k L(D)` and
`deg D = ∑_p D(p) · deg p`, and let `g` be the genus, i.e. the dimension of
`H¹(X, 𝒪_X) = A/(A(0) + F)`.  If `K` is a canonical divisor, i.e. a divisor for
which Serre duality `dim_k H¹(D) = ℓ(K - D)` holds, then

`ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/
theorem riemann_roch_curve {k : Type u} [Field k] {F : Type v} [Field F] [Algebra k F]
    {P : Type w} (val : P → AddValuation F (WithTop ℤ)) [FFBase k val] [FFCurve k val]
    (K : P →₀ ℤ) (hK : ∀ D : P →₀ ℤ, index k val D = ell k val (K - D)) (D : P →₀ ℤ) :
    (ell k val D : ℤ) - ell k val (K - D) = degDiv k val D + 1 - genus k val := by
  rw [← hK D]
  exact (riemann_roch_index k val D).2.2

open FFBase in
/-- Riemann's inequality `ℓ(D) ≥ deg D + 1 - g`, an unconditional consequence of the
index form of Riemann–Roch. -/
theorem riemann_inequality {k : Type u} [Field k] {F : Type v} [Field F] [Algebra k F]
    {P : Type w} (val : P → AddValuation F (WithTop ℤ)) [FFBase k val] [FFCurve k val]
    (D : P →₀ ℤ) : degDiv k val D + 1 - genus k val ≤ (ell k val D : ℤ) := by
  have h := (riemann_roch_index k val D).2.2
  have : (0 : ℤ) ≤ index k val D := Int.natCast_nonneg _
  omega

open FFBase in
/-- A canonical divisor satisfies `ℓ(K) = g`. -/
theorem ell_canonical {k : Type u} [Field k] {F : Type v} [Field F] [Algebra k F]
    {P : Type w} (val : P → AddValuation F (WithTop ℤ)) [FFBase k val] [FFCurve k val]
    (K : P →₀ ℤ) (hK : ∀ D : P →₀ ℤ, index k val D = ell k val (K - D)) :
    ell k val K = genus k val := by
  have h := riemann_roch_curve val K hK 0
  rw [ell_zero, sub_zero] at h
  simp only [degDiv, Finsupp.sum_zero_index] at h
  omega

open FFBase in
/-- A canonical divisor has degree `2g - 2`. -/
theorem degDiv_canonical {k : Type u} [Field k] {F : Type v} [Field F] [Algebra k F]
    {P : Type w} (val : P → AddValuation F (WithTop ℤ)) [FFBase k val] [FFCurve k val]
    (K : P →₀ ℤ) (hK : ∀ D : P →₀ ℤ, index k val D = ell k val (K - D)) :
    degDiv k val K = 2 * (genus k val : ℤ) - 2 := by
  have h := riemann_roch_curve val K hK K
  rw [sub_self, ell_zero, ell_canonical val K hK] at h
  omega

end Math2

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

