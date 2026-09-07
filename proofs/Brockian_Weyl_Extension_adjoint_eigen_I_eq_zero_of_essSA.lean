/-
  Brockian/WeylSelfAdjointExtension.lean — the **self-adjoint extension** rung of
  Weyl / von Neumann theory: for a densely-defined symmetric operator `T` that is
  essentially self-adjoint, its closure `T̄` is the canonical (and, in the reachable
  sense below, minimal/unique) self-adjoint object, and its spectrum is real.

  Built on:
    * `Brockian/WeylOperator.lean`  (`Brockian.Weyl.Operator`): `IsSymmetric`,
      `deficiencySpace`, `mem_deficiencySpace_iff`, `EssentiallySelfAdjoint`,
      `IsSymmetric.im_eq_zero_of_apply_eq_smul` (real eigenvalues).
    * `Brockian/WeylClosure.lean` (`Brockian.Weyl.Closure`): `symmetric_isClosable`,
      `symmetric_closure_le_adjoint` (`T̄ ⊆ T*`), `closure_eq_self_of_isClosed`.
    * `Brockian/WeylCayley.lean`  (`Brockian.Weyl.Cayley`): `essentiallySelfAdjoint_iff`
      (the range-density criterion).
    * Mathlib v4.32.0's `LinearPMap.adjoint`, `LinearPMap.IsSelfAdjoint`
      (`isSelfAdjoint_def`, `IsSelfAdjoint.isClosed`), `adjoint_graph_eq_graph_adjoint`,
      and `IsClosable.graph_closure_eq_closure_graph`.

  ## Setting

  `H` is a complex Hilbert space (`CompleteSpace H`; physics inner-product
  convention, conjugate-linear in the FIRST slot). `T : H →ₗ.[ℂ] H` is a
  densely-defined symmetric operator (density `Dense (↑T.domain : Set H)` is the
  standing hypothesis making `T.adjoint` a bona-fide operator).

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `adjoint_graph_topologicalClosure_eq` — the pure-submodule fact
      `(ḡ).adjoint = g.adjoint`: the graph-adjoint depends only on the *closure* of
      the graph (its defining orthogonality condition is a continuous, hence closed,
      relation). The topological engine behind everything below.

    * `adjoint_closure` — **`(T̄)* = T*`**: the adjoint of the closure equals the
      adjoint. (`T*` sees only the graph closure, which `T` and `T̄` share.) The key
      structural identity Mathlib does not ship.

    * `isSymmetric_of_le_adjoint` — `T ⊆ T*  ⇒  T` symmetric (the converse of
      `IsFormalAdjoint.le_adjoint`), so symmetry is exactly `T ⊆ T*`.

    * `closure_isSymmetric` — **the closure of a symmetric operator is symmetric.**
      From `T̄ ⊆ T* = (T̄)*` (using `adjoint_closure`) and the previous lemma. The
      genuine "`T̄` is symmetric" fact, obtained without a graph-limit argument.

    * `le_closure_le_adjoint` — **the von Neumann inclusion chain `T ⊆ T̄ ⊆ T*`**
      packaged (`T ≤ T̄` from `le_closure`, `T̄ ≤ T*` from `symmetric_closure_le_adjoint`).

    * `isSelfAdjoint_closure_iff_eq_adjoint` — **`T̄` self-adjoint ⟺ `T̄ = T*`.**
      Because `(T̄)* = T*`, self-adjointness of the closure is *exactly* the missing
      reverse inclusion `T* ⊆ T̄`. This pins the Gate to a single equality.

    * `essentiallySelfAdjoint_iff'` — the Cayley range-density criterion, re-exported
      into this namespace as the self-adjoint-extension existence test.

    * `adjoint_eigen_I_eq_zero_of_essSA` / `adjoint_eigen_neg_I_eq_zero_of_essSA`
      — **under ESA, `±i` is not an eigenvalue of `T*`**: `T* g = ±i·g ⇒ g = 0`
      (the trivial deficiency spaces, unpacked). A real-spectrum foothold on `T*`.

    * `eigenvalue_im_zero` — eigenvalues of the symmetric `T` are real (reused).

    * `closure_eigenvalue_im_zero` — **eigenvalues of the closure `T̄` are real**
      (`T̄ v = μ·v`, `v ≠ 0 ⇒ Im μ = 0`), via `closure_isSymmetric`. The real-spectrum
      statement for the self-adjoint extension candidate itself.

    * `closure_le_of_isClosed_extension` — **`T̄` is the smallest closed extension**:
      any closed `S ⊇ T` has `T̄ ⊆ S`.

    * `closure_le_of_isSelfAdjoint_extension` — **`T̄` is contained in every
      self-adjoint extension** `S` (`S` self-adjoint is closed). The reachable
      uniqueness content.

    * `id_closure_isSelfAdjoint`, `id_closure_eigenvalue_im_zero` — Gate-0
      non-vacuity on the identity operator (a genuine self-adjoint witness).

  ## What is NOT proved, and why (honest scope statement)

  The **full** rung-1/2 goals — the equality `T̄ = T*` (equivalently `T̄` genuinely
  self-adjoint), and hence the strict uniqueness `S = T̄` for a self-adjoint extension
  `S` — are **not** proved. `isSelfAdjoint_closure_iff_eq_adjoint` reduces both to the
  single reverse inclusion `T* ⊆ T̄`, i.e. `T̄ = T*`. That is precisely the von
  Neumann fact `T̄ = T** ` together with "ESA ⟹ deficiency-free ⟹ `T** ` self-adjoint":
  it needs the **double adjoint** `T** ` and the extension bijection, neither of which
  exists in Mathlib v4.32.0 (`LinearPMap` has `adjoint` but no `adjoint_adjoint`, no
  Cayley-transform surjectivity). So this file ships the reachable maximum: the
  inclusion chain, `T̄` symmetric with real spectrum, the exact self-adjointness
  criterion `T̄ = T*`, and `T̄` minimal among closed / self-adjoint extensions —
  naming the one missing equality rather than asserting it.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Brockian.WeylOperator
import Brockian.WeylClosure
import Brockian.WeylCayley

namespace Brockian.Weyl.Extension

open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.Cayley

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The graph-adjoint depends only on the graph closure -/

/-- **The graph-adjoint sees only the closure of the graph.** For any submodule `g`
of `H × H`, `(ḡ).adjoint = g.adjoint`. The defining condition of `Submodule.adjoint`
(`Submodule.mem_adjoint_iff`) is, for a fixed test vector `x`, the vanishing of the
*continuous* form `(a,b) ↦ ⟪b, x₁⟫ − ⟪a, x₂⟫` on `g`; a continuous form vanishing on
`g` vanishes on its closure, so `g` and `ḡ` have the same adjoint. This is the
topological engine under `adjoint_closure`. -/
theorem adjoint_graph_topologicalClosure_eq (g : Submodule ℂ (H × H)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  ext x
  rw [Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    exact h a b (g.le_topologicalClosure hab)
  · intro h a b hab
    have hcont : Continuous (fun p : H × H => inner ℂ p.2 x.fst - inner ℂ p.1 x.snd) :=
      (continuous_snd.inner continuous_const).sub (continuous_fst.inner continuous_const)
    have hclosed : IsClosed {p : H × H | inner ℂ p.2 x.fst - inner ℂ p.1 x.snd = 0} :=
      isClosed_eq hcont continuous_const
    have hsub : (g : Set (H × H)) ⊆ {p : H × H | inner ℂ p.2 x.fst - inner ℂ p.1 x.snd = 0} := by
      intro p hp; exact h p.1 p.2 hp
    have hmem : (a, b) ∈ closure (g : Set (H × H)) := by
      rw [← Submodule.topologicalClosure_coe]; exact hab
    have := closure_minimal hsub hclosed hmem
    simpa using this

/-! ### The adjoint of the closure equals the adjoint -/

/-- **`(T̄)* = T*`.** The adjoint of the closure of a densely-defined operator equals
its adjoint. Reason: `T*.graph = T.graph.adjoint` and `T̄.graph = T.graph.topologicalClosure`
(Mathlib), and the graph-adjoint is closure-blind (`adjoint_graph_topologicalClosure_eq`).
Mathlib v4.32.0 has the ingredients but not this consequence. -/
theorem adjoint_closure {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hcl : T.IsClosable) : T.closure.adjoint = T.adjoint := by
  have hsub : (T.domain : Set H) ⊆ (T.closure.domain : Set H) :=
    SetLike.coe_subset_coe.mpr (LinearPMap.le_closure T).1
  have hdcl : Dense (T.closure.domain : Set H) := Dense.mono hsub hd
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hdcl,
      LinearPMap.adjoint_graph_eq_graph_adjoint hd,
      ← hcl.graph_closure_eq_closure_graph,
      adjoint_graph_topologicalClosure_eq]

/-! ### Symmetry is exactly `T ⊆ T*`; the closure is symmetric -/

/-- **`T ⊆ T*` ⇒ `T` symmetric** (the converse of `IsFormalAdjoint.le_adjoint`). If
the densely-defined `T` is contained in its adjoint, then on the domain
`⟪T x, y⟫ = ⟪T* x, y⟫ = ⟪x, T y⟫`, i.e. `T` is symmetric. Together with
`symmetric_le_adjoint`, symmetry ⟺ `T ⊆ T*`. -/
theorem isSymmetric_of_le_adjoint {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (h : T ≤ T.adjoint) : IsSymmetric T := by
  intro x y
  have hx : (x : H) ∈ T.adjoint.domain := h.1 x.2
  have hxeq : T x = T.adjoint ⟨(x : H), hx⟩ := h.2 rfl
  have hfa := (LinearPMap.adjoint_isFormalAdjoint hd) ⟨(x : H), hx⟩ y
  rw [hxeq]
  simpa using hfa

/-- **The closure of a symmetric operator is symmetric.** From the inclusion chain
`T̄ ⊆ T*` and the identity `T* = (T̄)*` (`adjoint_closure`), we get `T̄ ⊆ (T̄)*`, which
by `isSymmetric_of_le_adjoint` is symmetry of `T̄`. (No graph-limit argument needed —
the closure-blindness of the adjoint does the work.) -/
theorem closure_isSymmetric {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : IsSymmetric T.closure := by
  have hcl : T.IsClosable := Brockian.Weyl.Closure.symmetric_isClosable hT hd
  have hsub : (T.domain : Set H) ⊆ (T.closure.domain : Set H) :=
    SetLike.coe_subset_coe.mpr (LinearPMap.le_closure T).1
  have hdcl : Dense (T.closure.domain : Set H) := Dense.mono hsub hd
  refine isSymmetric_of_le_adjoint hdcl ?_
  rw [adjoint_closure hd hcl]
  exact Brockian.Weyl.Closure.symmetric_closure_le_adjoint hT hd

/-! ### The inclusion chain `T ⊆ T̄ ⊆ T*` -/

/-- **The von Neumann inclusion chain `T ⊆ T̄ ⊆ T*`.** The symmetric operator sits
inside its closure (`LinearPMap.le_closure`), which in turn sits inside the adjoint
(`symmetric_closure_le_adjoint`). Von Neumann's chain `T ⊆ T̄ = T** ⊆ T*`, minus the
`T̄ = T**` identity Mathlib lacks. -/
theorem le_closure_le_adjoint {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : T ≤ T.closure ∧ T.closure ≤ T.adjoint :=
  ⟨LinearPMap.le_closure T, Brockian.Weyl.Closure.symmetric_closure_le_adjoint hT hd⟩

/-! ### The self-adjointness criterion for the closure -/

/-- **`T̄` is self-adjoint ⟺ `T̄ = T*`.** Since `(T̄)* = T*` (`adjoint_closure`),
self-adjointness of the closure — `(T̄)* = T̄` — is *exactly* the equality `T̄ = T*`,
equivalently the reverse inclusion `T* ⊆ T̄`. This isolates the entire remaining
Gate to one identity: the double-adjoint fact `T̄ = T** ` (with ESA giving
deficiency-freeness) that Mathlib v4.32.0 does not provide. -/
theorem isSelfAdjoint_closure_iff_eq_adjoint {T : H →ₗ.[ℂ] H}
    (hT : IsSymmetric T) (hd : Dense (T.domain : Set H)) :
    IsSelfAdjoint T.closure ↔ T.closure = T.adjoint := by
  have hcl : T.IsClosable := Brockian.Weyl.Closure.symmetric_isClosable hT hd
  rw [LinearPMap.isSelfAdjoint_def, adjoint_closure hd hcl, eq_comm]

/-! ### The essential-self-adjointness (extension existence) criterion -/

/-- **Existence criterion for the self-adjoint extension.** A densely-defined
symmetric `T` is essentially self-adjoint — i.e. its closure is a self-adjoint
extension candidate — iff both `ran(T + i)` and `ran(T − i)` are dense
(`Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff`, re-exported). -/
theorem essentiallySelfAdjoint_iff' {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H)) :
    EssentiallySelfAdjoint T ↔
      Dense (rangeAddI T : Set H) ∧ Dense (rangeSubI T : Set H) :=
  Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff hd

/-! ### Real spectrum -/

/-- **Eigenvalues of the symmetric `T` are real** (reused from `WeylOperator`):
`T v = μ·v`, `v ≠ 0 ⇒ Im μ = 0`. -/
theorem eigenvalue_im_zero {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {v : T.domain}
    {μ : ℂ} (hv : (v : H) ≠ 0) (heig : T v = μ • (v : H)) : μ.im = 0 :=
  hT.im_eq_zero_of_apply_eq_smul hv heig

/-- **Eigenvalues of the closure `T̄` are real.** For the self-adjoint extension
candidate `T̄`, `T̄ v = μ·v` with `v ≠ 0` forces `Im μ = 0`. The real-spectrum
statement for `T̄` itself, via `closure_isSymmetric` and the symmetric real-eigenvalue
lemma. -/
theorem closure_eigenvalue_im_zero {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) {v : T.closure.domain} {μ : ℂ}
    (hv : (v : H) ≠ 0) (heig : T.closure v = μ • (v : H)) : μ.im = 0 :=
  (closure_isSymmetric hT hd).im_eq_zero_of_apply_eq_smul hv heig

/-- **Under ESA, `+i` is not an eigenvalue of `T*`.** If `T` is essentially
self-adjoint then `T* g = i·g ⇒ g = 0` (the deficiency space `ker(T* − i)` is
trivial). A real-spectrum foothold: the non-real `+i` is absent from the point
spectrum of `T*`. -/
theorem adjoint_eigen_I_eq_zero_of_essSA {T : H →ₗ.[ℂ] H}
    (h : EssentiallySelfAdjoint T) {g : T.adjoint.domain}
    (hg : T.adjoint g = Complex.I • (g : H)) : (g : H) = 0 := by
  have hmem : g ∈ deficiencySpace T Complex.I :=
    (mem_deficiencySpace_iff T Complex.I g).mpr hg
  rw [h.1, Submodule.mem_bot] at hmem
  exact Submodule.coe_eq_zero.mpr hmem

/-- **Under ESA, `−i` is not an eigenvalue of `T*`.** `T* g = −i·g ⇒ g = 0`. -/
theorem adjoint_eigen_neg_I_eq_zero_of_essSA {T : H →ₗ.[ℂ] H}
    (h : EssentiallySelfAdjoint T) {g : T.adjoint.domain}
    (hg : T.adjoint g = (-Complex.I) • (g : H)) : (g : H) = 0 := by
  have hmem : g ∈ deficiencySpace T (-Complex.I) :=
    (mem_deficiencySpace_iff T (-Complex.I) g).mpr hg
  rw [h.2, Submodule.mem_bot] at hmem
  exact Submodule.coe_eq_zero.mpr hmem

/-! ### Uniqueness (reachable form): `T̄` is the minimal closed / self-adjoint extension -/

/-- **`T̄` is the smallest closed extension.** Any *closed* operator `S` with `T ⊆ S`
contains the closure: `T̄ ⊆ S`. (Closure is monotone and fixes closed operators.) -/
theorem closure_le_of_isClosed_extension {T S : H →ₗ.[ℂ] H} (h : T ≤ S)
    (hS : S.IsClosed) : T.closure ≤ S := by
  have hmono : T.closure ≤ S.closure := hS.isClosable.closure_mono h
  rwa [Brockian.Weyl.Closure.closure_eq_self_of_isClosed hS] at hmono

/-- **`T̄` is contained in every self-adjoint extension.** If `S` is self-adjoint and
`T ⊆ S`, then `T̄ ⊆ S` (a self-adjoint `LinearPMap` is closed, `IsSelfAdjoint.isClosed`).
This is the reachable uniqueness content: the closure is the minimal self-adjoint
extension candidate; the strict equality `S = T̄` needs the double-adjoint gap
(`isSelfAdjoint_closure_iff_eq_adjoint`). -/
theorem closure_le_of_isSelfAdjoint_extension {T S : H →ₗ.[ℂ] H} (h : T ≤ S)
    (hS : IsSelfAdjoint S) : T.closure ≤ S :=
  closure_le_of_isClosed_extension h hS.isClosed

/-! ### Gate-0 non-vacuity: the concrete real-scalar witness -/

/-- **Gate-0.** The concrete real-scalar operator `smulPMap c` (`x ↦ (c:ℝ)·x`, full
domain) is symmetric with dense domain, so its closure is symmetric — the entire
extension layer (`closure_isSymmetric`, the inclusion chain, the self-adjointness
criterion, the real-spectrum lemmas) fires on a genuine, everywhere-defined, nonzero
operator, and nothing here is vacuous. -/
theorem smulPMap_closure_isSymmetric (c : ℝ) :
    IsSymmetric (smulPMap (H := H) c).closure :=
  closure_isSymmetric (smulPMap_isSymmetric c) (Brockian.Weyl.Closure.smulPMap_dense c)

/-- **Gate-0 (real spectrum).** Eigenvalues of the closure of the concrete witness
`smulPMap c` are real: the real-spectrum rung `closure_eigenvalue_im_zero` is
non-vacuous. -/
theorem smulPMap_closure_eigenvalue_im_zero (c : ℝ)
    {v : (smulPMap (H := H) c).closure.domain} {μ : ℂ}
    (hv : (v : H) ≠ 0) (heig : (smulPMap (H := H) c).closure v = μ • (v : H)) :
    μ.im = 0 :=
  closure_eigenvalue_im_zero (smulPMap_isSymmetric c)
    (Brockian.Weyl.Closure.smulPMap_dense c) hv heig

end Brockian.Weyl.Extension
