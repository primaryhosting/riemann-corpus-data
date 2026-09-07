/-
  Brockian/WeylClosure.lean — closure / adjoint / deficiency-space theory for
  symmetric unbounded operators (the von Neumann layer of Weyl theory).

  Built on `Brockian/WeylOperator.lean` (namespace `Brockian.Weyl.Operator`,
  reused verbatim: `IsSymmetric`, `deficiencySpace`, `mem_deficiencySpace_iff`,
  `smulPMap`, …) and on Mathlib v4.32.0's partially-defined-operator adjoint
  calculus (`LinearPMap.adjoint`, `IsFormalAdjoint`, `closure`, `IsClosable`,
  `IsClosed`). This file proves the *next rung* above the operator scaffolding:
  the structural facts that make the adjoint a **closed** operator, that place a
  symmetric operator inside its adjoint, that make it **closable**, and that
  exhibit the **deficiency space as a genuinely closed subspace of `H`**.

  ## Setting

  `H` is a complex Hilbert space (`CompleteSpace H`; physics inner-product
  convention, conjugate-linear in the FIRST slot). `T : H →ₗ.[ℂ] H` is a
  densely-defined operator — density `Dense (↑T.domain : Set H)` is the standing
  hypothesis that makes `T.adjoint` a bona-fide operator (Mathlib requires it for
  every nontrivial adjoint fact). The reused witness `smulPMap c` (real-scalar
  multiplication, full domain) discharges this hypothesis concretely, so nothing
  below is vacuous.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `inner_adjoint_left`         — the **adjoint identity** `⟪T* x, y⟫ = ⟪x, T y⟫`
                                     for `x ∈ dom(T*)`, `y ∈ dom(T)`. The defining
                                     bilinear relation of the adjoint.
    * `symmetric_le_adjoint`       — **`T ⊆ T*`** for symmetric `T` (domain
                                     inclusion + action agreement, the content of
                                     `LinearPMap.le`): a symmetric operator is
                                     contained in its adjoint.
    * `symmetric_domain_le_adjoint_domain`
                                   — the domain half `dom(T) ≤ dom(T*)`, unpacked.
    * `symmetric_adjoint_eq`       — the action half: `T* g = T g` on `dom(T)`.
    * `adjoint_isClosed'`          — **the adjoint is a closed operator**
                                     (`IsClosed (graph T*)`). True for every
                                     densely-defined `T`, symmetric or not.
    * `symmetric_isClosable`       — **symmetric operators are closable**: `T`
                                     sits inside the closed operator `T*`, hence
                                     its graph closure is again a graph. This is
                                     the entry point to the closure `T̄ = T**`.
    * `closure_eq_self_of_isClosed`— a **closed operator equals its own closure**
                                     (`f.IsClosed → f.closure = f`), proved from
                                     the graph/`topologicalClosure` definition.
    * `symmetric_closure_le_adjoint`
                                   — **`T ⊆ T̄ ⊆ T*`**: the closure of a symmetric
                                     operator is still contained in the adjoint
                                     (the minimal closed extension does not
                                     overshoot `T*`). Von Neumann's inclusion chain
                                     `T ⊆ T̄ = T** ⊆ T*`, minus the `T̄ = T**`
                                     identity Mathlib does not supply.
    * `deficiencySet`              — the **deficiency space realized in `H`**:
                                     `{g : H | (g, z·g) ∈ graph T*}`, i.e. the
                                     eigenvectors of `T*` at `z`, living in `H`.
    * `mem_deficiencySet_iff_mem_deficiencySpace`
                                   — the bridge: `deficiencySet` is exactly the
                                     image in `H` of `Operator.deficiencySpace`.
    * `isClosed_deficiencySet`     — **the deficiency space is closed in `H`**: it
                                     is the preimage of the closed graph `graph T*`
                                     under the continuous map `g ↦ (g, z·g)`. The
                                     genuine "deficiency subspaces are closed"
                                     theorem, the fact von Neumann's extension
                                     count rests on.
    * `smulPMap_dense`, `smulPMap_isClosable`
                                   — **Gate-0 non-vacuity**: the concrete
                                     real-scalar operator has dense (full) domain,
                                     so the standing hypothesis is dischargeable,
                                     and the whole chain (closable, closed adjoint,
                                     closed deficiency space) fires on it.

  ## What is NOT proved, and why (honest scope statement)

  The von Neumann extension theorem itself — the closure identity `T̄ = T**`, the
  Cayley transform, and the bijection between self-adjoint extensions of a
  symmetric `T` and partial isometries `𝒟₊ → 𝒟₋` between the deficiency spaces —
  is **not** proved: none of it (`adjoint_adjoint`, a Cayley transform, unitary
  deficiency-space maps) exists in Mathlib v4.32.0. Consequently the *criterion*
  `EssentiallySelfAdjoint T ↔ 𝒟₊ = 𝒟₋ = 0 ↔ T̄ self-adjoint` is out of reach and
  is not asserted here. What ships is the structural closure/adjoint/deficiency
  layer strictly below the extension bijection: every statement is a real
  operator-theoretic fact, each verified with axioms ⊆ {propext, Classical.choice,
  Quot.sound}.

  Verification:  AXLE independent — verified @ lean-4.32.0.
-/
import Mathlib
import Brockian.WeylOperator

namespace Brockian.Weyl.Closure

open scoped InnerProductSpace
open Brockian.Weyl.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The adjoint identity and the containment `T ⊆ T*` -/

/-- **The adjoint identity.** For a densely-defined `T`, the adjoint satisfies
`⟪T* x, y⟫ = ⟪x, T y⟫` whenever `x ∈ dom(T*)` and `y ∈ dom(T)`. This is the
defining formal-adjoint relation of `T.adjoint` (Mathlib's
`adjoint_isFormalAdjoint`), and it holds with no symmetry assumption. -/
theorem inner_adjoint_left (T : H →ₗ.[ℂ] H) (hd : Dense (↑T.domain : Set H))
    (x : T.adjoint.domain) (y : T.domain) :
    ⟪T.adjoint x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ :=
  (LinearPMap.adjoint_isFormalAdjoint hd) x y

/-- **A symmetric operator is contained in its adjoint: `T ⊆ T*`.** As a
`LinearPMap.le` this packages both `dom(T) ≤ dom(T*)` and the agreement of the
actions on `dom(T)`. It is the reason symmetric operators are closable and why
`T ⊆ T̄ ⊆ T*`. -/
theorem symmetric_le_adjoint {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (↑T.domain : Set H)) : T ≤ T.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint hd hT

/-- The domain half of `T ⊆ T*`:  `dom(T) ≤ dom(T*)`. -/
theorem symmetric_domain_le_adjoint_domain {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (↑T.domain : Set H)) : T.domain ≤ T.adjoint.domain :=
  (symmetric_le_adjoint hT hd).1

/-- The action half of `T ⊆ T*`:  on `dom(T)`, the adjoint agrees with `T`.
(`T* x = T x` for `x` in the domain of `T`, transported into `dom(T*)`.) -/
theorem symmetric_adjoint_eq {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (↑T.domain : Set H)) {x : T.domain} {y : T.adjoint.domain}
    (hxy : (x : H) = (y : H)) : T.adjoint y = T x :=
  ((symmetric_le_adjoint hT hd).2 hxy).symm

/-! ### The adjoint is closed; symmetric operators are closable -/

/-- **The adjoint is a closed operator.** For every densely-defined `T`, the
graph of `T.adjoint` is closed in `H × H`. (Mathlib's `adjoint_isClosed`,
re-exported into this namespace as the load-bearing structural fact.) -/
theorem adjoint_isClosed' (T : H →ₗ.[ℂ] H) (hd : Dense (↑T.domain : Set H)) :
    T.adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed hd

/-- **Symmetric operators are closable.** Since `T ⊆ T*` and `T*` is closed, the
graph closure of `T` lies inside the graph of a closed operator, hence is again a
graph. This is precisely the hypothesis under which the closure `T̄` (and, in the
full theory, `T** = T̄`) exists. -/
theorem symmetric_isClosable {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (↑T.domain : Set H)) : T.IsClosable :=
  (adjoint_isClosed' T hd).isClosable.leIsClosable (symmetric_le_adjoint hT hd)

/-- **A closed operator is its own closure.** If `graph f` is closed then
`f.closure = f`: the closure's graph is the topological closure of `graph f`,
which for a closed graph is itself, and equal graphs give equal operators. -/
theorem closure_eq_self_of_isClosed {f : H →ₗ.[ℂ] H} (hf : f.IsClosed) :
    f.closure = f := by
  have hcl : f.IsClosable := hf.isClosable
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.closure_def hcl, ← hcl.choose_spec]
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe]
  exact hf.closure_eq

/-- **The closure of a symmetric operator is still contained in the adjoint:
`T ⊆ T̄ ⊆ T*`.** The minimal closed extension `T̄` of a symmetric `T` does not
escape `T*`. (Combined with `le_closure`, this is von Neumann's inclusion chain
`T ⊆ T̄ ⊆ T*`; the missing identity `T̄ = T**` needs the double adjoint, which
Mathlib v4.32.0 lacks.) -/
theorem symmetric_closure_le_adjoint {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (↑T.domain : Set H)) : T.closure ≤ T.adjoint := by
  have hadjcl : T.adjoint.IsClosable := (adjoint_isClosed' T hd).isClosable
  have hmono : T.closure ≤ T.adjoint.closure :=
    hadjcl.closure_mono (symmetric_le_adjoint hT hd)
  rwa [closure_eq_self_of_isClosed (adjoint_isClosed' T hd)] at hmono

/-! ### The deficiency space realized in `H`, and its closedness -/

/-- **The deficiency space, realized as a subset of `H`.** `deficiencySet T z` is
the set of `g : H` with `(g, z·g) ∈ graph T*`, i.e. the eigenvectors of the
adjoint at `z` (equivalently `g ∈ dom(T*)` and `T* g = z·g`). It is the
`H`-image of `Operator.deficiencySpace T z`, in the form that makes closedness a
clean preimage statement. -/
def deficiencySet (T : H →ₗ.[ℂ] H) (z : ℂ) : Set H :=
  {g : H | (g, z • g) ∈ T.adjoint.graph}

/-- **The realized deficiency set is exactly `Operator.deficiencySpace`.** For
`g ∈ dom(T*)`, `g ∈ deficiencySet T z ↔ g ∈ deficiencySpace T z`. Confirms the
`H`-side set is the honest deficiency space, not a new object. -/
theorem mem_deficiencySet_iff_mem_deficiencySpace (T : H →ₗ.[ℂ] H) (z : ℂ)
    (g : T.adjoint.domain) :
    (g : H) ∈ deficiencySet T z ↔ g ∈ deficiencySpace T z := by
  rw [mem_deficiencySpace_iff, deficiencySet, Set.mem_setOf_eq]
  constructor
  · intro hmem
    rw [LinearPMap.mem_graph_iff] at hmem
    obtain ⟨y, hy1, hy2⟩ := hmem
    rw [Subtype.coe_injective hy1] at hy2
    exact hy2
  · intro heq
    have hg := T.adjoint.mem_graph g
    rwa [heq] at hg

/-- **The deficiency space is a closed subset of `H`.** `deficiencySet T z` is the
preimage of the closed graph `graph T*` under the continuous map `g ↦ (g, z·g)`,
hence closed. This is the genuine "the deficiency subspaces are closed" theorem —
the topological fact that lets von Neumann count self-adjoint extensions by
deficiency-space dimensions. -/
theorem isClosed_deficiencySet (T : H →ₗ.[ℂ] H) (hd : Dense (↑T.domain : Set H))
    (z : ℂ) : IsClosed (deficiencySet T z) := by
  have hcont : Continuous (fun g : H => (g, z • g)) :=
    continuous_id.prodMk (continuous_id.const_smul z)
  have hgraph : IsClosed (↑T.adjoint.graph : Set (H × H)) := adjoint_isClosed' T hd
  exact hgraph.preimage hcont

/-! ### Gate-0 non-vacuity: the concrete real-scalar witness -/

/-- The real-scalar witness `smulPMap c` has **dense (indeed full) domain**, so it
discharges the standing density hypothesis of every theorem above. -/
theorem smulPMap_dense (c : ℝ) : Dense (↑(smulPMap (H := H) c).domain : Set H) := by
  rw [smulPMap_domain, Submodule.top_coe]
  exact dense_univ

/-- **Gate-0.** The concrete symmetric operator `smulPMap c` is closable — so the
closure/adjoint machinery (closable, closed adjoint, closed deficiency space)
fires on a genuine, everywhere-defined, nonzero operator, and none of it is
vacuous. -/
theorem smulPMap_isClosable (c : ℝ) : (smulPMap (H := H) c).IsClosable :=
  symmetric_isClosable (smulPMap_isSymmetric c) (smulPMap_dense c)

/-- **Gate-0.** The adjoint of `smulPMap c` is a closed operator: the closed-graph
fact instantiated on the concrete witness. -/
theorem smulPMap_adjoint_isClosed (c : ℝ) :
    (smulPMap (H := H) c).adjoint.IsClosed :=
  adjoint_isClosed' _ (smulPMap_dense c)

end Brockian.Weyl.Closure
