import Mathlib
import Brockian.ConstellationGraph

/-
# Constellation Sieve — Acyclicity sub-brick: the arithmetic core of "the +3 flow is a path".

This is the FIRST sub-brick toward closing the **graph → block-permutation similarity** gate.
Prior bricks packaged the `+3` translation flow on the wheel as
`Brockian.ConstellationGraph.plusThreeGraph (n) : SimpleGraph (ZMod n)` (adjacency `b − a = ±3`),
established maximum degree ≤ 2 (`plus_three_neighbourhood`), and the twin-admissibility run cap
(`twin_run_cap_mod5`, `twin_no_four_run`). A degree-≤2 graph is a disjoint union of paths and
cycles; to conclude the admissible sub-flow is a union of **paths** we need the *acyclicity* fact —
that once the inadmissible residues are deleted the `+3` flow cannot close up into a cycle.

This file supplies the **arithmetic core** of that acyclicity, phrased over `ZMod M`.

WHAT LANDED (all fully proved, no `sorry`/`admit`/`native_decide`/`axiom`):

* **Theorem A — transitivity / reachability of the +3 orbit** (`plusThree_reaches`).
  When `Nat.Coprime 3 M`, `3` is a unit of `ZMod M`, so the pure `+3` step reaches *every* residue:
  `∀ a b, ∃ k : ℕ, a + 3 * (k : ZMod M) = b`. The single `+3` orbit is the whole group.

* **Theorem A′ — the +3 step is a bijection** (`plusThree_bijective`).
  `a ↦ a + 3` is a bijection of `ZMod M` (it is translation by a group element).

* **Theorem B — no short return** (`plusThree_no_short_cycle`), the load-bearing acyclicity fact.
  When `Nat.Coprime 3 M`, for `0 < k < M` we have `a + 3 * (k : ZMod M) ≠ a`: the `+3` walk cannot
  return to its start in fewer than `M` steps. (`3` a unit ⇒ `3·k = 0 ↔ k = 0` in `ZMod M`, and
  `(k : ZMod M) = 0 ↔ M ∣ k`, impossible for `0 < k < M`.) This is the precise arithmetic statement
  that the `+3` flow has no *short* cycle — the fact that breaks the deleted flow into finite paths.

* **Theorem D — an inadmissible residue exists** (`zero_not_twinAdm`, `exists_inadmissible`).
  For `1 < M`, residue `0` is not a unit, hence not twin-admissible; so the twin-admissible vertex
  set is a **proper** subset of `ZMod M`. This is why the single `+3` cycle, once its non-vertex
  residues are removed, is cut open into paths rather than remaining a closed cycle.

WHAT IS *NOT* CLOSED HERE (honest scope): **Theorem C**, the packaged `SimpleGraph` statement
"`plusThreeGraph M` (for `Coprime 3 M`) is a single `M`-cycle, and its induced subgraph on any
proper vertex subset is `SimpleGraph.IsAcyclic`", is **NOT** proved. Turning the arithmetic core
(A, B, D) into a statement in the `SimpleGraph.Walk`/`IsCycle`/induced-subgraph API is a substantial
separate development, and the full graph → block-permutation similarity gate remains **open**. The
theorems below are the honest, verified arithmetic substrate for that future step.
-/

namespace Brockian.ConstellationAcyclic

open Brockian.ConstellationGraph

/-- `3` is a unit of `ZMod M` whenever `Nat.Coprime 3 M`. Shared helper for Theorems A and B. -/
theorem isUnit_three_of_coprime (M : ℕ) [NeZero M] (h3 : Nat.Coprime 3 M) :
    IsUnit (3 : ZMod M) := by
  have h := (ZMod.isUnit_iff_coprime 3 M).mpr h3
  simpa using h

/-- **Theorem A — reachability of the +3 orbit.** When `Nat.Coprime 3 M`, the pure `+3` step is
transitive on `ZMod M`: every residue `b` is reached from every residue `a` by some number of `+3`
steps. Since `3` is a unit, `3·ℤ` is the whole additive group. -/
theorem plusThree_reaches (M : ℕ) [NeZero M] (h3 : Nat.Coprime 3 M) :
    ∀ a b : ZMod M, ∃ k : ℕ, a + 3 * (k : ZMod M) = b := by
  intro a b
  obtain ⟨u, hu'⟩ := isUnit_three_of_coprime M h3
  -- `c` is a right inverse of `3`: `3 * c = 1`.
  set c : ZMod M := (↑u⁻¹ : ZMod M) with hc
  have h3c : (3 : ZMod M) * c = 1 := by
    rw [hc, ← hu']
    simp
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (n := M) (c * (b - a))
  refine ⟨k, ?_⟩
  rw [hk, ← mul_assoc, h3c, one_mul]
  ring

/-- **Theorem A′ — the +3 step is a bijection.** Translation `a ↦ a + 3` is a bijection of
`ZMod M` (inverse `a ↦ a − 3`), so the `+3` flow is a permutation of the residues. -/
theorem plusThree_bijective (M : ℕ) [NeZero M] :
    Function.Bijective (fun a : ZMod M => a + 3) := by
  constructor
  · intro x y h
    exact add_right_cancel h
  · intro y
    exact ⟨y - 3, by ring⟩

/-- **Theorem B — no short return (the acyclicity core).** When `Nat.Coprime 3 M`, a `+3` walk of
length `k` with `0 < k < M` never returns to its start: `a + 3 * (k : ZMod M) ≠ a`.

Because `3` is a unit, `3 * (k : ZMod M) = 0` forces `(k : ZMod M) = 0`, i.e. `M ∣ k`, impossible
for `0 < k < M`. Thus the `+3` flow admits no cycle shorter than the full modulus — the arithmetic
fact that, after deleting inadmissible residues, breaks the flow into finite paths. -/
theorem plusThree_no_short_cycle (M : ℕ) [NeZero M] (a : ZMod M) (k : ℕ)
    (hk : 0 < k) (hkM : k < M) (h3 : Nat.Coprime 3 M) :
    a + 3 * (k : ZMod M) ≠ a := by
  intro h
  have hu : IsUnit (3 : ZMod M) := isUnit_three_of_coprime M h3
  have h0 : (3 : ZMod M) * (k : ZMod M) = 0 := by linear_combination h
  have hk0 : (k : ZMod M) = 0 := (hu.mul_right_eq_zero).mp h0
  have hdvd : M ∣ k := (ZMod.natCast_eq_zero_iff k M).mp hk0
  have hle : M ≤ k := Nat.le_of_dvd hk hdvd
  omega

/-- **Theorem D — `0` is not twin-admissible.** For `1 < M`, `ZMod M` is nontrivial, so `0` is not a
unit and hence `0` fails twin-admissibility. -/
theorem zero_not_twinAdm (M : ℕ) [NeZero M] (hM : 1 < M) :
    ¬ twinAdm (0 : ZMod M) := by
  haveI : Fact (1 < M) := ⟨hM⟩
  rintro ⟨h0, _⟩
  exact not_isUnit_zero h0

/-- **Theorem D (corollary) — the admissible vertex set is a proper subset.** For `1 < M` there is a
residue (namely `0`) that is not twin-admissible, so the twin-admissible vertices form a *proper*
subset of `ZMod M`. This properness is what cuts the single `+3` cycle open into paths. -/
theorem exists_inadmissible (M : ℕ) [NeZero M] (hM : 1 < M) :
    ∃ v : ZMod M, ¬ twinAdm v :=
  ⟨0, zero_not_twinAdm M hM⟩

end Brockian.ConstellationAcyclic
