import Mathlib
import Brockian.ConstellationGraph
import Brockian.ConstellationAcyclic

/-
# Constellation Sieve — the SimpleGraph acyclicity of the twin-admissible `+3` flow.

This file closes the **last open piece** of the graph → block-permutation similarity gate that the
arithmetic sub-brick `Brockian.ConstellationAcyclic` left explicitly open ("Theorem C"): the fully
packaged `SimpleGraph.IsAcyclic` statement for the twin-admissible induced subgraph of the `+3`
flow.

## What is VERIFIED here (no `sorry`/`admit`/`native_decide`/`axiom`)

* `intLine` / `intLine_isAcyclic` — the integer line graph on `ℤ` (adjacency `|a − b| = 1`) is
  acyclic. Proved via `isAcyclic_iff_forall_adj_isBridge`: every edge `{m, m+1}` is a bridge,
  because the predicate `x ≤ m` is invariant along every walk in the edge-deleted graph, so `m` and
  `m + 1` become unreachable.

* `twin_admissible_induced_acyclic` — **THE PRIZE.** For `Nat.Coprime 3 M` and `1 < M`, the induced
  subgraph of `Brockian.ConstellationGraph.plusThreeGraph M` on the twin-admissible vertex set
  `{a | twinAdm a}` is `SimpleGraph.IsAcyclic`.

## The proof idea (Route 2, made effective)

When `Nat.Coprime 3 M`, `3` is a unit of `ZMod M` with inverse `c`. The **position map**
`pos a = (c * a).val : ℤ` sends the `+3` step to a `+1` step: if `b − a = 3` then
`c·b = c·a + 1`, and the `+3` flow becomes the standard `M`-cycle `0, 3, 6, …` re-indexed by
`pos`. The *only* wrap-around of `pos` (from `M − 1` back to `0`) happens at the residue `0`, which
is **not twin-admissible** (`zero_not_twinAdm`). Hence, restricted to the admissible vertices, `pos`
is an **injective graph homomorphism into `intLine`**: admissible neighbours have `pos`-values that
differ by *exactly* `±1` in `ℤ` (never the wrap `±(M−1)`, since that requires a `pos`-value `0`,
i.e. the inadmissible residue `0`). Acyclicity then transports back along the injective hom via
`SimpleGraph.IsAcyclic.comap`.

This is the graph-theoretic translation of the arithmetic substrate
(`plusThree_no_short_cycle`, `zero_not_twinAdm`): the properness of the admissible vertex set cuts
the single `+3`-cycle open into a forest of paths. The full `IsAcyclic` gate is now **closed**.
-/

namespace Brockian.ConstellationGraphAcyclic

open Brockian.ConstellationGraph
open Brockian.ConstellationAcyclic
open SimpleGraph

/-- The integer line graph on `ℤ`: `a` and `b` are adjacent iff they differ by `1`. This is a
disjoint countable union of the two rays, i.e. a bi-infinite path — acyclic. -/
def intLine : SimpleGraph ℤ where
  Adj a b := a - b = 1 ∨ b - a = 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

theorem intLine_adj {a b : ℤ} : intLine.Adj a b ↔ a - b = 1 ∨ b - a = 1 := Iff.rfl

/-- A predicate preserved along single adjacencies of a graph is preserved along any walk. -/
private theorem walk_pred {V : Type*} {K : SimpleGraph V} {p : V → Prop}
    (hp : ∀ ⦃a b⦄, K.Adj a b → p a → p b) : ∀ {u v : V}, K.Walk u v → p u → p v := by
  intro u v w
  induction w with
  | nil => exact fun h => h
  | cons hadj _ ih => exact fun h => ih (hp hadj h)

/-- Every edge `{m, m+1}` of the integer line is a bridge: deleting it, the potential `x ≤ m` is
invariant along walks, so `m` and `m + 1` become unreachable. -/
theorem intLine_isBridge (m : ℤ) : intLine.IsBridge s(m, m + 1) := by
  rw [isBridge_iff]
  rintro ⟨w⟩
  have hp : ∀ ⦃a b : ℤ⦄, (intLine.deleteEdges {s(m, m + 1)}).Adj a b → a ≤ m → b ≤ m := by
    intro a b hab ha
    rw [SimpleGraph.deleteEdges_adj, intLine_adj] at hab
    obtain ⟨hadj, hne⟩ := hab
    rcases hadj with h1 | h1
    · omega
    · by_cases hbm : b ≤ m
      · exact hbm
      · push_neg at hbm
        exfalso
        apply hne
        rw [Set.mem_singleton_iff]
        have hA : a = m := by omega
        have hB : b = m + 1 := by omega
        rw [hA, hB]
  have hmm : m + 1 ≤ m := walk_pred hp w (le_refl m)
  omega

/-- **The integer line graph is acyclic.** Every edge is a bridge, so by
`isAcyclic_iff_forall_adj_isBridge` the graph has no cycle. -/
theorem intLine_isAcyclic : intLine.IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rw [intLine_adj] at hvw
  rcases hvw with h | h
  · have hv : v = w + 1 := by omega
    subst hv
    rw [Sym2.eq_swap]
    exact intLine_isBridge w
  · have hw : w = v + 1 := by omega
    subst hw
    exact intLine_isBridge v

/-- **THE PRIZE — the twin-admissible induced `+3` flow is acyclic.** For `Nat.Coprime 3 M` and
`1 < M`, the induced subgraph of `plusThreeGraph M` on the twin-admissible vertices is acyclic.

The position map `pos a = (3⁻¹ · a).val` is an injective graph homomorphism from the induced graph
into `intLine`: a `+3` (resp. `−3`) step becomes a `+1` (resp. `−1`) step of `pos`, and the sole
wrap-around of `pos` occurs at the residue `0`, which is inadmissible (`zero_not_twinAdm`); hence
admissible neighbours have `pos`-values differing by exactly `±1` in `ℤ`. Acyclicity of `intLine`
transports back through `SimpleGraph.IsAcyclic.comap`. -/
theorem twin_admissible_induced_acyclic (M : ℕ) [NeZero M] (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    (SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)).IsAcyclic := by
  haveI : Fact (1 < M) := ⟨hM⟩
  -- `c = 3⁻¹` in `ZMod M`.
  obtain ⟨u, hu⟩ := isUnit_three_of_coprime M h3
  set c : ZMod M := (↑u⁻¹ : ZMod M) with hc
  have h3c : (3 : ZMod M) * c = 1 := by rw [hc, ← hu]; simp
  have hcu : IsUnit c := by rw [hc]; exact (u⁻¹).isUnit
  -- The `+1` step of `val` has no wrap-around unless the result is `0`.
  have valstep : ∀ x : ZMod M, x + 1 ≠ 0 → (x + 1).val = x.val + 1 := by
    intro x hx
    have hlt : x.val < M := ZMod.val_lt x
    have hval : (x + 1).val = (x.val + 1) % M := by rw [ZMod.val_add, ZMod.val_one]
    rcases Nat.lt_or_ge (x.val + 1) M with h | h
    · rw [hval, Nat.mod_eq_of_lt h]
    · exfalso
      apply hx
      have he : x.val + 1 = M := by omega
      rw [← ZMod.val_eq_zero, hval, he, Nat.mod_self]
  -- Admissible residues have nonzero `c`-image (since `c` is a unit and `0` is inadmissible).
  have hcne : ∀ a : ZMod M, twinAdm a → c * a ≠ 0 := by
    intro a ha hz
    have h0 : c * a = c * 0 := by rw [mul_zero]; exact hz
    have hae : a = 0 := hcu.mul_right_injective h0
    rw [hae] at ha
    exact zero_not_twinAdm M hM ha
  -- The position map as an injective graph homomorphism into the integer line.
  refine intLine_isAcyclic.comap
    (G := SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M))
    { toFun := fun a => ((c * (a : ZMod M)).val : ℤ)
      map_rel' := ?_ } ?_
  · -- map_rel': admissible adjacency maps to a `±1` step of `pos`.
    intro a b hab
    obtain ⟨hstep, _⟩ := hab
    simp only [Function.Embedding.coe_subtype] at hstep
    rw [intLine_adj]
    rcases hstep with hstep | hstep
    · -- (↑b − ↑a = 3) ⇒ c·b = c·a + 1 ⇒ pos b = pos a + 1.
      right
      have hBA : c * (b : ZMod M) = c * (a : ZMod M) + 1 := by
        linear_combination c * hstep + h3c
      have hBne : c * (a : ZMod M) + 1 ≠ 0 := hBA ▸ hcne _ b.2
      have hv : (c * (b : ZMod M)).val = (c * (a : ZMod M)).val + 1 := by
        rw [hBA, valstep _ hBne]
      rw [hv]; push_cast; ring
    · -- (↑a − ↑b = 3) ⇒ c·a = c·b + 1 ⇒ pos a = pos b + 1.
      left
      have hAB : c * (a : ZMod M) = c * (b : ZMod M) + 1 := by
        linear_combination c * hstep + h3c
      have hAne : c * (b : ZMod M) + 1 ≠ 0 := hAB ▸ hcne _ a.2
      have hv : (c * (a : ZMod M)).val = (c * (b : ZMod M)).val + 1 := by
        rw [hAB, valstep _ hAne]
      rw [hv]; push_cast; ring
  · -- injectivity of `pos`.
    intro a b hab
    have hab' : ((c * (a : ZMod M)).val : ℤ) = ((c * (b : ZMod M)).val : ℤ) := hab
    have h1 : (c * (a : ZMod M)).val = (c * (b : ZMod M)).val := by exact_mod_cast hab'
    have h2 : c * (a : ZMod M) = c * (b : ZMod M) := ZMod.val_injective M h1
    have h3' : (a : ZMod M) = (b : ZMod M) := (hcu.mul_right_inj).mp h2
    exact Subtype.ext h3'

end Brockian.ConstellationGraphAcyclic
