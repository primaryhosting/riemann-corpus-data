import Mathlib
import Brockian.ConstellationGraph
import Brockian.ConstellationAcyclic
import Brockian.ConstellationGraphAcyclic
import Brockian.ConstellationPaths

/-
# Constellation Sieve — the adjacency-matrix → block-diagonal bridge attempt (the FINAL gate).

This file is the honest final-gate attempt on the graph `adjMatrix → block-diagonal / spectrum-
containment` step for the twin-admissible `+3` constellation graph
`G M := SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)`.

Upstream, everything *around* this step is closed:
* `Brockian.ConstellationGraphAcyclic.twin_admissible_induced_acyclic` — `G M` is `IsAcyclic`;
* `Brockian.ConstellationPaths.forest_of_paths` — `G M` is acyclic with degree ≤ 2 (a forest of
  paths), and `no_four_vertex_plus_three_chain` caps each component at ≤ 3 vertices;
* `Brockian.ConstellationGlobalSpectrum.H123_spectrum` — the assembled block operator
  `H₁ ⊕ H₂ ⊕ H₃` has EXACT spectrum `{2−√2, 1, 2, 3, 2+√2}`.

## What is VERIFIED here (no `sorry`/`admit`/`native_decide`/`axiom`)

The acyclicity brick built only an injective graph *homomorphism* `pos : G M →g intLine`
(`pos a = (3⁻¹·a).val : ℤ`) — enough for `IsAcyclic.comap`. This file upgrades that to the
**strongest true structural bridge available without the matrix-reindexing API**:

* `G_embeds_intLine` — **`pos` is a graph EMBEDDING** `G M ↪g intLine` (a `SimpleGraph.Embedding`,
  i.e. an *induced*-subgraph embedding: `intLine.Adj (pos a) (pos b) ↔ (G M).Adj a b`, both
  directions). The reverse direction reproves the acyclicity Hom; the forward direction is the new
  content: if the `pos`-images of two admissible residues are integer-consecutive, then the residues
  are genuinely `±3`-adjacent (no spurious integer-line edges are introduced). Hence **`G M` is
  isomorphic to an induced subgraph of the integer line graph** — precisely the statement that each
  connected component of `G M` is a *contiguous integer interval* (an honest structural path), which
  is the missing bridge from "forest of ≤3-paths" toward the block-diagonal form.

* `G_isAcyclic_of_embedding` — a re-derivation of `G M`'s acyclicity *through* the embedding
  (`intLine_isAcyclic.comap`), showing the embedding subsumes the earlier Hom-only result.

## What remains the OPEN gate (honest scope — NOT faked here)

The last step — reindexing `SimpleGraph.adjMatrix ℝ (G M)` by connected component into an explicit
block-diagonal `⨁ Pₖ` of path-adjacency blocks (`k ≤ 3`), and thereby transporting
`H123_spectrum` to the graph Hamiltonian `2•I − adjMatrix ℝ (G M)` — is **NOT** established here.
Mathlib provides no cheap `SimpleGraph.ConnectedComponent → Matrix.reindex` block-decomposition of
the adjacency matrix over `ℝ`, so `TARGET 1` (block reindexing) and `TARGET 2` (spectrum containment
of the graph Hamiltonian) do not close. The `adjMatrix → block` bridge is therefore still **OPEN**.
What this file adds is the exact structural fact that would feed such a reindexing: the components of
`G M` are integer intervals (`G_embeds_intLine`). We do not fake the reindexing.

Verification: no `sorry` / `admit` / `axiom` / `native_decide`. Core Mathlib only.
-/

namespace Brockian.ConstellationAdjBridge

open Brockian.ConstellationGraph
open Brockian.ConstellationAcyclic
open Brockian.ConstellationGraphAcyclic
open SimpleGraph

/-- **The `pos`-embedding of the twin-admissible `+3` graph into the integer line.**

For `Nat.Coprime 3 M` and `1 < M`, the position map `pos a = (3⁻¹·a).val : ℤ` is a graph
*embedding* `G M ↪g intLine`: `intLine.Adj (pos a) (pos b) ↔ (G M).Adj a b`.

The reverse implication (`+3`-adjacency ⇒ integer-consecutive `pos`) is the acyclicity Hom. The
forward implication (integer-consecutive `pos` ⇒ `+3`-adjacency) is the new content: if
`(3⁻¹·a).val` and `(3⁻¹·b).val` differ by exactly `1` in `ℤ`, then `3⁻¹·a = 3⁻¹·b ± 1` in `ZMod M`,
so `a − b = ±3`; no non-`+3` edge of the integer line has both endpoints in the `pos`-image of the
admissible vertices. Hence `G M` is (isomorphic to) an **induced subgraph of the integer line** — its
connected components are contiguous integer intervals. -/
theorem G_embeds_intLine (M : ℕ) [NeZero M] (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    Nonempty ((Brockian.ConstellationPaths.G M) ↪g intLine) := by
  haveI : Fact (1 < M) := ⟨hM⟩
  -- `c = 3⁻¹` in `ZMod M`.
  obtain ⟨u, hu⟩ := isUnit_three_of_coprime M h3
  set c : ZMod M := (↑u⁻¹ : ZMod M) with hc
  have h3c : (3 : ZMod M) * c = 1 := by rw [hc, ← hu]; simp
  have hcu : IsUnit c := by rw [hc]; exact (u⁻¹).isUnit
  have h3ne : (3 : ZMod M) ≠ 0 := (isUnit_three_of_coprime M h3).ne_zero
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
  -- Admissible residues have nonzero `c`-image.
  have hcne : ∀ a : ZMod M, twinAdm a → c * a ≠ 0 := by
    intro a ha hz
    have h0 : c * a = c * 0 := by rw [mul_zero]; exact hz
    have hae : a = 0 := hcu.mul_right_injective h0
    rw [hae] at ha
    exact zero_not_twinAdm M hM ha
  -- Cast recovery: `((c*a).val : ZMod M) = c*a`.
  have hrecover : ∀ a : ZMod M, (((c * a).val : ℕ) : ZMod M) = c * a := by
    intro a; exact ZMod.natCast_rightInverse (c * a)
  refine ⟨⟨⟨fun a => ((c * (a : ZMod M)).val : ℤ), ?_⟩, ?_⟩⟩
  · -- injectivity of `pos`.
    intro a b hab
    have hab' : ((c * (a : ZMod M)).val : ℤ) = ((c * (b : ZMod M)).val : ℤ) := hab
    have h1 : (c * (a : ZMod M)).val = (c * (b : ZMod M)).val := by exact_mod_cast hab'
    have h2 : c * (a : ZMod M) = c * (b : ZMod M) := by
      rw [← hrecover (a : ZMod M), ← hrecover (b : ZMod M), h1]
    have h3' : (a : ZMod M) = (b : ZMod M) := (hcu.mul_right_inj).mp h2
    exact Subtype.ext h3'
  · -- `map_rel_iff'`: `intLine.Adj (pos a) (pos b) ↔ (G M).Adj a b`.
    intro a b
    rw [Brockian.ConstellationPaths.G_adj]
    simp only [intLine_adj, Function.Embedding.coeFn_mk]
    constructor
    · -- FORWARD (new): integer-consecutive `pos` ⇒ `±3`-adjacency of residues.
      intro hInt
      rcases hInt with hI | hI
      · -- `pos a − pos b = 1` ⇒ `↑a − ↑b = 3`.
        have hnat : (c * (a : ZMod M)).val = (c * (b : ZMod M)).val + 1 := by omega
        have hXY : c * (a : ZMod M) = c * (b : ZMod M) + 1 := by
          have hc2 := congrArg (Nat.cast : ℕ → ZMod M) hnat
          push_cast at hc2
          rw [hrecover a, hrecover b] at hc2
          exact hc2
        have hone : c * ((a : ZMod M) - (b : ZMod M)) = 1 := by linear_combination hXY
        have hd : (a : ZMod M) - (b : ZMod M) = 3 := by
          linear_combination 3 * hone - ((a : ZMod M) - (b : ZMod M)) * h3c
        refine ⟨Or.inr hd, ?_⟩
        intro hab0
        apply h3ne
        rw [← hd, hab0, sub_self]
      · -- `pos b − pos a = 1` ⇒ `↑b − ↑a = 3`.
        have hnat : (c * (b : ZMod M)).val = (c * (a : ZMod M)).val + 1 := by omega
        have hXY : c * (b : ZMod M) = c * (a : ZMod M) + 1 := by
          have hc2 := congrArg (Nat.cast : ℕ → ZMod M) hnat
          push_cast at hc2
          rw [hrecover b, hrecover a] at hc2
          exact hc2
        have hone : c * ((b : ZMod M) - (a : ZMod M)) = 1 := by linear_combination hXY
        have hd : (b : ZMod M) - (a : ZMod M) = 3 := by
          linear_combination 3 * hone - ((b : ZMod M) - (a : ZMod M)) * h3c
        refine ⟨Or.inl hd, ?_⟩
        intro hab0
        apply h3ne
        rw [← hd, hab0, sub_self]
    · -- REVERSE (acyclicity Hom): `±3`-adjacency ⇒ integer-consecutive `pos`.
      intro hG
      obtain ⟨hstep, _⟩ := hG
      rcases hstep with hstep | hstep
      · right
        have hBA : c * (b : ZMod M) = c * (a : ZMod M) + 1 := by
          linear_combination c * hstep + h3c
        have hBne : c * (a : ZMod M) + 1 ≠ 0 := hBA ▸ hcne _ b.2
        have hv : (c * (b : ZMod M)).val = (c * (a : ZMod M)).val + 1 := by
          rw [hBA, valstep _ hBne]
        rw [hv]; push_cast; ring
      · left
        have hAB : c * (a : ZMod M) = c * (b : ZMod M) + 1 := by
          linear_combination c * hstep + h3c
        have hAne : c * (b : ZMod M) + 1 ≠ 0 := hAB ▸ hcne _ a.2
        have hv : (c * (a : ZMod M)).val = (c * (b : ZMod M)).val + 1 := by
          rw [hAB, valstep _ hAne]
        rw [hv]; push_cast; ring

/-- **Acyclicity through the embedding.** The `G M ↪g intLine` embedding re-derives the acyclicity
of `G M` (via `intLine_isAcyclic.comap`), so the embedding subsumes the earlier Hom-only acyclicity
result `twin_admissible_induced_acyclic`. -/
theorem G_isAcyclic_of_embedding (M : ℕ) [NeZero M] (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    (Brockian.ConstellationPaths.G M).IsAcyclic := by
  obtain ⟨f⟩ := G_embeds_intLine M h3 hM
  exact intLine_isAcyclic.comap f.toHom f.injective

end Brockian.ConstellationAdjBridge
