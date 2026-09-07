/-
  Brockian/AutomorphismFull.lean — the REVERSE bound that completes `Aut(C₅) ≅ D₅`.

  This module supplies the upper bound `|Aut(C₅)| ≤ 10` that `Brockian.Automorphism`
  left open (see its module note), and consequently the full flagship isomorphism
  `Aut(C₅) ≃* D₅`.

  ── The pinning argument ──
    A graph automorphism `σ` of the 5-cycle is determined by `σ 0` and `σ 1`, and
    `σ 1` must be a neighbour of `σ 0` (i.e. `σ 0 ± 1`). Concretely we prove the
    canonical-form theorem `dihedralHom_surjective`: EVERY automorphism of `C₅`
    equals `dihedralHom g` for some dihedral `g` — a rotation if `σ 1 = σ 0 + 1`,
    a reflection if `σ 1 = σ 0 - 1`. The five vertex-values are forced one by one:
    `σ (k+1)` is a neighbour of `σ k`, and injectivity of `σ` rules out the "wrong"
    neighbour (the one already used), so the step `σ (k+1) - σ k` is constant.

  ── What is PROVED here ──
    * `dihedralHom_surjective` — `dihedralHom : D₅ →* Aut(C₅)` is surjective.
    * `dihedralHom_bijective`  — hence bijective (with `dihedral_action_faithful`).
    * `autEquivDihedral`       — the group isomorphism `D₅ ≃* Aut(C₅)`.
    * `aut_equiv_dihedral`     — `Nonempty (D₅ ≃* Aut(C₅))`.
    * `aut_card_eq_ten`        — `Nat.card (C₅ ≃g C₅) = 10`.
    * `card_aut_le_ten`        — the reverse bound `Nat.card (C₅ ≃g C₅) ≤ 10`.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.Automorphism

namespace Brockian.Automorphism.Full

open SimpleGraph
open DihedralGroup
open Brockian.Automorphism

/-- Neighbour disjunction for a graph automorphism of `C₅`: if `a`, `b` are adjacent
in `C₅` then their images differ by `±1` in the `Fin 5` cyclic ring. -/
private lemma img_diff (σ : C5 ≃g C5) {a b : Fin 5} (hab : C5.Adj a b) :
    σ a - σ b = 1 ∨ σ b - σ a = 1 := by
  have h : C5.Adj (σ a) (σ b) := σ.map_adj_iff.mpr hab
  simpa only [C5, cycleGraph_adj] using h

/-- **Canonical form of a `C₅` automorphism (the reverse bound).**
Every graph automorphism of the 5-cycle is realized by the dihedral action:
`dihedralHom : D₅ →* Aut(C₅)` is surjective. -/
theorem dihedralHom_surjective : Function.Surjective dihedralHom := by
  intro σ
  have hinj : Function.Injective (σ : Fin 5 → Fin 5) := σ.toEquiv.injective
  -- the four consecutive-edge neighbour disjunctions (`σ (k+1) = σ k ± 1`)
  have h01 := img_diff σ (show C5.Adj (0 : Fin 5) 1 by decide)
  have h12 := img_diff σ (show C5.Adj (1 : Fin 5) 2 by decide)
  have h23 := img_diff σ (show C5.Adj (2 : Fin 5) 3 by decide)
  have h34 := img_diff σ (show C5.Adj (3 : Fin 5) 4 by decide)
  -- injectivity of `σ` rules out the "wrong" (already-used) neighbour at each step
  have d02 : σ 2 ≠ σ 0 := fun h => absurd (hinj h) (by decide)
  have d31 : σ 3 ≠ σ 1 := fun h => absurd (hinj h) (by decide)
  have d42 : σ 4 ≠ σ 2 := fun h => absurd (hinj h) (by decide)
  rcases h01 with h01 | h01
  · -- σ 0 - σ 1 = 1, i.e. σ 1 = σ 0 - 1 : reflection branch.
    -- omega chains each step, using the disjunctions and the distinctness facts.
    have e1 : σ 1 = σ 0 - 1 := by omega
    have e2 : σ 2 = σ 0 - 2 := by omega
    have e3 : σ 3 = σ 0 - 3 := by omega
    have e4 : σ 4 = σ 0 - 4 := by omega
    refine ⟨sr (-(σ 0)), ?_⟩
    rw [dihedralHom_sr]
    apply RelIso.ext
    intro x
    rw [reflIso_apply, neg_neg]
    have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
  · -- σ 1 - σ 0 = 1, i.e. σ 1 = σ 0 + 1 : rotation branch.
    have e1 : σ 1 = σ 0 + 1 := by omega
    have e2 : σ 2 = σ 0 + 2 := by omega
    have e3 : σ 3 = σ 0 + 3 := by omega
    have e4 : σ 4 = σ 0 + 4 := by omega
    refine ⟨r (σ 0), ?_⟩
    rw [dihedralHom_r]
    apply RelIso.ext
    intro x
    rw [rotIso_apply]
    have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega

/-- The dihedral action is bijective: injective (`dihedral_action_faithful`) and
surjective (`dihedralHom_surjective`). -/
theorem dihedralHom_bijective : Function.Bijective dihedralHom :=
  ⟨dihedral_action_faithful, dihedralHom_surjective⟩

/-- **The flagship isomorphism `Aut(C₅) ≅ D₅`.**
The group isomorphism `D₅ ≃* Aut(C₅)`, obtained from the bijective homomorphism
`dihedralHom`. -/
noncomputable def autEquivDihedral : DihedralGroup 5 ≃* (C5 ≃g C5) :=
  MulEquiv.ofBijective dihedralHom dihedralHom_bijective

/-- `Aut(C₅)` is isomorphic to the dihedral group `D₅` (existence form). -/
theorem aut_equiv_dihedral : Nonempty (DihedralGroup 5 ≃* (C5 ≃g C5)) :=
  ⟨autEquivDihedral⟩

/-- **`|Aut(C₅)| = 10`.** The automorphism group of the 5-cycle has exactly ten
elements, matching `|D₅| = 10`. -/
theorem aut_card_eq_ten : Nat.card (C5 ≃g C5) = 10 := by
  have h := Nat.card_eq_of_bijective dihedralHom dihedralHom_bijective
  rw [← h, Nat.card_eq_fintype_card, DihedralGroup.card]

/-- **The reverse bound `|Aut(C₅)| ≤ 10`.** This is the direction left open in
`Brockian.Automorphism`; together with `ten_le_card_aut` it pins `|Aut(C₅)| = 10`. -/
theorem card_aut_le_ten : Nat.card (C5 ≃g C5) ≤ 10 := aut_card_eq_ten.le

end Brockian.Automorphism.Full
