/-
  Brockian/Automorphism.lean — the symmetry face of the Brockian Pentagonal Law.

  Citation-grade Mathlib-4.32 port of the automorphism / dihedral symmetry theory
  of the 5-cycle `C₅ = SimpleGraph.cycleGraph 5`, the graph whose golden spectrum
  and pentagon geometry are treated in `Brockian.Geometry`.

  ── What is PROVED here (rung 2 of the target ladder, plus rung 3 base) ──
    * `rotIso`, `reflIso`   — explicit graph automorphisms of `C₅`:
                              rotation `x ↦ x + a` and reflection `x ↦ -b - x`,
                              each PROVED to preserve adjacency (`rot_map_adj`,
                              `refl_map_adj`).                              [rung 3]
    * `dihedralHom`         — a group homomorphism `D₅ →* Aut(C₅)` realizing the
                              full dihedral group as graph automorphisms.
    * `dihedral_action_faithful` — that homomorphism is INJECTIVE: `D₅` embeds
                              faithfully into `Aut(C₅)`.                    [rung 2]
    * `ten_le_card_aut`     — consequently `10 ≤ |Aut(C₅)|` (quantitative lower
                              bound, using `|D₅| = 10`).

  ── What is NOT proved here (honest blocker for the full `Aut(C₅) ≅ D₅`) ──
    The flagship isomorphism `Aut(C₅) ≃* D₅` (equivalently `Nat.card (Aut C₅) = 10`)
    additionally needs the REVERSE bound `|Aut(C₅)| ≤ 10`, i.e. that every graph
    automorphism of `C₅` is one of these ten. Mathlib-4.32 supplies no
    `SimpleGraph.Aut` enumeration nor a `Fintype (C₅ ≃g C₅)` instance, so this
    upper bound would require an explicit connectivity argument (an automorphism of
    a cycle is determined by the images of two adjacent vertices) that has no clean
    4.32 witness. It is DROPPED, not faked — the theorem names above claim exactly
    what is proved and no more.

  Note: `d5_card : Fintype.card (DihedralGroup 5) = 10` already lives in
  `Brockian.Geometry`; here we reuse `DihedralGroup.card` directly for the
  `Nat.card` form rather than duplicating it.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Brockian.Automorphism

open SimpleGraph
open DihedralGroup

/-- The 5-cycle graph `C₅`, on vertex set `Fin 5`. -/
abbrev C5 : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

/-! ### Two explicit families of automorphisms of `C₅` -/

/-- Rotation `x ↦ x + a` as a permutation of the vertices. -/
def rotEquiv (a : Fin 5) : Fin 5 ≃ Fin 5 := Equiv.addRight a

/-- Reflection `x ↦ -b - x` as a permutation of the vertices (an involution). -/
def reflEquiv (b : Fin 5) : Fin 5 ≃ Fin 5 where
  toFun x := -b - x
  invFun x := -b - x
  left_inv x := by simp
  right_inv x := by simp

@[simp] lemma rotEquiv_apply (a x : Fin 5) : rotEquiv a x = x + a := rfl
@[simp] lemma reflEquiv_apply (b x : Fin 5) : reflEquiv b x = -b - x := rfl

/-- **Rotation preserves adjacency.** `x ↦ x + a` keeps the cyclic distance,
since `(u + a) - (v + a) = u - v` in `Fin 5`. -/
lemma rot_map_adj (a u v : Fin 5) :
    C5.Adj (rotEquiv a u) (rotEquiv a v) ↔ C5.Adj u v := by
  simp only [rotEquiv_apply, C5, SimpleGraph.cycleGraph_adj]
  have e1 : (u + a) - (v + a) = u - v := by abel
  have e2 : (v + a) - (u + a) = v - u := by abel
  rw [e1, e2]

/-- **Reflection preserves adjacency.** `x ↦ -b - x` reverses the cyclic
orientation, swapping the two adjacency disjuncts, so adjacency is preserved. -/
lemma refl_map_adj (b u v : Fin 5) :
    C5.Adj (reflEquiv b u) (reflEquiv b v) ↔ C5.Adj u v := by
  simp only [reflEquiv_apply, C5, SimpleGraph.cycleGraph_adj]
  have e1 : (-b - u) - (-b - v) = v - u := by abel
  have e2 : (-b - v) - (-b - u) = u - v := by abel
  rw [e1, e2]
  tauto

/-- Rotation as a graph automorphism of `C₅`. -/
def rotIso (a : Fin 5) : C5 ≃g C5 := ⟨rotEquiv a, rot_map_adj a _ _⟩

/-- Reflection as a graph automorphism of `C₅`. -/
def reflIso (b : Fin 5) : C5 ≃g C5 := ⟨reflEquiv b, refl_map_adj b _ _⟩

/-! ### The dihedral group as a subgroup of `Aut(C₅)` -/

/-- The underlying map of the dihedral action. -/
def act : DihedralGroup 5 → (C5 ≃g C5)
  | r a => rotIso a
  | sr b => reflIso b

@[simp] lemma act_r (a : ZMod 5) : act (r a) = rotIso a := rfl
@[simp] lemma act_sr (b : ZMod 5) : act (sr b) = reflIso b := rfl

lemma mul_rr (a b : ZMod 5) : (r a * r b : DihedralGroup 5) = r (a + b) := rfl
lemma mul_rsr (a b : ZMod 5) : (r a * sr b : DihedralGroup 5) = sr (b - a) := rfl
lemma mul_srr (a b : ZMod 5) : (sr a * r b : DihedralGroup 5) = sr (a + b) := rfl
lemma mul_srsr (a b : ZMod 5) : (sr a * sr b : DihedralGroup 5) = r (b - a) := rfl

/-- **The dihedral action on `C₅` by graph automorphisms.**
`D₅ = DihedralGroup 5` acts on the 5-cycle: `r a` rotates (`x ↦ x + a`) and
`sr b` reflects (`x ↦ -b - x`). Both preserve adjacency, and the assignment is a
group homomorphism into the automorphism group `C₅ ≃g C₅`. -/
def dihedralHom : DihedralGroup 5 →* (C5 ≃g C5) where
  toFun := act
  map_one' := by
    apply RelIso.ext; intro x
    show rotEquiv 0 x = x
    simp
  map_mul' := by
    rintro (a | a) (b | b)
    · rw [mul_rr, act_r, act_r, act_r]; apply RelIso.ext; intro x
      show rotEquiv (a + b) x = rotEquiv a (rotEquiv b x)
      simp only [rotEquiv_apply]; abel
    · rw [mul_rsr, act_sr, act_r, act_sr]; apply RelIso.ext; intro x
      show reflEquiv (b - a) x = rotEquiv a (reflEquiv b x)
      simp only [rotEquiv_apply, reflEquiv_apply]; abel
    · rw [mul_srr, act_sr, act_sr, act_r]; apply RelIso.ext; intro x
      show reflEquiv (a + b) x = reflEquiv a (rotEquiv b x)
      simp only [rotEquiv_apply, reflEquiv_apply]; abel
    · rw [mul_srsr, act_r, act_sr, act_sr]; apply RelIso.ext; intro x
      show rotEquiv (b - a) x = reflEquiv a (reflEquiv b x)
      simp only [rotEquiv_apply, reflEquiv_apply]; abel

@[simp] lemma dihedralHom_r (a : ZMod 5) : dihedralHom (r a) = rotIso a := rfl
@[simp] lemma dihedralHom_sr (b : ZMod 5) : dihedralHom (sr b) = reflIso b := rfl

@[simp] lemma rotIso_apply (a x : Fin 5) : rotIso a x = x + a := rfl
@[simp] lemma reflIso_apply (b x : Fin 5) : reflIso b x = -b - x := rfl

/-- A rotation and a reflection of `C₅` cannot agree at both vertex `0` and vertex
`1`: the induced vertex-differences are `+1` and `-1`, and `1 ≠ -1` in `Fin 5`. -/
private lemma rot_ne_refl (a b : Fin 5)
    (h0 : (0 : Fin 5) + a = -b - 0) (h1 : (1 : Fin 5) + a = -b - 1) : False := by
  simp only [zero_add, sub_zero] at h0
  rw [h0] at h1
  have e : (1 : Fin 5) + (-b) = (-1) + (-b) := by rw [h1]; abel
  exact absurd (add_right_cancel e) (by decide)

/-- **Faithfulness of the dihedral action (rung 2).**
The homomorphism `dihedralHom : D₅ →* Aut(C₅)` is injective: distinct dihedral
symmetries act as distinct graph automorphisms of the 5-cycle. Hence `D₅` embeds
as a subgroup of `Aut(C₅)`. -/
theorem dihedral_action_faithful : Function.Injective dihedralHom := by
  intro g₁ g₂ h
  obtain (a | a) := g₁ <;> obtain (b | b) := g₂ <;>
    simp only [dihedralHom_r, dihedralHom_sr] at h
  · -- r a = r b
    have h0 := DFunLike.congr_fun h 0
    simp only [rotIso_apply, zero_add] at h0
    exact congrArg r h0
  · -- r a = sr b : rotation ≠ reflection
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [rotIso_apply, reflIso_apply] at h0 h1
    exact absurd (rot_ne_refl _ _ h0 h1) (fun x => x)
  · -- sr a = r b : reflection ≠ rotation
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [rotIso_apply, reflIso_apply] at h0 h1
    exact absurd (rot_ne_refl _ _ h0.symm h1.symm) (fun x => x)
  · -- sr a = sr b
    have h0 := DFunLike.congr_fun h 0
    simp only [reflIso_apply, sub_zero, neg_inj] at h0
    exact congrArg sr h0

/-- `Aut(C₅) = C₅ ≃g C₅` is finite: it embeds into `Equiv.Perm (Fin 5)` via the
underlying permutation. -/
instance : Finite (C5 ≃g C5) := by
  apply Finite.of_injective (fun f => (f.toEquiv : Equiv.Perm (Fin 5)))
  intro f g hfg
  apply RelIso.ext
  intro x
  exact DFunLike.congr_fun hfg x

/-- **Lower bound on `|Aut(C₅)|` (rung 2, quantitative).**
Since `D₅` embeds into `Aut(C₅)` by graph automorphisms (`dihedral_action_faithful`)
and `|D₅| = 10`, the automorphism group of the 5-cycle has at least `10` elements.
The reverse bound `|Aut(C₅)| ≤ 10`, which would upgrade this to the full
`Aut(C₅) ≅ D₅`, is NOT proved here (see the module note). -/
theorem ten_le_card_aut : 10 ≤ Nat.card (C5 ≃g C5) := by
  have hcard : Nat.card (DihedralGroup 5) = 10 := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  calc 10 = Nat.card (DihedralGroup 5) := hcard.symm
    _ ≤ Nat.card (C5 ≃g C5) :=
        Nat.card_le_card_of_injective dihedralHom dihedral_action_faithful

end Brockian.Automorphism
