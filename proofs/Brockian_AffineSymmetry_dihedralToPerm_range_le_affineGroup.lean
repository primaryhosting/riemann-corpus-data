/-
  Brockian/AffineSymmetry.lean — the TRUE symmetry group of the ray / transition
  structure, cleanly SEPARATED into its three distinct groups.

  ── The error this module retires (paper audit target #3) ──
    Papers 2 & 4 claim "the automorphism group of the additive ray partition of
    `ZMod p` is `D_p`."  That conflates THREE genuinely different groups:

      1. the *additive* automorphism group of `(ZMod p, +)`, which is
         `(ZMod p)ˣ ≅ C_{p-1}` (multiplication by a unit) — NOT `D_p`;
      2. the *graph* automorphism group of the cycle graph `C_p`, which is
         `D_p ≅ Aut(C_p)` (proved in `Brockian.Automorphism.Full.autEquivDihedral`);
      3. the ±1-affine map family `{i ↦ ±i + c}`, a *dihedral subgroup of order 2p
         inside the affine group* `Aff(1, F_p)` — this is the map the papers actually
         describe, mislabeled as "the automorphism group of the additive partition".

    For `p = 5` the orders are `4`, `10`, `10`: the additive automorphism group has
    order `4`, so it CANNOT be `D₅` (order `10`).  That single inequality retires the
    conflation; the affine dihedral (order `10`) is the object the papers meant.

  ── What is PROVED here ──
    • `additiveAutEquivUnits`  — the CORRECT identification
        `AddAut (ZMod p) ≃+ Additive (ZMod p)ˣ`  (Mathlib `ZMod.AddAutEquivUnits`).
    • `additiveAut_card`       — `Nat.card (AddAut (ZMod p)) = p - 1`  (general prime).
    • `additiveAut_card_five`  — order `4` for `p = 5`.
    • `units_isCyclic`         — `(ZMod p)ˣ` is cyclic, i.e. `C_{p-1}`.
    • `affinePerm` / `affineGroup` — the affine group `Aff(1, F_p) ≤ Equiv.Perm (ZMod p)`.
    • `dihedralToPerm`         — `DihedralGroup p →* Equiv.Perm (ZMod p)`, `r a ↦ (i ↦ i+a)`,
                                 `sr b ↦ (i ↦ -i-b)`; the ±1-affine dihedral realization.
    • `dihedralToPerm_injective`, `dihedralToPerm_card` — it is faithful of order `2p`.
    • `dihedralToPerm_range_le_affineGroup` — its image sits inside `Aff(1, F_p)`.
    • `symmetry_separation`    — the three orders `4 / 10 / 10` with `4 ≠ 10`, cleanly
                                 separating additive-aut `C₄` from graph-aut `D₅`.

  Verification:  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.  No `sorry`, no `axiom`,
  no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import Brockian.AutomorphismFull

namespace Brockian.AffineSymmetry

open DihedralGroup
open Brockian.Automorphism
open Brockian.Automorphism.Full

/-! ## 1. Additive automorphisms of `ZMod p` are the units `(ZMod p)ˣ ≅ C_{p-1}`

An additive automorphism of `(ZMod p, +)` is *multiplication by a unit*, so the group
of additive automorphisms is `(ZMod p)ˣ`, a cyclic group of order `p - 1` — **not** the
dihedral group `D_p`. -/

variable (p : ℕ)

/-- **The CORRECT identification.**  The additive automorphism group of `ZMod p` is the
group of units `(ZMod p)ˣ` (written additively as `Additive (ZMod p)ˣ`), realized by
multiplication by a unit.  This is Mathlib's `ZMod.AddAutEquivUnits`. -/
def additiveAutEquivUnits : AddAut (ZMod p) ≃+ Additive (ZMod p)ˣ :=
  ZMod.AddAutEquivUnits p

/-- **Order of the additive automorphism group is `p - 1`.**  Hence for a prime `p` it is
the cyclic group `C_{p-1}` — categorically distinct from `D_p` (order `2p`). -/
theorem additiveAut_card [Fact p.Prime] :
    Nat.card (AddAut (ZMod p)) = p - 1 := by
  rw [Nat.card_congr (ZMod.AddAutEquivUnits p).toEquiv,
      Nat.card_congr (Additive.toMul : Additive (ZMod p)ˣ ≃ (ZMod p)ˣ),
      Nat.card_eq_fintype_card, ZMod.card_units]

/-- **`(ZMod p)ˣ` is cyclic** (finite units of a field/integral domain), so the additive
automorphism group `AddAut (ZMod p) ≅ (ZMod p)ˣ` is the cyclic group `C_{p-1}`. -/
theorem units_isCyclic [Fact p.Prime] : IsCyclic (ZMod p)ˣ := inferInstance

/-- **`p = 5`: the additive automorphism group has order `4`.**  It is `C₄`, so it is NOT
`D₅` (order `10`) — the paper's claim is false already at the order. -/
theorem additiveAut_card_five : Nat.card (AddAut (ZMod 5)) = 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := additiveAut_card 5
  omega

/-! ## 2. The ±1-affine dihedral group inside `Aff(1, F_p)`

The map the papers actually describe, `i ↦ ±i + c`, is the *dihedral subgroup of order
`2p` inside the affine group* `Aff(1, F_p) = {i ↦ a·i + b : a ∈ (ZMod p)ˣ, b ∈ ZMod p}`.
We model `Aff(1, F_p)` as a subgroup of `Equiv.Perm (ZMod p)` and exhibit the dihedral
realization, faithful and of order `2p`, landing inside it. -/

section Affine

variable [Fact p.Prime]

/-- The affine permutation `i ↦ a·i + b` of `F_p = ZMod p`, for a unit slope `a`. -/
def affinePerm (a : (ZMod p)ˣ) (b : ZMod p) : Equiv.Perm (ZMod p) :=
  (Equiv.mulLeft₀ (a : ZMod p) a.ne_zero).trans (Equiv.addRight b)

@[simp] theorem affinePerm_apply (a : (ZMod p)ˣ) (b x : ZMod p) :
    affinePerm p a b x = (a : ZMod p) * x + b := by
  simp [affinePerm]

/-- **The affine group `Aff(1, F_p)`** as a subgroup of `Equiv.Perm (ZMod p)`: all maps
`i ↦ a·i + b` with unit slope `a`.  Closed under composition and inverse. -/
def affineGroup : Subgroup (Equiv.Perm (ZMod p)) where
  carrier := {σ | ∃ (a : (ZMod p)ˣ) (b : ZMod p), σ = affinePerm p a b}
  one_mem' := ⟨1, 0, by ext x; simp⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    refine ⟨a * a', (a : ZMod p) * b' + b, ?_⟩
    ext x
    simp only [Equiv.Perm.mul_apply, affinePerm_apply, Units.val_mul]
    ring
  inv_mem' := by
    rintro σ ⟨a, b, rfl⟩
    refine ⟨a⁻¹, -((a⁻¹ : (ZMod p)ˣ) * b), ?_⟩
    have ha : (a : ZMod p) * (a⁻¹ : (ZMod p)ˣ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hmul :
        affinePerm p a b * affinePerm p a⁻¹ (-((a⁻¹ : (ZMod p)ˣ) * b)) = 1 := by
      ext x
      simp only [Equiv.Perm.mul_apply, affinePerm_apply, Equiv.Perm.one_apply]
      linear_combination (x - b) * ha
    exact inv_eq_of_mul_eq_one_right hmul

/-- The underlying map of the dihedral realization: rotations `r a ↦ (i ↦ i + a)` (slope
`+1`) and reflections `sr b ↦ (i ↦ -i - b)` (slope `-1`). -/
def dihAct : DihedralGroup p → Equiv.Perm (ZMod p)
  | .r a => affinePerm p 1 a
  | .sr b => affinePerm p (-1) (-b)

@[simp] theorem dihAct_r (a : ZMod p) : dihAct p (r a) = affinePerm p 1 a := rfl
@[simp] theorem dihAct_sr (b : ZMod p) : dihAct p (sr b) = affinePerm p (-1) (-b) := rfl

/-- **The ±1-affine dihedral realization** `DihedralGroup p →* Equiv.Perm (ZMod p)`.
This is the map Papers 2 & 4 describe as "the automorphism group of the additive ray
partition": `i ↦ ±i + c`.  It is a genuine dihedral group of order `2p` sitting inside
the affine group — NOT the additive automorphism group `(ZMod p)ˣ`. -/
def dihedralToPerm : DihedralGroup p →* Equiv.Perm (ZMod p) where
  toFun := dihAct p
  map_one' := by
    show affinePerm p 1 0 = 1
    ext x; simp
  map_mul' g₁ g₂ := by
    obtain (a | a) := g₁ <;> obtain (b | b) := g₂
    · show affinePerm p 1 (a + b) = affinePerm p 1 a * affinePerm p 1 b
      ext x
      simp only [Equiv.Perm.mul_apply, affinePerm_apply, Units.val_one]; ring
    · show affinePerm p (-1) (-(b - a)) = affinePerm p 1 a * affinePerm p (-1) (-b)
      ext x
      simp only [Equiv.Perm.mul_apply, affinePerm_apply, Units.val_one, Units.val_neg]; ring
    · show affinePerm p (-1) (-(a + b)) = affinePerm p (-1) (-a) * affinePerm p 1 b
      ext x
      simp only [Equiv.Perm.mul_apply, affinePerm_apply, Units.val_one, Units.val_neg]; ring
    · show affinePerm p 1 (b - a) = affinePerm p (-1) (-a) * affinePerm p (-1) (-b)
      ext x
      simp only [Equiv.Perm.mul_apply, affinePerm_apply, Units.val_one, Units.val_neg]; ring

@[simp] theorem dihedralToPerm_r (a : ZMod p) :
    dihedralToPerm p (r a) = affinePerm p 1 a := rfl
@[simp] theorem dihedralToPerm_sr (b : ZMod p) :
    dihedralToPerm p (sr b) = affinePerm p (-1) (-b) := rfl

/-- **The dihedral realization is faithful** when `p ≠ 2` (equivalently `(2 : ZMod p) ≠ 0`):
distinct dihedral symmetries act as distinct affine permutations of `F_p`. -/
theorem dihedralToPerm_injective (hp : (2 : ZMod p) ≠ 0) :
    Function.Injective (dihedralToPerm p) := by
  intro g₁ g₂ h
  obtain (a | a) := g₁ <;> obtain (b | b) := g₂
  · -- r a = r b
    have h0 := DFunLike.congr_fun h 0
    simp only [dihedralToPerm_r, affinePerm_apply, Units.val_one, mul_zero, zero_add] at h0
    exact congrArg r h0
  · -- r a = sr b : rotation ≠ reflection
    exfalso; apply hp
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [dihedralToPerm_r, dihedralToPerm_sr, affinePerm_apply,
      Units.val_one, Units.val_neg] at h0 h1
    linear_combination h1 - h0
  · -- sr a = r b : reflection ≠ rotation
    exfalso; apply hp
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [dihedralToPerm_r, dihedralToPerm_sr, affinePerm_apply,
      Units.val_one, Units.val_neg] at h0 h1
    linear_combination h0 - h1
  · -- sr a = sr b
    have h0 := DFunLike.congr_fun h 0
    simp only [dihedralToPerm_sr, affinePerm_apply, Units.val_neg, Units.val_one,
      mul_zero, zero_add, neg_inj] at h0
    exact congrArg sr h0

/-- **Order `2p`.**  The ±1-affine dihedral group has exactly `2p` elements, matching
`|D_p| = 2p` — the standard dihedral order, distinct from `|(ZMod p)ˣ| = p - 1`. -/
theorem dihedralToPerm_card (hp : (2 : ZMod p) ≠ 0) :
    Nat.card (dihedralToPerm p).range = 2 * p := by
  have e := MonoidHom.ofInjective (dihedralToPerm_injective p hp)
  rw [Nat.card_congr e.symm.toEquiv, DihedralGroup.nat_card]

/-- **The dihedral realization lands inside the affine group.**  Every `i ↦ ±i + c` is an
affine map `i ↦ a·i + b` with `a = ±1` a unit, so the dihedral image is a *subgroup of
`Aff(1, F_p)`* — exactly the correct home for the maps the papers describe. -/
theorem dihedralToPerm_range_le_affineGroup :
    (dihedralToPerm p).range ≤ affineGroup p := by
  rintro σ ⟨g, rfl⟩
  obtain (a | b) := g
  · exact ⟨1, a, rfl⟩
  · exact ⟨-1, -b, rfl⟩

end Affine

/-! ## 3. The clean separation: additive-aut `C₄` ≠ graph-aut `D₅`

The decisive fact.  At `p = 5`:

  • additive automorphism group `AddAut (ZMod 5) ≅ (ZMod 5)ˣ` has order **4** (`C₄`);
  • graph automorphism group `C₅ ≃g C₅ ≅ D₅` has order **10** (proved in
    `Brockian.Automorphism.Full.autEquivDihedral`);
  • the ±1-affine dihedral group has order **10** (`Aff`-subgroup, `dihedralToPerm`).

Since `4 ≠ 10`, the additive automorphism group is NOT `D₅`.  The papers conflated the
order-`10` affine dihedral (which is the object they informally describe) with the
additive automorphism group.  This theorem records all three orders and the inequality. -/

instance instFactPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem symmetry_separation :
    Nat.card (AddAut (ZMod 5)) = 4 ∧
    Nat.card (C5 ≃g C5) = 10 ∧
    Nat.card (dihedralToPerm 5).range = 10 ∧
    Nat.card (AddAut (ZMod 5)) ≠ Nat.card (C5 ≃g C5) := by
  refine ⟨additiveAut_card_five, aut_card_eq_ten, ?_, ?_⟩
  · have h2 : (2 : ZMod 5) ≠ 0 := by decide
    have h := dihedralToPerm_card 5 h2
    omega
  · rw [additiveAut_card_five, aut_card_eq_ten]; decide

end Brockian.AffineSymmetry
