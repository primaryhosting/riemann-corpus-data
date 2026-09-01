/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the text is otherwise verbatim.)

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

namespace Brockian

open DihedralGroup

/-!
## The dihedral action on the vertices of the `n`-gon

We label the vertices of the regular `n`-gon by `ZMod n`.  With Mathlib's multiplication
convention on `DihedralGroup n` (`r i * sr j = sr (j - i)`), the natural *left* action of the
symmetry group on the vertex set is given by

* `r i • x = x - i`   (rotation),
* `sr i • x = i - x`  (reflection).
-/

/-- The action of a symmetry of the regular `n`-gon on its vertex set `ZMod n`. -/
def ngonAct {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | r i, x => x - i
  | sr i, x => i - x

/-- The symmetry group of the `n`-gon acts on the vertex set `ZMod n`. -/
instance ngonMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := ngonAct
  one_smul x := by
    show ngonAct (r (0 : ZMod n)) x = x
    simp [ngonAct]
  mul_smul g h x := by
    show ngonAct (g * h) x = ngonAct g (ngonAct h x)
    cases g with
    | r i => cases h with
      | r j => simp [ngonAct]; ring
      | sr j => simp [ngonAct]; ring
    | sr i => cases h with
      | r j => simp [ngonAct]; ring
      | sr j => simp [ngonAct]; ring

@[simp] lemma r_smul {n : ℕ} (i x : ZMod n) : (r i : DihedralGroup n) • x = x - i := rfl

@[simp] lemma sr_smul {n : ℕ} (i x : ZMod n) : (sr i : DihedralGroup n) • x = i - x := rfl

/-- **Pentagon equivariance, general `n`-gon version.**

A self-map `f` of the vertex set `ZMod n` of the regular `n`-gon commutes with the whole
symmetry group `DihedralGroup n` if and only if it is the translation by a `2`-torsion
element `c` of `ZMod n`.

For `n = 5` (the pentagon) — indeed for any odd `n` — the only such `c` is `0`, so the only
equivariant self-map is the identity; for even `n` there is exactly one further equivariant map,
the antipodal map `x ↦ x + n / 2`. -/
theorem PentagonPentagonEquivarianceGeneral {n : ℕ} (f : ZMod n → ZMod n) :
    (∀ (g : DihedralGroup n) (x : ZMod n), f (g • x) = g • f x) ↔
      ∃ c : ZMod n, c + c = 0 ∧ ∀ x, f x = x + c := by
  constructor
  · intro h
    refine ⟨f 0, ?_, ?_⟩
    · -- reflection through the vertex `0` forces `f 0` to be `2`-torsion
      have h0 := h (sr 0) 0
      simp only [sr_smul, zero_sub, neg_zero] at h0
      -- `f 0 = -f 0`
      have : f 0 = -f 0 := h0
      linear_combination (norm := ring_nf) this
    · intro x
      -- rotations force `f` to be a translation
      have hx := h (r (-x)) 0
      simp only [r_smul, zero_sub, neg_neg] at hx
      rw [hx]
      ring
  · rintro ⟨c, hc, hf⟩ g x
    cases g with
    | r i => simp only [r_smul, hf]; ring
    | sr i =>
        simp only [sr_smul, hf]
        linear_combination (norm := ring_nf) hc

/-- Specialisation to odd `n`: the identity is the only equivariant self-map of the vertex
set of the regular `n`-gon. -/
theorem ngon_equivariance_odd {n : ℕ} (hn : Odd n) (f : ZMod n → ZMod n)
    (h : ∀ (g : DihedralGroup n) (x : ZMod n), f (g • x) = g • f x) :
    ∀ x, f x = x := by
  obtain ⟨c, hc, hf⟩ := (PentagonPentagonEquivarianceGeneral f).1 h
  have hc0 : c = 0 := by
    have h2 : (2 : ZMod n) * c = 0 := by linear_combination (norm := ring_nf) hc
    have : IsUnit (2 : ZMod n) := by
      have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
      simpa using (ZMod.isUnit_iff_coprime 2 n).2 (by simpa [Nat.Coprime] using hcop)
    obtain ⟨u, hu⟩ := this
    have := congrArg (fun z => (↑u⁻¹ : ZMod n) * z) h2
    simpa [← hu, ← mul_assoc, ← Units.val_mul] using this
  intro x
  simp [hf, hc0]

/-- The pentagon case (`n = 5`), recovering the original `D₅` statement. -/
theorem PentagonEquivariance (f : ZMod 5 → ZMod 5)
    (h : ∀ (g : DihedralGroup 5) (x : ZMod 5), f (g • x) = g • f x) :
    ∀ x, f x = x :=
  ngon_equivariance_odd (by decide) f h

end Brockian

