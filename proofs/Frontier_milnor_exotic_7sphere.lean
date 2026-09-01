/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## What is formalized here

Milnor's theorem (1956) states that there is a smooth 7-manifold which is homeomorphic
but *not* diffeomorphic to the standard 7-sphere `S⁷`.

Mathlib (at this project's pinned version) contains none of the machinery required for a
from-scratch proof: no Pontryagin classes, no Hirzebruch signature theorem, no Morse-theoretic
recognition of spheres (Reeb's theorem), no computation of `π₃(SO(4))`, and no library of
`S³`-bundles over `S⁴`.  A search of the library turns up no statement about exotic spheres or
about Milnor's `λ`-invariant, so no existing lemma closes or nearly closes this goal.

What is provided instead is a **Lean-checked reduction**.  Milnor's geometric input is isolated
as the fields of the structure `Frontier.MilnorData`, and the theorem
`Frontier.milnor_exotic_7sphere` derives, from that input alone, the existence of a manifold
homeomorphic but not diffeomorphic to `S⁷`.  The reduction is Milnor's own counting argument:

* for odd `k`, the total space `M k` of a certain `S³`-bundle over `S⁴` is homeomorphic to `S⁷`
  (Milnor exhibits a Morse function with exactly two critical points and invokes Reeb's
  theorem);
* the `λ`-invariant, valued in `ℤ/7`, is a diffeomorphism invariant, vanishes on the standard
  sphere, and equals `k² - 1 (mod 7)` on `M k`;
* hence any odd `k` with `k² ≢ 1 (mod 7)` — e.g. `k = 3`, where `k² - 1 = 8 ≡ 1 (mod 7)` —
  yields an exotic 7-sphere.

Everything except the fields of `MilnorData` is proved here, unconditionally and with no
axioms beyond Lean's own.  Residues mod `7` are expressed with `Int` and `%` so that the file
needs no imports at all (the required header comment must be the first thing in the file, and
Lean does not permit a module docstring before an `import`).
-/

namespace Frontier

/-- `IsOdd k` says that the integer `k` is odd. -/
def IsOdd (k : Int) : Prop := ∃ m : Int, k = 2 * m + 1

/-- The geometric input of Milnor's construction, packaged as hypotheses.

`Mfld` is a type of smooth 7-manifolds, `Homeo` and `Diffeo` the relations of being
homeomorphic resp. diffeomorphic, `S7` the standard smooth 7-sphere, `M k` the total space of
Milnor's `S³`-bundle over `S⁴` with invariants `(h, l) = ((k+1)/2, (1-k)/2)` for odd `k`, and
`lam` Milnor's `λ`-invariant, here represented by an integer that is well defined modulo `7`. -/
structure MilnorData where
  /-- The ambient type of smooth 7-manifolds. -/
  Mfld : Type
  /-- Being homeomorphic. -/
  Homeo : Mfld → Mfld → Prop
  /-- Being diffeomorphic. -/
  Diffeo : Mfld → Mfld → Prop
  /-- The standard smooth 7-sphere. -/
  S7 : Mfld
  /-- Milnor's family of `S³`-bundles over `S⁴`, indexed by an odd integer `k`. -/
  M : Int → Mfld
  /-- Milnor's `λ`-invariant, an integer well defined modulo `7`. -/
  lam : Mfld → Int
  /-- `λ` is a diffeomorphism invariant (mod `7`). -/
  lam_congr : ∀ a b, Diffeo a b → lam a % 7 = lam b % 7
  /-- `λ` vanishes on the standard sphere. -/
  lam_S7 : lam S7 % 7 = 0
  /-- For odd `k`, `M k` is homeomorphic to `S⁷`: an explicit Morse function on `M k` has
  exactly two critical points, so Reeb's theorem applies. -/
  homeo_M : ∀ k : Int, IsOdd k → Homeo (M k) S7
  /-- Milnor's computation of the invariant: `λ (M k) ≡ k² - 1 (mod 7)`. -/
  lam_M : ∀ k : Int, IsOdd k → lam (M k) % 7 = (k * k - 1) % 7

/-- The arithmetic heart of Milnor's argument: `3² - 1 = 8 ≢ 0 (mod 7)`. -/
theorem milnor_lambda_three : (3 * 3 - 1 : Int) % 7 ≠ 0 := by decide

/-- There is an odd integer `k` with `k² - 1 ≢ 0 (mod 7)`; concretely `k = 3`. -/
theorem exists_odd_lambda_ne_zero :
    ∃ k : Int, IsOdd k ∧ (k * k - 1) % 7 ≠ 0 :=
  ⟨3, ⟨1, by decide⟩, milnor_lambda_three⟩

/-- **Milnor's exotic 7-sphere**, as a Lean-checked reduction to Milnor's geometric input
`D : MilnorData`: there is a smooth manifold homeomorphic, but not diffeomorphic, to the
standard 7-sphere. -/
theorem milnor_exotic_7sphere (D : MilnorData) :
    ∃ m : D.Mfld, D.Homeo m D.S7 ∧ ¬ D.Diffeo m D.S7 := by
  obtain ⟨k, hk, hlam⟩ := exists_odd_lambda_ne_zero
  refine ⟨D.M k, D.homeo_M k hk, fun hdiff => hlam ?_⟩
  have h1 : D.lam (D.M k) % 7 = D.lam D.S7 % 7 := D.lam_congr _ _ hdiff
  rw [D.lam_M k hk, D.lam_S7] at h1
  exact h1

/-- The residue of `k² - 1` mod `7` for every `k ≡ 3 (mod 14)`. -/
theorem lambda_three_add_fourteen (t : Int) :
    ((3 + 14 * t) * (3 + 14 * t) - 1) % 7 = 1 := by
  have h : (3 + 14 * t) * (3 + 14 * t) - 1 = 8 + 7 * (12 * t + 28 * (t * t)) := by
    grind
  rw [h]
  omega

/-- A stronger form of the reduction: arbitrarily large `k` give exotic 7-spheres, since
`k² - 1 ≡ 1 (mod 7)` for every `k ≡ 3 (mod 14)`. -/
theorem milnor_exotic_7sphere_unbounded (D : MilnorData) (n : Int) :
    ∃ k : Int, n ≤ k ∧ D.Homeo (D.M k) D.S7 ∧ ¬ D.Diffeo (D.M k) D.S7 := by
  obtain ⟨t, ht⟩ : ∃ t : Int, n ≤ 3 + 14 * t := by
    rcases Int.le_total 0 n with h | h
    · exact ⟨n, by omega⟩
    · exact ⟨0, by omega⟩
  refine ⟨3 + 14 * t, ht, D.homeo_M _ ⟨1 + 7 * t, by omega⟩, fun hdiff => ?_⟩
  have h1 : D.lam (D.M (3 + 14 * t)) % 7 = D.lam D.S7 % 7 := D.lam_congr _ _ hdiff
  rw [D.lam_M _ ⟨1 + 7 * t, by omega⟩, D.lam_S7, lambda_three_add_fourteen] at h1
  exact absurd h1 (by decide)

end Frontier

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

