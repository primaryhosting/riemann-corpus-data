import Mathlib

/-! # The depth-holonomy homomorphism is INJECTIVE — hence an isomorphism.

Over the residue cycle `ZMod 6` with fiber `ZMod 6`, the transfer operator `K h` advances the
residue and, at the seam `j = 5 → 0`, increments the fiber depth by the holonomy `h ∈ ZMod 6`.
Winding the cycle once from the base point `(0,0)` reads off exactly the holonomy `h` in the
fiber. Distinct holonomies therefore give distinct loop actions even on the single base point:
the depth-holonomy homomorphism `ZMod 6 → (translations of ZMod 6)` is INJECTIVE. Combined with
surjectivity onto all fiber-translations, this gives `ZMod 6 ≅` the holonomy group — cyclic of
order 6, not merely a homomorphic image. -/

namespace Brockian.HolonomyIsomorphism

/-- The transfer operator: advance the residue by one and, at the seam `j = 5`, add the
    holonomy `h` to the fiber depth. -/
def K (h : ZMod 6) (x : ZMod 6 × ZMod 6) : ZMod 6 × ZMod 6 :=
  (x.1 + 1, x.2 + (if x.1 = 5 then h else 0))

/-- **Loop probe.** Winding the cycle once from the base point `(0,0)` returns to residue `0`
    and reads off exactly the holonomy `h` in the fiber. -/
theorem loop_probe (h : ZMod 6) :
    (K h)^[6] ((0 : ZMod 6), (0 : ZMod 6)) = ((0 : ZMod 6), h) := by revert h; decide

/-- **Injectivity (relational form).** Distinct holonomies give distinct loop actions even on
    the single base point `(0,0)`: the depth-holonomy homomorphism is injective. -/
theorem loop_injective : ∀ (h h' : ZMod 6),
    (K h)^[6] ((0 : ZMod 6), (0 : ZMod 6)) = (K h')^[6] ((0 : ZMod 6), (0 : ZMod 6)) → h = h' := by
  decide

/-- **Injectivity (`Function.Injective`).** The probe map `h ↦ (K h)^[6] (0,0)` is injective. -/
theorem loop_probe_injective :
    Function.Injective (fun h : ZMod 6 => (K h)^[6] ((0 : ZMod 6), (0 : ZMod 6))) := by
  intro a b hab; exact loop_injective a b hab

/-- **Surjective side.** Every fiber-translation `x ↦ (x.1, x.2 + h)` is realized by winding the
    `h`-loop once — the holonomy group is exactly the group of fiber-translations. -/
theorem holonomy_iso_onto_translations :
    ∀ (h : ZMod 6) (x : ZMod 6 × ZMod 6), (K h)^[6] x = (x.1, x.2 + h) := by decide

/-- **Isomorphism bundle.** Injective probe map + surjection onto all fiber-translations: the
    depth-holonomy is an isomorphism `ZMod 6 ≅` holonomy group (cyclic of order 6). -/
theorem holonomy_group_iso :
    (Function.Injective (fun h : ZMod 6 => (K h)^[6] ((0 : ZMod 6), (0 : ZMod 6)))) ∧
    (∀ (h : ZMod 6) (x : ZMod 6 × ZMod 6), (K h)^[6] x = (x.1, x.2 + h)) :=
  ⟨loop_probe_injective, holonomy_iso_onto_translations⟩

end Brockian.HolonomyIsomorphism
