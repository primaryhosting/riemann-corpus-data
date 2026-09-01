import Mathlib

/-!
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Knaster–Tarski**: a monotone map `f` on a complete lattice has a least fixed point,
i.e. there is `a` with `f a = a` which is below every fixed point of `f`.

The witness is Mathlib's `OrderHom.lfp`; the two facts used are
`OrderHom.map_lfp` (it is a fixed point) and `OrderHom.lfp_le` (it is least
among prefixed points, hence among fixed points). -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a, f a = a ∧ ∀ b, f b = b → a ≤ b :=
  ⟨OrderHom.lfp ⟨f, hf⟩, OrderHom.map_lfp ⟨f, hf⟩, fun _ hb => OrderHom.lfp_le _ hb.le⟩

end CS

