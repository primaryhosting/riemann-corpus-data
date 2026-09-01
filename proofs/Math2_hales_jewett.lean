import Mathlib

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

/-- The point of the combinatorial line described by the template `τ : Fin N → Option (Fin k)`
at the parameter value `a : Fin k`.  A coordinate `i` with `τ i = none` is a *moving* coordinate
(its value is `a`), while a coordinate with `τ i = some b` is *frozen* at the value `b`. -/
def linePoint {N k : ℕ} (τ : Fin N → Option (Fin k)) (a : Fin k) : Fin N → Fin k :=
  fun i => (τ i).getD a

/-- **The Hales–Jewett theorem.**  For every alphabet size `k` and every number of colours `r`
there is a dimension `N` such that every `r`-colouring of the combinatorial cube
`Fin N → Fin k` admits a monochromatic combinatorial line: a template
`τ : Fin N → Option (Fin k)` with at least one moving coordinate, all of whose `k` points
receive the same colour. -/
theorem hales_jewett (k r : ℕ) :
    ∃ N : ℕ, ∀ C : (Fin N → Fin k) → Fin r,
      ∃ τ : Fin N → Option (Fin k), (∃ i, τ i = none) ∧
        ∃ c : Fin r, ∀ a : Fin k, C (linePoint τ a) = c := by
  obtain ⟨ι, _iFin, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  refine ⟨Fintype.card ι, fun C => ?_⟩
  obtain ⟨l, c, hc⟩ := hι (fun v => C (fun i => v (e.symm i)))
  refine ⟨fun i => l.idxFun (e.symm i), ?_, c, fun a => ?_⟩
  · obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simpa using hi⟩
  · simpa [linePoint, Combinatorics.Line.toFun] using hc a

end Math2

