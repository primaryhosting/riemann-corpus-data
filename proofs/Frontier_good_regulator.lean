/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- **Conant–Ashby good regulator theorem** (deterministic base case).

Setting: `S` is the set of states of the regulated system (the disturbances),
`R` is the set of regulatory actions, and `Z` is the set of outcomes.
The system's behaviour is described by `h : S → R → Z`, sending a state `s` and
an action `r` to the resulting outcome `h s r`.

Hypotheses:
* `hgood`: the regulator `ρ : S → R` is *good*, i.e. it regulates perfectly —
  the outcome is the constant (optimal) value `z₀`, whatever the system state.
* `hinj`: the system is *fully entangled* — in each state, distinct regulatory
  actions lead to distinct outcomes.

Conclusion: the regulator *is a model* of the system: its action depends only on
the system's behaviour `h s`, and indeed `ρ` factors as `m ∘ (fun s => h s)` for
some map `m` defined on system behaviours.  In particular a good regulator is a
simulation of (contains a model of) the regulated system. -/
theorem good_regulator {S R Z : Type*} [Nonempty R]
    (h : S → R → Z) (ρ : S → R) (z₀ : Z)
    (hgood : ∀ s, h s (ρ s) = z₀)
    (hinj : ∀ s, Function.Injective (h s)) :
    (∀ s s', h s = h s' → ρ s = ρ s') ∧
      ∃ m : (R → Z) → R, ∀ s, ρ s = m (h s) := by
  have hfac : Function.FactorsThrough ρ h := by
    intro s s' hss'
    apply hinj s
    rw [hgood s, hss', hgood s']
  refine ⟨fun s s' hss' => hfac hss', ?_⟩
  refine ⟨Function.extend h ρ (fun _ => Classical.arbitrary R), fun s => ?_⟩
  rw [hfac.extend_apply]

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

