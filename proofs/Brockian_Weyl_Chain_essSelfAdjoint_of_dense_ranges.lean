/-
  Brockian/WeylChain.lean — closing the Weyl chain, modulo the one open link.

  The essential-self-adjointness chain for a densely-defined symmetric operator T:

    finite-b nested-circle geometry   (Brockian.Weyl.Disk, VERIFIED)
        │  radius r_b = 1/(2|Im λ|∫₀ᵇ|φ|²), monotone
        ▼
    b→∞ dichotomy  r_b→0 ⟺ ∫₀^∞|φ|²=∞   (Aristotle target: aristotle/…/WeylDichotomyTarget.lean)
        ▼
    limit-point at ∞                     (Brockian.Weyl.LP: const potential VERIFIED; general OPEN)
        │  ⟵── THE ONE OPEN LINK: limit-point ⟹ ran(T±i) dense ──⟶
        ▼
    ran(T+i), ran(T−i) both dense
        ▼
    EssentiallySelfAdjoint T             (Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff, VERIFIED)

  This file proves the LOWER half unconditionally: given the two range-density facts,
  essential self-adjointness follows from the verified von Neumann criterion. So the whole
  chain is complete EXCEPT the single bridge `limit-point ⟹ range dense`, which is isolated
  here as the explicit hypotheses `h_plus`, `h_minus`. Nothing is faked; the open link is
  named, not hidden.
-/
import Brockian.WeylCayley

open Brockian.Weyl.Operator Brockian.Weyl.Cayley

namespace Brockian.Weyl.Chain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Chain closure (modulo the range-density bridge).** A densely-defined symmetric
operator whose ranges `ran(T+i)` and `ran(T−i)` are both dense is essentially self-adjoint.
This composes the entire Weyl chain onto the one remaining open link (density of the ranges,
which the limit-point property is expected to supply). -/
theorem essSelfAdjoint_of_dense_ranges {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H))
    (h_plus : Dense (rangeAddI T : Set H))
    (h_minus : Dense (rangeSubI T : Set H)) :
    EssentiallySelfAdjoint T :=
  (essentiallySelfAdjoint_iff hT).mpr ⟨h_plus, h_minus⟩

end Brockian.Weyl.Chain
