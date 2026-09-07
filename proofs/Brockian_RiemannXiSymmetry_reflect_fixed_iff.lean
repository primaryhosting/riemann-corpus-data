import Brockian.RiemannXiFunctionalEquation
import Brockian.RiemannScaffold

namespace Brockian.RiemannXiSymmetry

open Complex

/-!
## Symmetry consequences of the Riemann xi functional equation

This module records only theorem-level consequences of the already-verified
functional equation
`RiemannScaffold.riemannXi (1 - s) = RiemannScaffold.riemannXi s`.

No Riemann Hypothesis statement, zero-location assertion, or Hilbert-Polya
existence claim is introduced here.
-/

/-- The Brockian xi functional equation, restated at the symmetry boundary. -/
theorem riemannXi_reflect (s : ℂ) :
    RiemannScaffold.riemannXi (1 - s) = RiemannScaffold.riemannXi s :=
  RiemannXiFunctionalEquation.riemannXi_one_sub s

/-- Reflection `s ↦ 1 - s` is an involution. -/
theorem reflect_reflect (s : ℂ) : 1 - (1 - s) = s := by
  ring

/-- A xi-zero reflects to a xi-zero. -/
theorem riemannXi_eq_zero_reflect {s : ℂ}
    (h : RiemannScaffold.riemannXi s = 0) :
    RiemannScaffold.riemannXi (1 - s) = 0 :=
  RiemannXiFunctionalEquation.riemannXi_one_sub_eq_zero h

/-- The reflected point is a xi-zero if and only if the original point is. -/
theorem riemannXi_reflect_eq_zero_iff (s : ℂ) :
    RiemannScaffold.riemannXi (1 - s) = 0 ↔
      RiemannScaffold.riemannXi s = 0 :=
  RiemannXiFunctionalEquation.riemannXi_one_sub_eq_zero_iff s

/-- The original point is a xi-zero if and only if its reflection is. -/
theorem riemannXi_eq_zero_iff_reflect (s : ℂ) :
    RiemannScaffold.riemannXi s = 0 ↔
      RiemannScaffold.riemannXi (1 - s) = 0 :=
  (riemannXi_reflect_eq_zero_iff s).symm

/-- The xi zero set is invariant under preimage by reflection. -/
theorem riemannXi_zeroSet_preimage_reflect :
    (fun s : ℂ => 1 - s) ⁻¹' {s : ℂ | RiemannScaffold.riemannXi s = 0} =
      {s : ℂ | RiemannScaffold.riemannXi s = 0} := by
  ext s
  exact riemannXi_reflect_eq_zero_iff s

/-- The xi zero set is invariant under image by reflection. -/
theorem riemannXi_zeroSet_image_reflect :
    (fun s : ℂ => 1 - s) '' {s : ℂ | RiemannScaffold.riemannXi s = 0} =
      {s : ℂ | RiemannScaffold.riemannXi s = 0} := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact riemannXi_eq_zero_reflect hs
  · intro hz
    refine ⟨1 - z, ?_, ?_⟩
    · exact riemannXi_eq_zero_reflect hz
    · ring

/-- A xi-zero comes with its reflected zero as a pair. -/
theorem riemannXi_zero_pair_of_zero {s : ℂ}
    (h : RiemannScaffold.riemannXi s = 0) :
    RiemannScaffold.riemannXi s = 0 ∧
      RiemannScaffold.riemannXi (1 - s) = 0 :=
  ⟨h, riemannXi_eq_zero_reflect h⟩

/-- A reflected xi-zero comes with the original zero as a pair. -/
theorem riemannXi_zero_pair_of_reflect_zero {s : ℂ}
    (h : RiemannScaffold.riemannXi (1 - s) = 0) :
    RiemannScaffold.riemannXi (1 - s) = 0 ∧
      RiemannScaffold.riemannXi s = 0 :=
  ⟨h, (riemannXi_reflect_eq_zero_iff s).mp h⟩

/-- The real part of the reflected point is `1 - Re s`. -/
theorem reflect_re (s : ℂ) : (1 - s).re = 1 - s.re := by
  simp

/-- Reflection preserves the critical-line real-part equation. -/
theorem reflect_re_eq_half_iff (s : ℂ) :
    (1 - s).re = 1 / 2 ↔ s.re = 1 / 2 := by
  rw [reflect_re]
  constructor <;> intro h <;> linarith

/-- The critical-line real-part equation is equivalent to fixed real part under reflection. -/
theorem criticalLine_re_iff_reflect_re_eq (s : ℂ) :
    s.re = 1 / 2 ↔ (1 - s).re = s.re := by
  rw [reflect_re]
  constructor <;> intro h <;> linarith

/-- Fixed real part under reflection is equivalent to lying on the critical line. -/
theorem reflect_re_eq_self_iff (s : ℂ) :
    (1 - s).re = s.re ↔ s.re = 1 / 2 :=
  (criticalLine_re_iff_reflect_re_eq s).symm

/-- A xi-zero on the critical line reflects to a xi-zero on the critical line. -/
theorem riemannXi_reflect_zero_and_criticalLine {s : ℂ}
    (hz : RiemannScaffold.riemannXi s = 0) (hre : s.re = 1 / 2) :
    RiemannScaffold.riemannXi (1 - s) = 0 ∧ (1 - s).re = 1 / 2 :=
  ⟨riemannXi_eq_zero_reflect hz, (reflect_re_eq_half_iff s).mpr hre⟩

/-- The fixed points of reflection are exactly the complex point `1 / 2`. -/
theorem reflect_fixed_iff (s : ℂ) : 1 - s = s ↔ s = 1 / 2 := by
  constructor
  · intro h
    have hre_eq : (1 - s).re = s.re := by rw [h]
    have hre : s.re = 1 / 2 := (reflect_re_eq_self_iff s).mp hre_eq
    have him_eq : (1 - s).im = s.im := by rw [h]
    have him : s.im = 0 := by
      simp at him_eq
      linarith
    apply Complex.ext
    · simp [hre]
    · simp [him]
  · intro h
    rw [h]
    norm_num

end Brockian.RiemannXiSymmetry
