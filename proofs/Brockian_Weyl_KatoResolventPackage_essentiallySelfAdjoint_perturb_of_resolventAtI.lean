/-
  Brockian/WeylKatoResolventPackage.lean

  A small resolvent package for the Kato--Rellich lane.

  `WeylKatoRellichTransfer` proves the Neumann argument from explicit bounded
  right resolvents `R_±` and product estimates `‖B‖ * ‖R_±‖ < 1`.  This file
  packages the common application shape: right resolvents at `±i` with norm at
  most one, so every bounded perturbation with `‖B‖ < 1` is covered.

  This is still not the full unbounded Kato--Rellich theorem.  The remaining
  analytic step is to construct this package from the self-adjoint closure of
  `T`; Mathlib 4.32 does not yet provide that resolvent construction.
-/
import Mathlib
import Brockian.WeylKatoRellichTransfer

namespace Brockian.Weyl.KatoResolventPackage

open scoped InnerProductSpace
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoRellichTransfer
open Brockian.Weyl.KatoUnbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Resolvents at `±i` with the standard self-adjoint norm bound -/

/-- Bounded right resolvents for `T+i` and `T-i`, with the Hilbert-space
self-adjoint resolvent bound normalized at distance one from the real axis.

This is a `Type` rather than a `Prop`: it carries the actual bounded operators
`Radd` and `Rsub` used by the Neumann argument. -/
structure ResolventAtI (T : H →ₗ.[ℂ] H) where
  Radd : H →L[ℂ] H
  Rsub : H →L[ℂ] H
  right_add : RightResolvent T (-Complex.I) Radd
  right_sub : RightResolvent T Complex.I Rsub
  norm_add : ‖Radd‖ ≤ 1
  norm_sub : ‖Rsub‖ ≤ 1

namespace ResolventAtI

/-- The `+i` resolvent product estimate produced by `‖B‖ < 1`. -/
theorem norm_mul_add_lt_one {T : H →ₗ.[ℂ] H} (hres : ResolventAtI T)
    (B : H →L[ℂ] H) (hBsmall : ‖B‖ < 1) :
    ‖B‖ * ‖hres.Radd‖ < 1 := by
  have hmul : ‖B‖ * ‖hres.Radd‖ ≤ ‖B‖ * 1 :=
    mul_le_mul_of_nonneg_left hres.norm_add (norm_nonneg B)
  have hlt : ‖B‖ * 1 < 1 := by simpa using hBsmall
  exact lt_of_le_of_lt hmul hlt

/-- The `-i` resolvent product estimate produced by `‖B‖ < 1`. -/
theorem norm_mul_sub_lt_one {T : H →ₗ.[ℂ] H} (hres : ResolventAtI T)
    (B : H →L[ℂ] H) (hBsmall : ‖B‖ < 1) :
    ‖B‖ * ‖hres.Rsub‖ < 1 := by
  have hmul : ‖B‖ * ‖hres.Rsub‖ ≤ ‖B‖ * 1 :=
    mul_le_mul_of_nonneg_left hres.norm_sub (norm_nonneg B)
  have hlt : ‖B‖ * 1 < 1 := by simpa using hBsmall
  exact lt_of_le_of_lt hmul hlt

/-- A `ResolventAtI` package and a norm-small bounded perturbation give full
surjectivity of the two shifted perturbed ranges. -/
theorem perturbed_ranges_eq_univ {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hres : ResolventAtI T) (hBsmall : ‖B‖ < 1) :
    (Brockian.Weyl.Cayley.rangeAddI (perturb T B) : Set H) = Set.univ ∧
      (Brockian.Weyl.Cayley.rangeSubI (perturb T B) : Set H) = Set.univ :=
  perturbed_ranges_eq_univ_of_resolvent_norm_mul_lt_one
    hres.right_add (hres.norm_mul_add_lt_one B hBsmall)
    hres.right_sub (hres.norm_mul_sub_lt_one B hBsmall)

/-- A `ResolventAtI` package and a norm-small bounded perturbation discharge the
named Kato transfer hypothesis. -/
theorem boundedPerturbationTransfer {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hres : ResolventAtI T) (hBsmall : ‖B‖ < 1) :
    BoundedPerturbationTransfer T B :=
  boundedPerturbationTransfer_of_resolvent_product_norm_lt_one
    hres.right_add (hres.norm_mul_add_lt_one B hBsmall)
    hres.right_sub (hres.norm_mul_sub_lt_one B hBsmall)

end ResolventAtI

/-! ### Kato--Rellich transfer from the package -/

/-- **Packaged Kato transfer.** If `T` has right resolvents at `±i` with norm at
most one, then every bounded perturbation with `‖B‖ < 1` is essentially
self-adjoint.

The theorem deliberately assumes the package.  Constructing `ResolventAtI T`
from `EssentiallySelfAdjoint T` is the remaining unbounded-operator
infrastructure step. -/
theorem essentiallySelfAdjoint_perturb_of_resolventAtI
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hres : ResolventAtI T)
    (hBsmall : ‖B‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one
    hd
    hres.right_add (hres.norm_mul_add_lt_one B hBsmall)
    hres.right_sub (hres.norm_mul_sub_lt_one B hBsmall)

/-- The same packaged transfer, exposing the intermediate full-range conclusion
through the Weyl chain criterion. -/
theorem essentiallySelfAdjoint_perturb_of_resolventAtI_via_chain
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hres : ResolventAtI T)
    (hBsmall : ‖B‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one_via_chain
    hd
    hres.right_add (hres.norm_mul_add_lt_one B hBsmall)
    hres.right_sub (hres.norm_mul_sub_lt_one B hBsmall)

end Brockian.Weyl.KatoResolventPackage
