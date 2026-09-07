/-
  Brockian/WeylKatoUnbounded.lean — the **unbounded bounded-perturbation
  (Kato–Rellich) rung**: a bounded self-adjoint operator perturbs a densely-defined
  symmetric operator without destroying the essential-self-adjointness machinery.

  ## Setting

  `T : H →ₗ.[ℂ] H` is a densely-defined symmetric UNBOUNDED operator on a complex
  Hilbert space `H` (physics convention: `⟪·,·⟫` conjugate-linear in the FIRST
  slot). `B : H →L[ℂ] H` is a BOUNDED self-adjoint operator. The perturbed operator

      `perturb T B := B +ᵥ T`   (same domain `dom T`, action `v ↦ T v + B v`)

  is Mathlib's `LinearPMap` `+ᵥ`-action of the linear map `↑B` on `T`
  (`LinearPMap.vadd_apply`, `vadd_domain`). We build the Kato–Rellich rung on top of
  `Brockian.Weyl.Operator`, `Brockian.Weyl.Cayley`, `Brockian.Weyl.ESA`,
  `Brockian.Weyl.FreeLaplacian` (symmetry half `isSymmetric_vadd_clm`), and
  `Brockian.Weyl.Kato` (bounded range-density `dense_range_add_sub_of_selfAdjoint`).

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `perturb` / `perturb_apply` / `perturb_domain` / `perturb_dense_domain`
                                      — the perturbed operator and its API: same
                                        (dense) domain as `T`, acting `v ↦ T v + B v`.

    * `perturb_isSymmetric`           — **symmetry is preserved**: `T` symmetric and
                                        `B` self-adjoint ⇒ `perturb T B` symmetric.
                                        (Reuses `FreeLaplacian.isSymmetric_vadd_clm`.)

    * `perturb_norm_sub_smul_ge`      — the basic inequality `‖(T+B)v − z·v‖ ≥
                                        |Im z|·‖v‖` transfers to the perturbed
                                        operator (corollary of the symmetric-operator
                                        inequality).

    * `perturb_apply_ne_I_smul` / `perturb_apply_ne_neg_I_smul`
                                      — `T + B ± i` is injective on the domain: `±i`
                                        is never an eigenvalue of the (symmetric)
                                        perturbed operator.

    * `perturb_norm_add_I_smul_eq`    — the Cayley isometry norm form
                                        `‖(T+B)v + i·v‖ = ‖(T+B)v − i·v‖` for the
                                        perturbed operator.

    * `essentiallySelfAdjoint_perturb_iff`
                                      — **the criterion, specialized**: for densely
                                        defined `T`, `perturb T B` is essentially
                                        self-adjoint **iff** `ran((T+B)+i)` and
                                        `ran((T+B)−i)` are both dense. (Specializes
                                        `Cayley.essentiallySelfAdjoint_iff`.)

    * `BoundedPerturbationTransfer` / `essentiallySelfAdjoint_perturb`
                                      — **THE conditional Kato–Rellich theorem.** With
                                        the range-density transfer named as the exact
                                        remaining hypothesis
                                        `BoundedPerturbationTransfer T B`
                                        (`ran((T+B)±i)` dense), a densely-defined
                                        `perturb T B` is essentially self-adjoint.
                                        This pins the one missing analytic step to a
                                        single precise Lean statement.

    * `perturb_clm_essentiallySelfAdjoint`
                                      — **the transfer hypothesis is realizable**
                                        (bounded witness, UNCONDITIONAL): when the
                                        "unbounded" `T` is itself a bounded
                                        self-adjoint `A : H →L[ℂ] H` presented as
                                        `A.toPMap ⊤`, the perturbation
                                        `perturb (A.toPMap ⊤) B` IS essentially
                                        self-adjoint. Proved by identifying it with
                                        `(A+B).toPMap ⊤` and invoking
                                        `ESA.clm_essentiallySelfAdjoint`.

    * `boundedPerturbationTransfer_clm`
                                      — hence `BoundedPerturbationTransfer` holds in
                                        the bounded case: the conditional theorem's
                                        hypothesis is non-vacuous.

  ## What is NOT proved, and why (honest scope statement)

  The genuinely UNBOUNDED Kato–Rellich range-density transfer — deriving
  `BoundedPerturbationTransfer T B` from `EssentiallySelfAdjoint T` (`ran(T±i)` dense)
  and `IsSelfAdjoint B` — is **not** proved. The elementary Neumann argument
  `(T+B) − z = (T − z)(I + (T − z)⁻¹B)` needs the resolvent `(T̄ − z)⁻¹` of the
  self-adjoint closure `T̄ = T**`, and the fact `‖(T̄ − z)⁻¹‖ ≤ 1/|Im z|`; both live
  in von Neumann closure / spectral theory absent from Mathlib v4.32.0 (the same gap
  named in `WeylOperator`'s scope note). The perpendicular route
  `y ⊥ ran((T+B) − z̄) ⇒ (T* + B − z)y = 0` reduces to `ker(T* + B − z) = ⊥`, which
  does not follow elementarily from `ker(T* − z) = ⊥` without that closure. So we ship
  the highest hole-free rung: all of the symmetric-operator content unconditionally,
  the criterion specialized, the remaining step as one precise hypothesis, and a
  non-vacuous bounded witness discharging that hypothesis end-to-end.

  Verification (spec §2A): AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylOperator
import Brockian.WeylCayley
import Brockian.WeylKato
import Brockian.WeylEssSelfAdjoint
import Brockian.WeylFreeLaplacian

namespace Brockian.Weyl.KatoUnbounded

open scoped InnerProductSpace
open Brockian.Weyl.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### The perturbed operator `T + B` -/

/-- **The perturbed operator** `T + B`, defined as Mathlib's `LinearPMap` `+ᵥ`-action
of the bounded operator `↑B` on `T`: same domain `dom T`, action `v ↦ T v + B v`. -/
noncomputable def perturb (T : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  B.toLinearMap +ᵥ T

/-- The perturbed operator acts as `v ↦ B v + T v` on the domain. -/
theorem perturb_apply (T : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (x : (perturb T B).domain) :
    (perturb T B) x = B (x : H) + T x := by
  simp only [perturb, LinearPMap.vadd_apply, ContinuousLinearMap.coe_coe]

/-- The perturbed operator keeps `T`'s domain. -/
theorem perturb_domain (T : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) :
    (perturb T B).domain = T.domain :=
  LinearPMap.vadd_domain _ _

/-- The perturbed operator is densely defined when `T` is. -/
theorem perturb_dense_domain (B : H →L[ℂ] H) {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) : Dense ((perturb T B).domain : Set H) := by
  rw [perturb_domain]; exact hd

/-! ### Symmetry and its analytic corollaries -/

section Symmetric

variable [CompleteSpace H]

/-- **Bounded self-adjoint perturbation preserves symmetry.** `T` symmetric and `B`
self-adjoint ⇒ `perturb T B` symmetric. (Reuses `FreeLaplacian.isSymmetric_vadd_clm`;
the `+ᵥ` cross terms match because `B` is self-adjoint and `T` symmetric.) -/
theorem perturb_isSymmetric {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) : IsSymmetric (perturb T B) :=
  Brockian.Weyl.FreeLaplacian.isSymmetric_vadd_clm B hB T hT

/-- **The basic inequality for the perturbed operator:** `‖(T+B)v − z·v‖ ≥
|Im z|·‖v‖`. Corollary of `IsSymmetric.norm_sub_smul_ge` applied to `perturb T B`. -/
theorem perturb_norm_sub_smul_ge {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (v : (perturb T B).domain) (z : ℂ) :
    |z.im| * ‖(v : H)‖ ≤ ‖(perturb T B) v - z • (v : H)‖ :=
  (perturb_isSymmetric hT hB).norm_sub_smul_ge v z

/-- **`T + B + i` is injective on the domain.** `i` is never an eigenvalue of the
(symmetric) perturbed operator. -/
theorem perturb_apply_ne_I_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) {v : (perturb T B).domain}
    (h : (perturb T B) v = Complex.I • (v : H)) : (v : H) = 0 :=
  Brockian.Weyl.Cayley.apply_ne_I_smul (perturb_isSymmetric hT hB) h

/-- **`T + B − i` is injective on the domain.** `−i` is never an eigenvalue of the
(symmetric) perturbed operator. -/
theorem perturb_apply_ne_neg_I_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) {v : (perturb T B).domain}
    (h : (perturb T B) v = (-Complex.I) • (v : H)) : (v : H) = 0 :=
  Brockian.Weyl.Cayley.apply_ne_neg_I_smul (perturb_isSymmetric hT hB) h

/-- **The Cayley isometry, norm form, for the perturbed operator:**
`‖(T+B)v + i·v‖ = ‖(T+B)v − i·v‖`. -/
theorem perturb_norm_add_I_smul_eq {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (v : (perturb T B).domain) :
    ‖(perturb T B) v + Complex.I • (v : H)‖ = ‖(perturb T B) v - Complex.I • (v : H)‖ :=
  Brockian.Weyl.Cayley.norm_add_I_smul_eq (perturb_isSymmetric hT hB) v

end Symmetric

/-! ### The essential-self-adjointness criterion for the perturbation -/

section Criterion

variable [CompleteSpace H]

/-- **The essential-self-adjointness criterion, specialized to `perturb T B`.** For a
densely-defined `T`, the perturbation is essentially self-adjoint **iff** both
`ran((T+B)+i)` and `ran((T+B)−i)` are dense. Specializes
`Cayley.essentiallySelfAdjoint_iff` via `perturb_dense_domain`. -/
theorem essentiallySelfAdjoint_perturb_iff {T : H →ₗ.[ℂ] H} (B : H →L[ℂ] H)
    (hd : Dense (T.domain : Set H)) :
    EssentiallySelfAdjoint (perturb T B) ↔
      Dense (Brockian.Weyl.Cayley.rangeAddI (perturb T B) : Set H) ∧
      Dense (Brockian.Weyl.Cayley.rangeSubI (perturb T B) : Set H) :=
  Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff (perturb_dense_domain B hd)

/-- **The exact remaining analytic step**, named as one precise proposition: the
range-density transfer for the bounded perturbation. `BoundedPerturbationTransfer T B`
holds when both `ran((T+B)+i)` and `ran((T+B)−i)` are dense — the statement the full
unbounded Kato–Rellich (Neumann/resolvent) argument would derive from
`EssentiallySelfAdjoint T` and `IsSelfAdjoint B`. -/
def BoundedPerturbationTransfer (T : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) : Prop :=
  Dense (Brockian.Weyl.Cayley.rangeAddI (perturb T B) : Set H) ∧
  Dense (Brockian.Weyl.Cayley.rangeSubI (perturb T B) : Set H)

/-- **THE CONDITIONAL KATO–RELLICH THEOREM.** A densely-defined symmetric operator `T`,
perturbed by a bounded self-adjoint `B`, is essentially self-adjoint **provided** the
range-density transfer `BoundedPerturbationTransfer T B` holds. The only content of the
hypothesis is the analytic step blocked on the (Mathlib-absent) self-adjoint closure;
everything else — symmetry, the criterion — is discharged unconditionally above. -/
theorem essentiallySelfAdjoint_perturb {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H)) (h : BoundedPerturbationTransfer T B) :
    EssentiallySelfAdjoint (perturb T B) :=
  (essentiallySelfAdjoint_perturb_iff B hd).mpr h

end Criterion

/-! ### The transfer hypothesis is realizable: the bounded witness -/

section BoundedWitness

variable [CompleteSpace H]

/-- The perturbation of a bounded self-adjoint `A` (as `A.toPMap ⊤`) by a bounded
self-adjoint `B` is **literally** `(A + B).toPMap ⊤`: same full domain, same action
`v ↦ A v + B v`. -/
theorem perturb_clm_eq (A B : H →L[ℂ] H) :
    perturb (A.toPMap ⊤) B = (A + B).toPMap ⊤ := by
  apply LinearPMap.ext
  · rw [perturb_domain, Brockian.Weyl.ESA.clm_domain, Brockian.Weyl.ESA.clm_domain]
  · intro x hf hg
    rw [perturb_apply]
    simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.add_apply]
    rw [add_comm]

/-- **THE BOUNDED WITNESS (unconditional).** When the "unbounded" `T` is itself a
bounded self-adjoint operator `A : H →L[ℂ] H` presented as `A.toPMap ⊤`, the
perturbation `perturb (A.toPMap ⊤) B` by a bounded self-adjoint `B` IS essentially
self-adjoint. Proved by identifying it with `(A+B).toPMap ⊤` (`perturb_clm_eq`) and
invoking `ESA.clm_essentiallySelfAdjoint` on the sum `A + B`. This shows the
conditional theorem's hypothesis is non-vacuous. -/
theorem perturb_clm_essentiallySelfAdjoint {A B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    EssentiallySelfAdjoint (perturb (A.toPMap ⊤) B) := by
  rw [perturb_clm_eq]
  exact Brockian.Weyl.ESA.clm_essentiallySelfAdjoint (A + B) (hA.add hB)

/-- **`BoundedPerturbationTransfer` holds in the bounded case.** Hence the range-density
transfer feeding the conditional Kato–Rellich theorem is realizable: `ran((A+B)±i)` are
dense whenever `A, B` are bounded self-adjoint. -/
theorem boundedPerturbationTransfer_clm {A B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    BoundedPerturbationTransfer (A.toPMap ⊤) B :=
  (essentiallySelfAdjoint_perturb_iff B (Brockian.Weyl.ESA.clm_dense A)).mp
    (perturb_clm_essentiallySelfAdjoint hA hB)

end BoundedWitness

end Brockian.Weyl.KatoUnbounded
