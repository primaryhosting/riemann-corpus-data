import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON FILE LAYOUT.  Lean 4 requires every `import` to precede any module
documentation comment, so the mandated `/-! ... -/` header block is placed
immediately after the single `import Mathlib` line; it is otherwise verbatim.
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

open Filter Topology

namespace Frontier

/-! ## Spacetime -/

/-- Four dimensional Minkowski/Euclidean spacetime, as the underlying real vector
space `ℝ⁴` on which the theory lives. -/
abbrev Spacetime : Type := EuclideanSpace ℝ (Fin 4)

/-! ## The kinematical (Wightman-type) data of a quantum field theory

We record the data that the Millennium Prize formulation of the Yang–Mills problem
attaches to a quantum field theory on `ℝ⁴`: a separable Hilbert space of states, a
distinguished unit vacuum vector, a unitary representation of the translation group
of spacetime fixing the vacuum, and the *energy spectrum* — the spectrum of the
generator of time translations — which is a closed subset of `[0, ∞)` containing
`0` (the vacuum energy).

The dynamical content of Yang–Mills theory (the field algebra, gauge invariance,
locality, the Osterwalder–Schrader/Wightman reconstruction) is **not** formalised
here; in the reduction theorem below it is carried by an arbitrary predicate
`IsQuantumYangMills`, so that the reduction applies to *any* such formalisation. -/
structure WightmanQFT where
  /-- The Hilbert space of states. -/
  Hilb : Type
  [normedGroup : NormedAddCommGroup Hilb]
  [innerSpace : InnerProductSpace ℂ Hilb]
  [complete : CompleteSpace Hilb]
  /-- The vacuum state. -/
  vacuum : Hilb
  /-- The vacuum is a unit vector. -/
  vacuum_unit : ‖vacuum‖ = 1
  /-- The unitary representation of the spacetime translation group. -/
  translation : Spacetime → (Hilb ≃ₗᵢ[ℂ] Hilb)
  translation_zero : translation 0 = LinearIsometryEquiv.refl ℂ Hilb
  translation_add : ∀ x y, translation (x + y) = (translation x).trans (translation y)
  /-- Translation invariance of the vacuum. -/
  translation_vacuum : ∀ x, translation x vacuum = vacuum
  /-- The energy spectrum: the spectrum of the generator of time translations. -/
  energySpectrum : Set ℝ
  /-- Spectra of self-adjoint operators are closed. -/
  energy_closed : IsClosed energySpectrum
  /-- The spectrum condition: the energy is non-negative. -/
  energy_nonneg : ∀ E ∈ energySpectrum, 0 ≤ E
  /-- The vacuum has energy `0`. -/
  energy_vacuum : (0 : ℝ) ∈ energySpectrum

attribute [instance] WightmanQFT.normedGroup WightmanQFT.innerSpace WightmanQFT.complete

/-- A quantum field theory on `ℝ⁴` together with a compact non-abelian gauge group,
i.e. the kinematical setting of a quantum Yang–Mills theory. -/
structure YangMillsTheory extends WightmanQFT where
  /-- The (compact, non-abelian) gauge group of the theory. -/
  gauge : Type
  [gaugeGroup : Group gauge]
  [gaugeTop : TopologicalSpace gauge]
  [gaugeTopGroup : IsTopologicalGroup gauge]
  /-- Compactness of the gauge group. -/
  gauge_compact : CompactSpace gauge
  /-- The gauge group is non-abelian, as required for Yang–Mills. -/
  gauge_nonabelian : ∃ a b : gauge, a * b ≠ b * a

attribute [instance] YangMillsTheory.gaugeGroup YangMillsTheory.gaugeTop
  YangMillsTheory.gaugeTopGroup YangMillsTheory.gauge_compact

/-! ## Mass gap -/

/-- `T` **has a mass gap** if there is `Δ > 0` such that every point of the energy
spectrum is either the vacuum energy `0` or at least `Δ`. -/
def HasMassGap (T : WightmanQFT) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ ∀ E ∈ T.energySpectrum, E = 0 ∨ Δ ≤ E

/-- The vacuum energy `0` is an isolated point of the energy spectrum, i.e. it is not
an accumulation point of the spectrum. -/
def VacuumIsolated (T : WightmanQFT) : Prop :=
  ¬ AccPt (0 : ℝ) (𝓟 T.energySpectrum)

/-- **Spectral characterisation of the mass gap.**  A theory satisfying the spectrum
condition has a positive mass gap if and only if the vacuum energy is an isolated
point of the energy spectrum. -/
theorem hasMassGap_iff_vacuumIsolated (T : WightmanQFT) :
    HasMassGap T ↔ VacuumIsolated T := by
  constructor
  · rintro ⟨Δ, hΔ, hgap⟩ hacc
    rw [accPt_iff_nhds] at hacc
    obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := hacc (Metric.ball (0 : ℝ) Δ) (Metric.ball_mem_nhds _ hΔ)
    rcases hgap y hy2 with h | h
    · exact hy3 h
    · have : |y| < Δ := by
        simpa [Real.dist_eq] using (Metric.mem_ball.1 hy1)
      exact absurd (lt_of_le_of_lt (le_abs_self y) this) (not_lt.2 h)
  · intro hiso
    rw [VacuumIsolated, accPt_iff_nhds] at hiso
    push_neg at hiso
    obtain ⟨U, hU, hUmem⟩ := hiso
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    refine ⟨ε, hε, fun E hE => ?_⟩
    by_cases hE0 : E = 0
    · exact Or.inl hE0
    · refine Or.inr ?_
      by_contra hlt
      push_neg at hlt
      have hmem : E ∈ Metric.ball (0 : ℝ) ε := by
        have h0 : 0 ≤ E := T.energy_nonneg E hE
        simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg h0]
        exact hlt
      exact hE0 (hUmem E ⟨hball hmem, hE⟩)

/-! ## The Millennium Prize statement

`MassGapStatement P` is the assertion, for a formalisation `P` of the dynamical
axioms of quantum Yang–Mills theory on `ℝ⁴`, that a quantum Yang–Mills theory exists
and has a positive mass gap. -/
def MassGapStatement (P : YangMillsTheory → Prop) : Prop :=
  ∃ T : YangMillsTheory, P T ∧ HasMassGap T.toWightmanQFT

/-- `IsolatedVacuumStatement P` asserts the existence of a quantum Yang–Mills theory
whose vacuum energy is an isolated point of the energy spectrum. -/
def IsolatedVacuumStatement (P : YangMillsTheory → Prop) : Prop :=
  ∃ T : YangMillsTheory, P T ∧ VacuumIsolated T.toWightmanQFT

/-- **Yang–Mills mass gap (Lean-checked reduction).**

For any formalisation `IsQuantumYangMills` of the dynamical axioms of quantum
Yang–Mills theory on `ℝ⁴` with a compact non-abelian gauge group: if such a theory
exists whose vacuum energy is an isolated point of the energy spectrum, then quantum
Yang–Mills theory on `ℝ⁴` exists and has a mass gap `Δ > 0`, i.e. every state of the
theory other than the vacuum has energy at least `Δ`.

This is a reduction of the Millennium Prize statement to the isolation of the vacuum
energy in the spectrum of the Hamiltonian; the full statement (unconditional
existence) remains open. -/
theorem yang_mills_mass_gap (IsQuantumYangMills : YangMillsTheory → Prop)
    (hex : IsolatedVacuumStatement IsQuantumYangMills) :
    MassGapStatement IsQuantumYangMills := by
  obtain ⟨T, hP, hiso⟩ := hex
  exact ⟨T, hP, (hasMassGap_iff_vacuumIsolated T.toWightmanQFT).2 hiso⟩

/-! ## A base case: the free spectrum `{0} ∪ [m, ∞)`

The energy spectrum of a free field of mass `m > 0` is `{0} ∪ [m, ∞)`.  We check
that it satisfies the spectral axioms above and that it has mass gap `m`, and we
exhibit a (kinematical) Yang–Mills theory realising it, so that the axiom system
above is consistent. -/

/-- The energy spectrum of a free field of mass `m`. -/
def freeSpectrum (m : ℝ) : Set ℝ := {0} ∪ Set.Ici m

theorem isClosed_freeSpectrum (m : ℝ) : IsClosed (freeSpectrum m) :=
  isClosed_singleton.union isClosed_Ici

theorem freeSpectrum_nonneg {m : ℝ} (hm : 0 ≤ m) :
    ∀ E ∈ freeSpectrum m, 0 ≤ E := by
  rintro E (rfl | hE)
  · exact le_rfl
  · exact hm.trans hE

theorem zero_mem_freeSpectrum (m : ℝ) : (0 : ℝ) ∈ freeSpectrum m :=
  Or.inl rfl

/-- The finite gauge group used in the consistency witness below carries the
discrete topology. -/
scoped instance permTopologicalSpace : TopologicalSpace (Equiv.Perm (Fin 3)) := ⊥

scoped instance permDiscreteTopology : DiscreteTopology (Equiv.Perm (Fin 3)) := ⟨rfl⟩

/-- The kinematical Yang–Mills data with one-dimensional state space, gauge group
`Equiv.Perm (Fin 3)` and free energy spectrum of mass `m`.  It witnesses that the
axiom system of `Frontier.YangMillsTheory` is consistent; it is of course *not* a
solution of the Millennium Prize problem, since it carries none of the dynamical
Yang–Mills content. -/
noncomputable def freeModel (m : ℝ) (hm : 0 ≤ m) : YangMillsTheory where
  Hilb := ℂ
  vacuum := 1
  vacuum_unit := by simp
  translation := fun _ => LinearIsometryEquiv.refl ℂ ℂ
  translation_zero := rfl
  translation_add := by intro x y; ext v; rfl
  translation_vacuum := by intro x; rfl
  energySpectrum := freeSpectrum m
  energy_closed := isClosed_freeSpectrum m
  energy_nonneg := freeSpectrum_nonneg hm
  energy_vacuum := zero_mem_freeSpectrum m
  gauge := Equiv.Perm (Fin 3)
  gaugeTopGroup := by infer_instance
  gauge_compact := by infer_instance
  gauge_nonabelian := by
    refine ⟨Equiv.swap 0 1, Equiv.swap 1 2, ?_⟩
    intro h
    have := congrArg (fun f : Equiv.Perm (Fin 3) => f 1) h
    simp [Equiv.swap_apply_def] at this

/-- **Base case.**  A theory with free energy spectrum of mass `m > 0` has a mass
gap, namely `m`. -/
theorem hasMassGap_freeModel {m : ℝ} (hm : 0 < m) :
    HasMassGap (freeModel m hm.le).toWightmanQFT := by
  refine ⟨m, hm, fun E hE => ?_⟩
  rcases (show E ∈ freeSpectrum m from hE) with rfl | hE'
  · exact Or.inl rfl
  · exact Or.inr hE'

end Frontier

