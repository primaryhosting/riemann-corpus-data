import Mathlib

/-! # Nonabelian gauge classification of pentagon holonomy.

This module proves the **nonabelian analogue** of the abelian phase-depth classification
(`Brockian.PhaseDepthClassification.cohomologous_iff_totalDepth_eq`). There the fiber is an
abelian group `G`, gauge-equivalence is being cohomologous, and the complete invariant is the
total depth `∑ j, c j`. Here we replace `G` by an arbitrary (possibly nonabelian) `Group H`.

Setup. The directed pentagon is the cycle `ZMod 5`. An *edge labeling* is `c : ZMod 5 → H`,
where `c j` is the label carried on the edge `j → j + 1`. A *gauge transformation*
`g : ZMod 5 → H` acts by
  `(g • c) j = g (j + 1) * c j * (g j)⁻¹`,
and two labelings are **gauge-equivalent** (`Gauge c₁ c₂`) when some `g` conjugates the first
into the second edge-by-edge. The **ordered holonomy** based at `0` is the path-ordered product
once around the loop,
  `hol c = c 4 * c 3 * c 2 * c 1 * c 0`.

Headline (`gauge_iff_conj`): `Gauge c₁ c₂ ↔ IsConj (hol c₁) (hol c₂)`. So the gauge classes of
edge-labelings on `C₅` are in bijection with the **conjugacy classes of `H`**, with invariant
the conjugacy class of the ordered product. For abelian `H` this collapses to equality of the
total holonomy, recovering the abelian classification (`gauge_iff_hol_eq`, `hol_eq_prod`).

Kept self-contained (`import Mathlib`) to match the corpus's per-module AXLE attestation model.
-/

namespace Brockian.PhaseDepthNonabelian

section Group

variable {H : Type*} [Group H]

/-- The ordered (path-ordered) holonomy of an edge labeling, based at `0`: the product of the
five edge labels once around the directed pentagon, in traversal order. -/
def hol (c : ZMod 5 → H) : H := c 4 * c 3 * c 2 * c 1 * c 0

/-- Two edge labelings are **gauge-equivalent** if a gauge transformation `g : ZMod 5 → H`
conjugates one into the other along every edge: `c₂ j = g (j+1) * c₁ j * (g j)⁻¹`. -/
def Gauge (c₁ c₂ : ZMod 5 → H) : Prop :=
  ∃ g : ZMod 5 → H, ∀ j, c₂ j = g (j + 1) * c₁ j * (g j)⁻¹

/-- The **standard labeling** carrying `X` on the last edge (`4 → 0`) and the identity on the
other four edges. Its ordered holonomy is `X`. Defined via an explicit vector so that
`stdLabel X k` reduces definitionally on each concrete `k : ZMod 5`. -/
def stdLabel (X : H) : ZMod 5 → H :=
  fun j => (![(1 : H), 1, 1, 1, X] : Fin 5 → H) j

/-- `Gauge` is reflexive (witness: the identity gauge `g = 1`). -/
theorem gauge_refl (c : ZMod 5 → H) : Gauge c c := by
  refine ⟨fun _ => 1, ?_⟩
  intro j
  group

/-- `Gauge` is symmetric (witness: invert the gauge, `g' = g⁻¹`). -/
theorem gauge_symm {c₁ c₂ : ZMod 5 → H} (h : Gauge c₁ c₂) : Gauge c₂ c₁ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨fun j => (g j)⁻¹, ?_⟩
  intro j
  rw [hg j]
  group

/-- `Gauge` is transitive (witness: compose the gauges, `k = h · g`). -/
theorem gauge_trans {c₁ c₂ c₃ : ZMod 5 → H}
    (h₁ : Gauge c₁ c₂) (h₂ : Gauge c₂ c₃) : Gauge c₁ c₃ := by
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨h, hh⟩ := h₂
  refine ⟨fun j => h j * g j, ?_⟩
  intro j
  rw [hh j, hg j]
  group

/-- **Target 1 — forward direction (`hol_gauge`).** A gauge transformation conjugates the
ordered holonomy: if `Gauge c₁ c₂` then `hol c₂ = u * hol c₁ * u⁻¹` with `u = g 0`. All interior
gauge factors telescope; only the basepoint value `g 0` survives, conjugating the product. -/
theorem hol_gauge {c₁ c₂ : ZMod 5 → H} (h : Gauge c₁ c₂) :
    ∃ u : H, hol c₂ = u * hol c₁ * u⁻¹ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g 0, ?_⟩
  simp only [hol]
  rw [hg 4, hg 3, hg 2, hg 1, hg 0]
  rw [show (4 : ZMod 5) + 1 = 0 from by decide, show (3 : ZMod 5) + 1 = 4 from by decide,
      show (2 : ZMod 5) + 1 = 3 from by decide, show (1 : ZMod 5) + 1 = 2 from by decide,
      show (0 : ZMod 5) + 1 = 1 from by decide]
  group

/-- **Trivialization.** Every labeling is gauge-equivalent to the standard form carrying all of
its holonomy on the last edge: `Gauge c (stdLabel (hol c))`. The witnessing gauge sweeps every
label into edge `4` via partial products `g k = (c (k-1) * ⋯ * c 0)⁻¹` (with `g 0 = 1`). -/
theorem gauge_trivialize (c : ZMod 5 → H) : Gauge c (stdLabel (hol c)) := by
  refine ⟨fun k =>
    (![(1 : H), (c 0)⁻¹, (c 1 * c 0)⁻¹, (c 2 * c 1 * c 0)⁻¹, (c 3 * c 2 * c 1 * c 0)⁻¹] :
      Fin 5 → H) k, ?_⟩
  intro j
  fin_cases j
  · show (1 : H) = (c 0)⁻¹ * c 0 * (1 : H)⁻¹
    group
  · show (1 : H) = (c 1 * c 0)⁻¹ * c 1 * ((c 0)⁻¹)⁻¹
    group
  · show (1 : H) = (c 2 * c 1 * c 0)⁻¹ * c 2 * ((c 1 * c 0)⁻¹)⁻¹
    group
  · show (1 : H) = (c 3 * c 2 * c 1 * c 0)⁻¹ * c 3 * ((c 2 * c 1 * c 0)⁻¹)⁻¹
    group
  · show c 4 * c 3 * c 2 * c 1 * c 0
        = (1 : H) * c 4 * ((c 3 * c 2 * c 1 * c 0)⁻¹)⁻¹
    group

/-- **Conjugation of standard forms.** The constant gauge `g = u` sends the standard labeling for
`X` to the standard labeling for `u * X * u⁻¹`: `Gauge (stdLabel X) (stdLabel (u * X * u⁻¹))`. -/
theorem gauge_stdLabel_conj (X u : H) :
    Gauge (stdLabel X) (stdLabel (u * X * u⁻¹)) := by
  refine ⟨fun _ => u, ?_⟩
  intro j
  fin_cases j
  · show (1 : H) = u * 1 * u⁻¹
    group
  · show (1 : H) = u * 1 * u⁻¹
    group
  · show (1 : H) = u * 1 * u⁻¹
    group
  · show (1 : H) = u * 1 * u⁻¹
    group
  · show u * X * u⁻¹ = u * X * u⁻¹
    rfl

/-- **Target 2 — reverse direction (`gauge_of_conj`).** If the ordered holonomies are conjugate,
`hol c₂ = u * hol c₁ * u⁻¹`, the labelings are gauge-equivalent. Proof: trivialize each labeling
to its standard form, connect the two standard forms by the constant gauge `u`, and chain. -/
theorem gauge_of_conj {c₁ c₂ : ZMod 5 → H}
    (h : ∃ u : H, hol c₂ = u * hol c₁ * u⁻¹) : Gauge c₁ c₂ := by
  obtain ⟨u, hu⟩ := h
  have g1 : Gauge c₁ (stdLabel (hol c₁)) := gauge_trivialize c₁
  have g2 : Gauge c₂ (stdLabel (hol c₂)) := gauge_trivialize c₂
  have g3 : Gauge (stdLabel (hol c₁)) (stdLabel (hol c₂)) := by
    rw [hu]; exact gauge_stdLabel_conj (hol c₁) u
  exact gauge_trans g1 (gauge_trans g3 (gauge_symm g2))

/-- **Target 3 — HEADLINE (`gauge_iff_conj`).** On the directed pentagon, two edge-labelings are
gauge-equivalent **iff** their ordered holonomies are conjugate in `H`. Hence the gauge classes of
labelings on `C₅` are in bijection with the conjugacy classes of `H`, the complete invariant being
the conjugacy class of the ordered product `hol c`. This is the exact nonabelian analogue of
`cohomologous_iff_totalDepth_eq`. -/
theorem gauge_iff_conj {c₁ c₂ : ZMod 5 → H} :
    Gauge c₁ c₂ ↔ IsConj (hol c₁) (hol c₂) := by
  rw [isConj_iff]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := hol_gauge h
    exact ⟨u, hu.symm⟩
  · rintro ⟨u, hu⟩
    exact gauge_of_conj ⟨u, hu.symm⟩

end Group

section CommGroup

variable {H : Type*} [CommGroup H]

/-- **Sanity, abelian recovery of the ordered product.** For abelian `H` the ordered holonomy is
just the (order-independent) product of all edge labels: `hol c = ∏ j, c j`. -/
theorem hol_eq_prod (c : ZMod 5 → H) : hol c = ∏ j, c j := by
  rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [hol]
  ac_rfl

/-- **Target 4 — sanity corollary.** For abelian `H`, conjugacy is equality, so the nonabelian
classification collapses to the abelian one: two labelings are gauge-equivalent **iff** they have
equal total holonomy `hol c₁ = hol c₂`. This is precisely the shape of the abelian
`cohomologous_iff_totalDepth_eq`, now recovered as a special case. -/
theorem gauge_iff_hol_eq {c₁ c₂ : ZMod 5 → H} :
    Gauge c₁ c₂ ↔ hol c₁ = hol c₂ := by
  rw [gauge_iff_conj, isConj_iff]
  constructor
  · rintro ⟨u, hu⟩
    have key : u * hol c₁ * u⁻¹ = hol c₁ := by
      rw [mul_comm u (hol c₁)]; group
    rw [key] at hu
    exact hu
  · intro h
    exact ⟨1, by simp [h]⟩

end CommGroup

end Brockian.PhaseDepthNonabelian
