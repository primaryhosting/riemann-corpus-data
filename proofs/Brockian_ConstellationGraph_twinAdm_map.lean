import Mathlib

/-
# Constellation Sieve Spectrum — Brick 4: the +3 flow RUN-CAP and degree bound.

Bricks 1–3 built the twin/constellation **wheel** and its Euler-product count
`∏_p (p − ν_p)`. This brick supplies the *structural* fact that explains why the wheel
graph decomposes into short paths `P₁, P₂, P₃`: under the `+3` translation flow, the
twin-admissible residues form **runs of length at most 3**.

A residue `a` is *twin-admissible* (`twinAdm a`) iff both `a` and `a + 2` are units of
`ZMod n` — the genuine coprimality/unit survival condition of the twin wheel.

`twin_run_cap_mod5`   — **the run cap (mod 5).** There is no `a : ZMod 5` with all four of
                        `a, a+3, a+6, a+9` twin-admissible. Over the field `ZMod 5`,
                        `IsUnit x ↔ x ≠ 0`, so this is a finite check: the four shifts hit the
                        distinct classes `{a, a+3, a+1, a+4}` (since `6 ≡ 1`, `9 ≡ 4` mod 5),
                        and the twin-forbidden classes are `{0, 3}` (`a ≠ 0`, `a + 2 ≠ 0`),
                        leaving only the three allowed classes `{1,2,4}` — four distinct
                        residues cannot all avoid two forbidden classes. Proof by `decide`.

`twin_no_four_run`    — **the lift.** For any modulus `M` divisible by `5`, no `a : ZMod M`
                        has all four of `a, a+3, a+6, a+9` twin-admissible. The reduction ring
                        hom `φ = ZMod.castHom : ZMod M →+* ZMod 5` sends units to units and
                        `a + k` to `φ a + k`, so a mod-`M` 4-run pushes forward to a mod-5
                        4-run, contradicting `twin_run_cap_mod5`. Hence every twin-admissible
                        `+3`-run has length ≤ 3.

`plus_three_neighbourhood` — **the degree bound.** If `b` is `+3`-adjacent to `a`
                        (`b − a = 3` or `a − b = 3`) then `b ∈ {a + 3, a − 3}`, i.e. each
                        vertex of the `+3` flow graph has at most two neighbours (degree ≤ 2).

`plusThreeGraph` / `plusThreeGraph_neighbour` — the `+3` adjacency packaged as a
                        `SimpleGraph (ZMod n)` (symmetric, irreflexive), with the same
                        neighbourhood confinement `{a + 3, a − 3}`.

Together: degree ≤ 2 (paths/cycles) + run length ≤ 3 ⇒ the wheel graph is a union of the
short paths `P₁, P₂, P₃`. No `sorry`, `admit`, `native_decide`, or `axiom` is used.
-/

namespace Brockian.ConstellationGraph

/-- **Twin-admissibility.** A residue `a : ZMod n` is twin-admissible iff both `a` and its
`+2` twin partner `a + 2` are units of `ZMod n` (coprime to the modulus). This is the genuine
unit/coprimality survival condition of the twin wheel. -/
def twinAdm {n : ℕ} (a : ZMod n) : Prop := IsUnit a ∧ IsUnit (a + 2)

/-- **Brick 4 — the mod-5 run cap.** No residue `a : ZMod 5` yields a full four-term
twin-admissible run `a, a+3, a+6, a+9` under the `+3` flow.

Over the field `ZMod 5`, `IsUnit x ↔ x ≠ 0`, so the statement is a finite check: the four
shifts occupy the distinct classes `{a, a+3, a+1, a+4}` (as `6 ≡ 1`, `9 ≡ 4` mod 5), while the
twin condition forbids the classes `{0, 3}`, leaving only `{1, 2, 4}` — four distinct residues
cannot all avoid two forbidden classes, so at least one term is non-admissible. This is the
load-bearing structural cap: twin-admissible `+3`-runs have length at most 3. -/
theorem twin_run_cap_mod5 :
    ¬ ∃ a : ZMod 5, twinAdm a ∧ twinAdm (a + 3) ∧ twinAdm (a + 6) ∧ twinAdm (a + 9) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp only [twinAdm, isUnit_iff_ne_zero]
  decide +revert

/-- Ring homs transport twin-admissibility: if `a` is twin-admissible then so is `φ a`, since
`φ` carries units to units and `φ (a + 2) = φ a + 2`. -/
theorem twinAdm_map {n m : ℕ} (φ : ZMod n →+* ZMod m) {a : ZMod n}
    (h : twinAdm a) : twinAdm (φ a) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.map φ, ?_⟩
  have hshift : φ a + 2 = φ (a + 2) := by simp [map_add, map_ofNat]
  rw [hshift]
  exact h2.map φ

/-- **Brick 4 — the lift.** For any modulus `M` divisible by `5`, no residue `a : ZMod M`
gives a four-term twin-admissible `+3`-run `a, a+3, a+6, a+9`.

The reduction ring hom `φ = ZMod.castHom h5 (ZMod 5)` sends units to units and satisfies
`φ (a + k) = φ a + k`; a mod-`M` 4-run therefore pushes forward to a mod-5 4-run, contradicting
`twin_run_cap_mod5`. Hence over *every* modulus divisible by 5 the twin-admissible `+3`-runs
have length at most 3. -/
theorem twin_no_four_run (M : ℕ) [NeZero M] (h5 : 5 ∣ M) (a : ZMod M) :
    ¬ (twinAdm a ∧ twinAdm (a + 3) ∧ twinAdm (a + 6) ∧ twinAdm (a + 9)) := by
  intro h
  obtain ⟨ha, ha3, ha6, ha9⟩ := h
  set φ : ZMod M →+* ZMod 5 := ZMod.castHom h5 (ZMod 5) with hφ
  refine twin_run_cap_mod5 ⟨φ a, twinAdm_map φ ha, ?_, ?_, ?_⟩
  · have h3 := twinAdm_map φ ha3
    simpa [map_add, map_ofNat] using h3
  · have h6 := twinAdm_map φ ha6
    simpa [map_add, map_ofNat] using h6
  · have h9 := twinAdm_map φ ha9
    simpa [map_add, map_ofNat] using h9

/-- **Brick 4 — the degree bound.** In the `+3` flow graph, adjacency of `b` to `a`
(`b − a = 3` or `a − b = 3`) forces `b ∈ {a + 3, a − 3}`: every vertex has at most two
`+3`-neighbours, so the flow graph has maximum degree 2 (a disjoint union of paths and cycles).
Combined with the run cap this yields the short paths `P₁, P₂, P₃`. -/
theorem plus_three_neighbourhood {n : ℕ} (a b : ZMod n) (h : b - a = 3 ∨ a - b = 3) :
    b ∈ ({a + 3, a - 3} : Finset (ZMod n)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases h with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination -h)

/-- The `+3` translation flow as a `SimpleGraph` on `ZMod n`: `a` and `b` are adjacent iff they
differ by `±3` (and are distinct). Symmetric and irreflexive by construction. -/
def plusThreeGraph (n : ℕ) : SimpleGraph (ZMod n) where
  Adj a b := (b - a = 3 ∨ a - b = 3) ∧ a ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- Neighbourhood confinement for the `+3` flow graph: any graph-neighbour `b` of `a` lies in
`{a + 3, a − 3}`, so `plusThreeGraph n` has maximum degree ≤ 2. -/
theorem plusThreeGraph_neighbour {n : ℕ} {a b : ZMod n}
    (h : (plusThreeGraph n).Adj a b) : b ∈ ({a + 3, a - 3} : Finset (ZMod n)) :=
  plus_three_neighbourhood a b h.1

end Brockian.ConstellationGraph
