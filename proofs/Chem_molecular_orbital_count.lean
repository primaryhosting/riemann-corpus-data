/-
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The space of molecular orbitals obtained by the LCAO (Linear Combination of Atomic
Orbitals) method from a family `ao` of `n` atomic orbitals: it is the space of all linear
combinations `∑ i, c i • ao i` of the atomic orbitals, i.e. their span. -/
def lcaoSpan (n : ℕ) (ao : Fin n → V) : Submodule K V :=
  Submodule.span K (Set.range ao)

/-- Every molecular orbital is a linear combination of the atomic orbitals, and conversely. -/
theorem mem_lcaoSpan_iff (n : ℕ) (ao : Fin n → V) (v : V) :
    v ∈ lcaoSpan (K := K) n ao ↔ ∃ c : Fin n → K, ∑ i, c i • ao i = v :=
  Submodule.mem_span_range_iff_exists_fun K

/-- **LCAO dimension preservation.**  A linear combination of `n` (linearly independent)
atomic orbitals yields a space of molecular orbitals of dimension exactly `n`: the LCAO
procedure produces exactly `n` molecular orbitals. -/
theorem molecular_orbital_count (n : ℕ) (ao : Fin n → V) (h : LinearIndependent K ao) :
    Module.finrank K (lcaoSpan (K := K) n ao) = n := by
  rw [lcaoSpan, finrank_span_eq_card h, Fintype.card_fin]

/-- The `n` molecular orbitals themselves: a basis of the LCAO space indexed by `Fin n`,
so the molecular orbitals are in bijection with the atomic orbitals. -/
noncomputable def moBasis (n : ℕ) (ao : Fin n → V) (h : LinearIndependent K ao) :
    Module.Basis (Fin n) K (lcaoSpan (K := K) n ao) :=
  Module.Basis.span h

/-- The coefficient space `Fin n → K` of LCAO coefficients is linearly isomorphic to the
space of molecular orbitals: distinct coefficient vectors give distinct molecular orbitals
and every molecular orbital arises this way. -/
noncomputable def lcaoEquiv (n : ℕ) (ao : Fin n → V) (h : LinearIndependent K ao) :
    (Fin n → K) ≃ₗ[K] lcaoSpan (K := K) n ao :=
  (Finsupp.linearEquivFunOnFinite K K (Fin n)).symm.trans (moBasis n ao h).repr.symm

end Chem

