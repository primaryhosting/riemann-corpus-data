import Mathlib

/-! # Phase-Depth dynamical-zeta / Lefschetz determinant identity

The crux lemma `circulant_det` — the characteristic determinant of the cyclic-shift
(circulant) permutation matrix — is proved from scratch by the Leibniz formula, collapsing
the permutation sum onto the identity and the shift itself. -/

namespace Brockian.PhaseDepthZeta

open Equiv Equiv.Perm Matrix Finset

variable {R : Type*} [CommRing R]

/-- **The circulant determinant.** For the cyclic-shift permutation `finRotate n` on
`Fin n`, `det (1 - z • P) = 1 - z ^ n`, where `P` is its permutation matrix.  (`0 < n` is
required: for `n = 0` the empty determinant is `1 ≠ 1 - z⁰ = 0`.) -/
theorem circulant_det (n : ℕ) (hn : 0 < n) (z : R) :
    Matrix.det (1 - z • (Equiv.toPEquiv (finRotate n)).toMatrix) = 1 - z ^ n := by
  match n, hn with
  | 1, _ =>
      rw [finRotate_one]
      simp [Matrix.det_fin_one, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  | (m + 2), _ =>
      -- Abbreviations for the shift and its inverse.
      set ρ : Perm (Fin (m + 2)) := (finRotate (m + 2))⁻¹ with hρ
      set M : Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
        1 - z • (Equiv.toPEquiv (finRotate (m + 2))).toMatrix with hMdef
      -- Per-entry formula for `M`.
      have hM : ∀ i j, M i j
          = (if i = j then (1 : R) else 0)
            - z * (if finRotate (m + 2) i = j then 1 else 0) := by
        intro i j
        simp only [hMdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff, smul_eq_mul]
      -- `finRotate` is fixed-point-free (support is everything).
      have hfp : ∀ i, finRotate (m + 2) i ≠ i := fun i =>
        Equiv.Perm.mem_support.mp (by rw [support_finRotate]; exact Finset.mem_univ i)
      -- Hence so is its inverse `ρ`.
      have hrhofp : ∀ i, ρ i ≠ i := by
        intro i
        have hi : i ∈ ((finRotate (m + 2))⁻¹).support := by
          rw [Equiv.Perm.support_inv, support_finRotate]; exact Finset.mem_univ i
        rw [hρ]; exact Equiv.Perm.mem_support.mp hi
      -- `ρ` is a cycle (inverse of a cycle).
      have hrhocyc : IsCycle ρ := by rw [hρ]; exact isCycle_finRotate.inv
      -- `finRotate` cancels `ρ`.
      have hAppInv : ∀ i, finRotate (m + 2) (ρ i) = i := by
        intro i; rw [hρ]; simp
      ------------------------------------------------------------------
      -- The combinatorial heart: a permutation `τ` with `τ i ∈ {i, ρ i}`
      -- everywhere is either the identity or `ρ`.
      ------------------------------------------------------------------
      have hcomb2 : ∀ τ : Perm (Fin (m + 2)),
          (∀ i, τ i = i ∨ τ i = ρ i) → τ = 1 ∨ τ = ρ := by
        intro τ hall'
        by_cases hfix : ∀ i, τ i = i
        · left; exact Equiv.ext hfix
        · right
          push_neg at hfix
          obtain ⟨i0, hi0⟩ := hfix
          have hi0ρ : τ i0 = ρ i0 := (hall' i0).resolve_left hi0
          have hclose : ∀ i, τ i = ρ i → τ (ρ i) = ρ (ρ i) := by
            intro i hi
            rcases hall' (ρ i) with h | h
            · exfalso
              have heq : τ (ρ i) = τ i := by rw [h, hi]
              exact hrhofp i (τ.injective heq)
            · exact h
          have hSpow : ∀ k : ℕ, τ ((ρ ^ k) i0) = ρ ((ρ ^ k) i0) := by
            intro k
            induction k with
            | zero => simpa using hi0ρ
            | succ k ih =>
                have hc := hclose ((ρ ^ k) i0) ih
                rw [pow_succ']
                simpa [Equiv.Perm.mul_apply] using hc
          have hAll : ∀ j, τ j = ρ j := by
            intro j
            obtain ⟨k, hk⟩ :=
              (hrhocyc.sameCycle (hrhofp i0) (hrhofp j)).exists_nat_pow_eq
            rw [← hk]; exact hSpow k
          exact Equiv.ext hAll
      ------------------------------------------------------------------
      -- Off the two special permutations, the Leibniz term vanishes.
      ------------------------------------------------------------------
      have key : ∀ τ : Perm (Fin (m + 2)),
          τ ∉ ({1, ρ} : Finset (Perm (Fin (m + 2)))) →
          ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (τ i) i = 0 := by
        intro τ hτ
        rw [Finset.mem_insert, Finset.mem_singleton] at hτ
        push_neg at hτ
        obtain ⟨hτ1, hτρ⟩ := hτ
        suffices hp : ∏ i, M (τ i) i = 0 by rw [hp, mul_zero]
        by_contra hp
        have hall : ∀ i, τ i = i ∨ τ i = ρ i := by
          intro i
          by_contra hii
          push_neg at hii
          obtain ⟨hne1, hne2⟩ := hii
          refine hp (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
          rw [hM, if_neg hne1, if_neg ?_]
          · ring
          · intro hc
            apply hne2
            apply (finRotate (m + 2)).injective
            rw [hAppInv]
            exact hc
        rcases hcomb2 τ hall with h | h
        · exact hτ1 h
        · exact hτρ h
      ------------------------------------------------------------------
      -- Assemble: det = f(1) + f(ρ) = 1 - z^(m+2).
      ------------------------------------------------------------------
      -- Diagonal entries are 1.
      have hdiag : ∀ i, M i i = 1 := by
        intro i
        rw [hM, if_pos rfl, if_neg (hfp i)]; ring
      -- Entries along the `ρ`-diagonal are `-z`.
      have hoff : ∀ i, M (ρ i) i = -z := by
        intro i
        rw [hM, if_neg (hrhofp i), if_pos (hAppInv i)]; ring
      have h1ρ : (1 : Perm (Fin (m + 2))) ≠ ρ := by
        intro h
        exact hrhofp ⟨0, by omega⟩ (by rw [← h]; rfl)
      have hterm1 : ∏ i, M ((1 : Perm (Fin (m + 2))) i) i = 1 := by
        simp only [Equiv.Perm.coe_one, id_eq, hdiag, Finset.prod_const_one]
      have hprodρ : ∏ i, M (ρ i) i = (-z) ^ (m + 2) := by
        simp only [hoff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hsignρ : ((Equiv.Perm.sign ρ : ℤ) : R) = (-1) ^ (m + 1) := by
        rw [hρ, Equiv.Perm.sign_inv, sign_finRotate]
        have hmm : m + 2 - 1 = m + 1 := by omega
        rw [hmm]; push_cast; ring
      rw [det_apply']
      rw [← Finset.sum_subset
            (Finset.subset_univ ({1, ρ} : Finset (Perm (Fin (m + 2)))))
            (fun σ _ hσ => key σ hσ)]
      rw [Finset.sum_pair h1ρ, hterm1, hprodρ, hsignρ]
      have e1 : ((Equiv.Perm.sign (1 : Perm (Fin (m + 2))) : ℤ) : R) = 1 := by simp
      rw [e1, show (-z) ^ (m + 2) = (-1) ^ (m + 2) * z ^ (m + 2) from neg_pow z (m + 2),
        ← mul_assoc, ← pow_add, Odd.neg_one_pow ⟨m + 1, by ring⟩]
      ring

/-- **The block-cyclic (standard-form) determinant.**  The permutation
`(finRotate L).prodCongr (id)` on `Fin L × Fin m` is a disjoint union of `m` cycles, each of
length `L` (the standard representative of the conjugacy class "m cycles of length L").  Its
characteristic determinant is `(1 - z^L)^m`.  This is the concrete engine behind
`det_one_sub_smul_of_uniform_cycles`: it computes the determinant of the block-diagonal normal
form via `circulant_det` on each block. -/
theorem blockCyclic_det (m L : ℕ) (hL : 0 < L) (z : R) :
    Matrix.det (1 - z •
        (Equiv.Perm.permMatrix R ((finRotate L).prodCongr (Equiv.refl (Fin m)))))
      = (1 - z ^ L) ^ m := by
  have hmat : (1 - z • (Equiv.Perm.permMatrix R ((finRotate L).prodCongr (Equiv.refl (Fin m)))))
      = blockDiagonal
          (fun _ : Fin m => (1 - z • ((finRotate L).permMatrix R) : Matrix (Fin L) (Fin L) R)) := by
    ext ⟨b, a⟩ ⟨b', a'⟩
    by_cases haa : a = a'
    · subst haa
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, blockDiagonal_apply,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff,
        smul_eq_mul, Prod.ext_iff, Equiv.prodCongr_apply]
    · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, blockDiagonal_apply,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff,
        smul_eq_mul, Prod.ext_iff, Equiv.prodCongr_apply, haa]
  rw [hmat, det_blockDiagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    show Matrix.det (1 - z • (Equiv.Perm.permMatrix R (finRotate L))) = 1 - z ^ L
      from circulant_det L hL z]

/-!
## Determinant assembly (Steps 2–3): the remaining Mathlib gap

With `circulant_det` and `blockCyclic_det` in hand, the **standard-form** determinant of a
permutation with `m` cycles all of length `L` — i.e. `(1 - z^L)^m` — is fully established
(AXLE-clean).  The two remaining links to the phase-depth identity
`det(1 − z·T_c) = det(1 − z⁵·ρ(H))` are:

* **`det_one_sub_smul_of_uniform_cycles`** (general Step 2): for an *arbitrary* fintype `S`
  and `σ : Perm S` with `σ.cycleType = Multiset.replicate m L` (`2 ≤ L`),
  `det(1 − z·σ.permMatrix R) = (1 − z^L)^m`.  The proof reduces to `blockCyclic_det` by
  transporting `σ` to the standard model on `Fin L × Fin m`:
    1. pick `e : S ≃ Fin L × Fin m` (exists since `Fintype.card S = L * m`);
    2. `det` is a conjugacy/reindex invariant
       (`Matrix.det_submatrix_equiv_self`, and `permMatrix` is a `MonoidHom` so
       `det(1 − z·permMatrix(g σ g⁻¹)) = det(1 − z·permMatrix σ)`);
    3. `(finRotate L).prodCongr 1` and `e.permCongr σ` have equal `cycleType`, hence are
       conjugate (`Equiv.Perm.isConj_iff_cycleType_eq`).

  **Missing Mathlib API** (each absent as of `lean-4.32.2`, and the precise blocker):
    - `Equiv.Perm.cycleType ((finRotate L).prodCongr 1) = Multiset.replicate m L` — no lemma
      computes the `cycleType` of an `Equiv.prodCongr` / external direct product of
      permutations; it would need to be developed from `cycleType_finRotate` plus a
      "disjoint product" cycle-type-additivity lemma that Mathlib does not expose for
      `prodCongr`.
    - `(e.permCongr σ).permMatrix R = reindex e e (σ.permMatrix R)` and the invariance of the
      *characteristic* determinant `det(1 − z·•)` under `permCongr`/conjugation — the pieces
      exist (`det_submatrix_equiv_self`, `permMatrixHom`) but the glue lemma
      `det(1 − z·permMatrix τ)` = class function of `τ` is not in Mathlib and must be built.

* **`phase_depth_det_identity`** (Step 3): apply the general Step 2 with
  `(σ, L, m) = (sigmaMap c` bundled as `sigmaPerm c, 5·addOrderOf H, |A|/addOrderOf H)` and
  `(rhoMap H` bundled, `addOrderOf H, |A|/addOrderOf H)` with `z ↦ z⁵` on the ρ side; both sides
  become `(1 − z^{5·ord H})^{|A|/ord H}` and coincide.  The dynamical inputs (every
  `sigmaPerm`-cycle has length exactly `5·ord H`, every `rho`-cycle length `ord H`) are already
  proved AXLE-clean in `Brockian/PhaseDepthCycles.lean` (`sigma_minimalPeriod`,
  `rho_minimalPeriod`, `cycle_length_bridge`); what is missing is exactly the
  cycle-length-multiset ⟹ `cycleType = replicate _ _` bridge and then Step 2.  Concretely the
  open sub-goal is `(sigmaPerm c).cycleType = Multiset.replicate (Fintype.card A / addOrderOf (Htot c))
  (5 * addOrderOf (Htot c))`, i.e. turning "all `minimalPeriod`s equal" into a `cycleType`
  equality — Mathlib has `cycleType` and `minimalPeriod`/`cycleOf` API but no single lemma
  "all cycles equal length ⟹ `cycleType = replicate`", so it too requires a short development.

Both `circulant_det` and `blockCyclic_det` are unconditional, general, and Mathlib-worthy; they
are the genuinely hard analytic core.  The residual gap is bookkeeping API around `cycleType`,
not further "hard link" mathematics. -/

end Brockian.PhaseDepthZeta
