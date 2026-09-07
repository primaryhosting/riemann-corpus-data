import Mathlib

/-! # Phase-Depth determinant identity — the last mile, AXLE-clean (`lean-4.32.2`)

This self-contained file proves the **phase-depth dynamical-zeta / Lefschetz determinant
identity**

  `det(1 − z · T_c) = det(1 − z⁵ · ρ(H))`,

where `T_c` is the permutation matrix of the transfer permutation `σ_c(j,a) = (j+1, a+c j)`
on `S = ZMod 5 × A`, and `ρ(H)(a) = a + H` (`H = ∑_j c j` the total holonomy).

It reuses verbatim the two already-proved analytic building blocks
(`circulant_det`, `blockCyclic_det`) and the dynamical period lemmas
(`sigma_minimalPeriod`, `rho_minimalPeriod`), and closes the three "last-mile" lemmas:

1. `cycleType_of_uniform_minimalPeriod` — uniform minimal period `L ≥ 2` forces
   `cycleType = replicate (card X / L) L`.
2. `det_one_sub_smul_eq_of_cycleType` — `cycleType = replicate m L` (with `card = L·m`)
   gives `det(1 − z·permMatrix σ) = (1 − z^L)^m`, via transport to the `Fin L × Fin m`
   standard form and conjugacy/reindex invariance of the characteristic determinant.
3. `phase_depth_det_identity` — assembles the two sides. -/

namespace Brockian.PhaseDepthDetIdentity

open Equiv Equiv.Perm Matrix Finset

/-! ## Building block 1 — the circulant / block-cyclic determinants (copied verbatim) -/

section BuildingBlocks
variable {R : Type*} [CommRing R]

/-- **The circulant determinant.** `det (1 - z • P) = 1 - z ^ n` for `P = finRotate n`. -/
theorem circulant_det (n : ℕ) (hn : 0 < n) (z : R) :
    Matrix.det (1 - z • (Equiv.toPEquiv (finRotate n)).toMatrix) = 1 - z ^ n := by
  match n, hn with
  | 1, _ =>
      rw [finRotate_one]
      simp [Matrix.det_fin_one, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  | (m + 2), _ =>
      set ρ : Perm (Fin (m + 2)) := (finRotate (m + 2))⁻¹ with hρ
      set M : Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
        1 - z • (Equiv.toPEquiv (finRotate (m + 2))).toMatrix with hMdef
      have hM : ∀ i j, M i j
          = (if i = j then (1 : R) else 0)
            - z * (if finRotate (m + 2) i = j then 1 else 0) := by
        intro i j
        simp only [hMdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff, smul_eq_mul]
      have hfp : ∀ i, finRotate (m + 2) i ≠ i := fun i =>
        Equiv.Perm.mem_support.mp (by rw [support_finRotate]; exact Finset.mem_univ i)
      have hrhofp : ∀ i, ρ i ≠ i := by
        intro i
        have hi : i ∈ ((finRotate (m + 2))⁻¹).support := by
          rw [Equiv.Perm.support_inv, support_finRotate]; exact Finset.mem_univ i
        rw [hρ]; exact Equiv.Perm.mem_support.mp hi
      have hrhocyc : IsCycle ρ := by rw [hρ]; exact isCycle_finRotate.inv
      have hAppInv : ∀ i, finRotate (m + 2) (ρ i) = i := by
        intro i; rw [hρ]; simp
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
      have hdiag : ∀ i, M i i = 1 := by
        intro i
        rw [hM, if_pos rfl, if_neg (hfp i)]; ring
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

/-- **The block-cyclic (standard-form) determinant.** `det (1 - z • P) = (1 - z^L)^m` for
`P` the permutation matrix of `(finRotate L).prodCongr (Equiv.refl (Fin m))`. -/
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

end BuildingBlocks

/-! ## Building block 2 — the transfer/roof permutations and their minimal periods (copied) -/

section Dynamics
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Total holonomy `H = ∑ j, c j`. -/
def Htot (c : ZMod 5 → A) : A := ∑ r : ZMod 5, c r

/-- The transfer permutation `σ_c(j,a) = (j+1, a + c j)` on `S = ZMod 5 × A`. -/
def sigmaMap (c : ZMod 5 → A) (x : ZMod 5 × A) : ZMod 5 × A := (x.1 + 1, x.2 + c x.1)

/-- The fiber roof map `ρ(H)(a) = a + H`. -/
def rhoMap (H : A) : A → A := fun a => a + H

theorem sigma_iterate (c : ZMod 5 → A) (n : ℕ) (x : ZMod 5 × A) :
    (sigmaMap c)^[n] x = (x.1 + n, x.2 + ∑ i ∈ Finset.range n, c (x.1 + i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [sigmaMap, Finset.sum_range_succ]
    refine Prod.ext ?_ ?_
    · push_cast; ring
    · push_cast; abel

theorem sum_shift (c : ZMod 5 → A) (j : ZMod 5) :
    ∑ i ∈ Finset.range 5, c (j + i) = Htot c := by
  have hB : ∑ r : ZMod 5, c (j + r) = ∑ r : ZMod 5, c r :=
    Equiv.sum_comp (Equiv.addLeft j) c
  have hA : ∑ i ∈ Finset.range 5, c (j + (i : ZMod 5)) = ∑ r : ZMod 5, c (j + r) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => c (j + (i : ZMod 5))) 5]
    rfl
  rw [hA, hB]
  rfl

theorem sigma_five (c : ZMod 5 → A) (x : ZMod 5 × A) :
    (sigmaMap c)^[5] x = (x.1, x.2 + Htot c) := by
  rw [sigma_iterate]
  refine Prod.ext ?_ ?_
  · show x.1 + ((5 : ℕ) : ZMod 5) = x.1
    rw [ZMod.natCast_self]; ring
  · show x.2 + ∑ i ∈ Finset.range 5, c (x.1 + i) = x.2 + Htot c
    rw [sum_shift]

theorem sigma_5k (c : ZMod 5 → A) (k : ℕ) :
    ∀ x : ZMod 5 × A, (sigmaMap c)^[5 * k] x = (x.1, x.2 + k • Htot c) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have h1 : 5 * (k + 1) = 5 + 5 * k := by ring
    rw [h1, Function.iterate_add_apply, ih, sigma_five]
    refine Prod.ext rfl ?_
    show (x.2 + k • Htot c) + Htot c = x.2 + (k + 1) • Htot c
    rw [succ_nsmul]; abel

theorem sigma_period (c : ZMod 5 → A) (x : ZMod 5 × A) (m : ℕ) :
    (sigmaMap c)^[m] x = x ↔ 5 * addOrderOf (Htot c) ∣ m := by
  constructor
  · intro h
    have hiter : (x.1 + (m : ZMod 5), x.2 + ∑ i ∈ Finset.range m, c (x.1 + i)) = x := by
      rw [← sigma_iterate]; exact h
    have hfst : x.1 + (m : ZMod 5) = x.1 := congrArg Prod.fst hiter
    have hm5 : (m : ZMod 5) = 0 := by
      have h2 : x.1 + (m : ZMod 5) = x.1 + 0 := by rw [add_zero]; exact hfst
      exact add_left_cancel h2
    have hdvd5 : (5 : ℕ) ∣ m := by
      rwa [CharP.cast_eq_zero_iff (ZMod 5) 5] at hm5
    obtain ⟨k, rfl⟩ := hdvd5
    have hk := sigma_5k c k x
    rw [hk] at h
    have hsnd : x.2 + k • Htot c = x.2 := congrArg Prod.snd h
    have hz : k • Htot c = 0 := by
      have h2 : x.2 + k • Htot c = x.2 + 0 := by rw [add_zero]; exact hsnd
      exact add_left_cancel h2
    have hordk : addOrderOf (Htot c) ∣ k := addOrderOf_dvd_of_nsmul_eq_zero hz
    exact mul_dvd_mul_left 5 hordk
  · intro h
    obtain ⟨t, ht⟩ := h
    have hm : m = 5 * (addOrderOf (Htot c) * t) := by rw [ht]; ring
    rw [hm, sigma_5k]
    refine Prod.ext rfl ?_
    show x.2 + (addOrderOf (Htot c) * t) • Htot c = x.2
    have hz : (addOrderOf (Htot c) * t) • Htot c = 0 := by
      rw [mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero]
    rw [hz, add_zero]

theorem sigma_minimalPeriod (c : ZMod 5 → A) (x : ZMod 5 × A) :
    Function.minimalPeriod (sigmaMap c) x = 5 * addOrderOf (Htot c) := by
  apply Nat.dvd_antisymm
  · rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    show (sigmaMap c)^[5 * addOrderOf (Htot c)] x = x
    rw [sigma_period]
  · have hp : (sigmaMap c)^[Function.minimalPeriod (sigmaMap c) x] x = x :=
      Function.isPeriodicPt_minimalPeriod (sigmaMap c) x
    rwa [sigma_period] at hp

theorem sigma_injective (c : ZMod 5 → A) : Function.Injective (sigmaMap c) := by
  intro x y h
  simp only [sigmaMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hx1 : x.1 = y.1 := add_right_cancel h1
  have hx2 : x.2 = y.2 := by
    rw [hx1] at h2
    exact add_right_cancel h2
  exact Prod.ext hx1 hx2

theorem sigma_bijective (c : ZMod 5 → A) : Function.Bijective (sigmaMap c) :=
  (Finite.injective_iff_bijective).mp (sigma_injective c)

/-- `σ_c` bundled as a permutation of `S`; its permutation matrix is `T_c`. -/
noncomputable def sigmaPerm (c : ZMod 5 → A) : Equiv.Perm (ZMod 5 × A) :=
  Equiv.ofBijective (sigmaMap c) (sigma_bijective c)

theorem rho_iterate (H : A) (m : ℕ) (a : A) : (rhoMap H)^[m] a = a + m • H := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [rhoMap, succ_nsmul]
    abel

theorem rho_period (H : A) (a : A) (m : ℕ) : (rhoMap H)^[m] a = a ↔ addOrderOf H ∣ m := by
  rw [rho_iterate]
  constructor
  · intro h
    have hz : m • H = 0 := by
      have h2 : a + m • H = a + 0 := by rw [add_zero]; exact h
      exact add_left_cancel h2
    exact addOrderOf_dvd_of_nsmul_eq_zero hz
  · intro h
    obtain ⟨t, rfl⟩ := h
    have hz : (addOrderOf H * t) • H = 0 := by
      rw [mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero]
    rw [hz, add_zero]

theorem rho_minimalPeriod (H : A) (a : A) :
    Function.minimalPeriod (rhoMap H) a = addOrderOf H := by
  apply Nat.dvd_antisymm
  · rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    show (rhoMap H)^[addOrderOf H] a = a
    rw [rho_period]
  · have hp : (rhoMap H)^[Function.minimalPeriod (rhoMap H) a] a = a :=
      Function.isPeriodicPt_minimalPeriod (rhoMap H) a
    rwa [rho_period] at hp

/-- The fiber roof map bundled as a permutation `ρ(H) : a ↦ a + H`. -/
def rhoPerm (H : A) : Equiv.Perm A := Equiv.addRight H

theorem rhoPerm_minimalPeriod (H : A) (a : A) :
    Function.minimalPeriod (rhoPerm H) a = addOrderOf H := by
  have hco : (⇑(rhoPerm H) : A → A) = rhoMap H := by
    funext a; simp [rhoPerm, rhoMap]
  rw [hco]; exact rho_minimalPeriod H a

theorem sigmaPerm_minimalPeriod (c : ZMod 5 → A) (x : ZMod 5 × A) :
    Function.minimalPeriod (sigmaPerm c) x = 5 * addOrderOf (Htot c) := by
  have hco : (⇑(sigmaPerm c) : ZMod 5 × A → ZMod 5 × A) = sigmaMap c := by
    funext x; simp [sigmaPerm]
  rw [hco]; exact sigma_minimalPeriod c x

end Dynamics

/-! ## Last mile — Lemma 1: cycleType from a uniform minimal period -/

section Lemma1
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- In a cycle, every support point has minimal period equal to the support cardinality. -/
lemma minimalPeriod_of_isCycle {c : Perm X} (hc : c.IsCycle) {x : X} (hx : x ∈ c.support) :
    Function.minimalPeriod ⇑c x = c.support.card := by
  have hN : orderOf c = c.support.card := hc.orderOf
  apply Nat.dvd_antisymm
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    show (⇑c)^[c.support.card] x = x
    rw [← Equiv.Perm.coe_pow, ← hN, pow_orderOf_eq_one]
    rfl
  · rw [← hN]
    by_contra hcon
    have hsupp : (c ^ (Function.minimalPeriod ⇑c x)).support = c.support :=
      hc.support_pow_eq_iff.2 hcon
    have hxmem : x ∈ (c ^ (Function.minimalPeriod ⇑c x)).support := hsupp ▸ hx
    rw [Equiv.Perm.mem_support] at hxmem
    apply hxmem
    have : (⇑c)^[Function.minimalPeriod ⇑c x] x = x :=
      Function.isPeriodicPt_minimalPeriod ⇑c x
    rwa [← Equiv.Perm.coe_pow] at this

/-- For a disjoint product, the minimal period at a support point of `c` matches that of `c`. -/
lemma minimalPeriod_mul_disjoint {c τ : Perm X} (hd : Disjoint c τ) {x : X}
    (hx : x ∈ c.support) :
    Function.minimalPeriod ⇑(c * τ) x = Function.minimalPeriod ⇑c x := by
  have hτx : τ x = x := (hd x).resolve_left (mem_support.mp hx)
  have hcm : Commute c τ := hd.commute
  have hiter : ∀ k : ℕ, ((c * τ) ^ k) x = (c ^ k) x := by
    intro k
    rw [hcm.mul_pow, Equiv.Perm.mul_apply, pow_apply_eq_self_of_apply_eq_self hτx]
  have hagree : ∀ k : ℕ, (⇑(c * τ))^[k] x = (⇑c)^[k] x := by
    intro k
    rw [← Equiv.Perm.coe_pow, ← Equiv.Perm.coe_pow]
    exact hiter k
  apply Nat.dvd_antisymm
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    show (⇑(c * τ))^[Function.minimalPeriod ⇑c x] x = x
    rw [hagree]
    exact Function.isPeriodicPt_minimalPeriod ⇑c x
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    show (⇑c)^[Function.minimalPeriod ⇑(c * τ) x] x = x
    rw [← hagree]
    exact Function.isPeriodicPt_minimalPeriod ⇑(c * τ) x

/-- **Lemma 1.** Uniform minimal period `L ≥ 2` forces `cycleType = replicate (card/L) L`. -/
theorem cycleType_of_uniform_minimalPeriod (σ : Perm X) (L : ℕ) (hL : 2 ≤ L)
    (h : ∀ x, Function.minimalPeriod ⇑σ x = L) :
    σ.cycleType = Multiset.replicate (Fintype.card X / L) L := by
  have hall : ∀ n ∈ σ.cycleType, n = L := by
    intro n hn
    obtain ⟨c, τ, hσeq, hd, hc, hcard⟩ := mem_cycleType_iff.1 hn
    have hc' := hc
    obtain ⟨x, hxne, -⟩ := hc'
    have hxsupp : x ∈ c.support := mem_support.mpr hxne
    have e1 : Function.minimalPeriod ⇑c x = c.support.card :=
      minimalPeriod_of_isCycle hc hxsupp
    have e2 : Function.minimalPeriod ⇑(c * τ) x = Function.minimalPeriod ⇑c x :=
      minimalPeriod_mul_disjoint hd hxsupp
    have e3 : Function.minimalPeriod ⇑σ x = L := h x
    rw [hσeq] at e3
    rw [e2, e1, hcard] at e3
    exact e3
  have hne : ∀ x, σ x ≠ x := by
    intro x hxfix
    have : Function.minimalPeriod ⇑σ x = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.2 hxfix
    rw [h x] at this
    omega
  have hsupp : σ.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun x => mem_support.mpr (hne x))
  have hsum : σ.cycleType.sum = Fintype.card X := by
    rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ]
  have hrepl : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) L :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum2 : σ.cycleType.sum = Multiset.card σ.cycleType * L := by
    conv_lhs => rw [hrepl]
    rw [Multiset.sum_replicate, smul_eq_mul]
  have hcardX : Fintype.card X = Multiset.card σ.cycleType * L := by
    rw [← hsum, hsum2]
  have hcardeq : Multiset.card σ.cycleType = Fintype.card X / L := by
    rw [hcardX, Nat.mul_div_cancel _ (by omega : 0 < L)]
  rw [hrepl, hcardeq]

end Lemma1

/-! ## Last mile — Lemma 2: the characteristic determinant from the cycle type -/

section Lemma2
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [CommRing R]

/-- `permCongr` is multiplicative. -/
lemma permCongr_mul (e : X ≃ Y) (a b : Perm X) :
    e.permCongr (a * b) = e.permCongr a * e.permCongr b := by
  ext y
  simp [Equiv.Perm.mul_apply, Equiv.permCongr_apply, e.symm_apply_apply]

/-- `permCongr` bundled as a monoid isomorphism, to reuse `map_zpow`. -/
def permCongrHom (e : X ≃ Y) : Perm X ≃* Perm Y where
  toEquiv := e.permCongr
  map_mul' := permCongr_mul e

@[simp] lemma permCongrHom_apply (e : X ≃ Y) (σ : Perm X) :
    permCongrHom e σ = e.permCongr σ := rfl

lemma support_permCongr (e : X ≃ Y) (σ : Perm X) :
    (e.permCongr σ).support = σ.support.map e.toEmbedding := by
  ext y
  simp only [Equiv.Perm.mem_support, Equiv.permCongr_apply, Finset.mem_map,
    Equiv.toEmbedding_apply, ne_eq]
  constructor
  · intro hh
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro hcontra
    exact hh (by rw [hcontra, e.apply_symm_apply])
  · rintro ⟨x, hx, rfl⟩
    rw [e.symm_apply_apply]
    intro hcontra
    exact hx (e.injective hcontra)

lemma card_support_permCongr (e : X ≃ Y) (σ : Perm X) :
    (e.permCongr σ).support.card = σ.support.card := by
  rw [support_permCongr, Finset.card_map]

lemma isCycle_permCongr (e : X ≃ Y) {σ : Perm X} (hσ : σ.IsCycle) :
    (e.permCongr σ).IsCycle := by
  obtain ⟨x, hx, hx2⟩ := hσ
  refine ⟨e x, ?_, ?_⟩
  · simp only [Equiv.permCongr_apply, e.symm_apply_apply]
    exact fun hh => hx (e.injective hh)
  · intro y hy
    have hy' : σ (e.symm y) ≠ e.symm y := by
      intro hh
      apply hy
      simp only [Equiv.permCongr_apply, hh, e.apply_symm_apply]
    obtain ⟨i, hi⟩ := hx2 hy'
    refine ⟨i, ?_⟩
    have hz : permCongrHom e (σ ^ i) = (permCongrHom e σ) ^ i := map_zpow (permCongrHom e) σ i
    have hpow : (e.permCongr σ) ^ i = e.permCongr (σ ^ i) := by
      have := hz.symm; simpa using this
    rw [hpow]
    simp only [Equiv.permCongr_apply, e.symm_apply_apply, hi, e.apply_symm_apply]

lemma disjoint_permCongr (e : X ≃ Y) {c τ : Perm X} (hd : Disjoint c τ) :
    Disjoint (e.permCongr c) (e.permCongr τ) := by
  intro y
  rcases hd (e.symm y) with hh | hh
  · left; simp only [Equiv.permCongr_apply, hh, e.apply_symm_apply]
  · right; simp only [Equiv.permCongr_apply, hh, e.apply_symm_apply]

/-- `cycleType` is invariant under relabeling by a type equivalence. -/
lemma cycleType_permCongr (e : X ≃ Y) (σ : Perm X) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one =>
      rw [show e.permCongr 1 = 1 from map_one (permCongrHom e), cycleType_one, cycleType_one]
  | base_cycles σ hσ =>
      rw [(isCycle_permCongr e hσ).cycleType, hσ.cycleType, card_support_permCongr]
  | induction_disjoint c τ hd hc ihc ihτ =>
      rw [permCongr_mul, (disjoint_permCongr e hd).cycleType_mul, hd.cycleType_mul, ihc, ihτ]

/-- The characteristic determinant `det(1 − z·permMatrix •)` is a conjugacy invariant. -/
lemma det_one_sub_smul_conj (z : R) (g σ : Perm X) :
    (1 - z • (g * σ * g⁻¹).permMatrix R).det = (1 - z • σ.permMatrix R).det := by
  set P := g.permMatrix R with hP
  set Pi := (g⁻¹).permMatrix R with hPi
  have hPiP : Pi * P = 1 := by
    rw [hPi, hP, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  have hpm : (g * σ * g⁻¹).permMatrix R = Pi * σ.permMatrix R * P := by
    rw [Matrix.permMatrix_mul, Matrix.permMatrix_mul, hPi, hP, mul_assoc]
  have hmat : Pi * (1 - z • σ.permMatrix R) * P = 1 - z • (g * σ * g⁻¹).permMatrix R := by
    rw [hpm, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul,
        hPiP]
  rw [← hmat, Matrix.det_mul, Matrix.det_mul]
  have hdet : Pi.det * P.det = 1 := by rw [← Matrix.det_mul, hPiP, Matrix.det_one]
  calc Pi.det * (1 - z • σ.permMatrix R).det * P.det
      = (1 - z • σ.permMatrix R).det * (Pi.det * P.det) := by ring
    _ = (1 - z • σ.permMatrix R).det := by rw [hdet, mul_one]

/-- The characteristic determinant is invariant under relabeling by a type equivalence. -/
lemma det_permCongr_eq (e : X ≃ Y) (σ : Perm X) (z : R) :
    (1 - z • (e.permCongr σ).permMatrix R).det = (1 - z • σ.permMatrix R).det := by
  have hmat : (1 - z • (e.permCongr σ).permMatrix R)
      = (1 - z • σ.permMatrix R).submatrix e.symm e.symm := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.submatrix_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff,
      smul_eq_mul, Equiv.permCongr_apply]
    congr 1
    · by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun hh => hij (e.symm.injective hh))]
    · congr 1
      by_cases hcond : σ (e.symm i) = e.symm j
      · rw [if_pos hcond, if_pos (by rw [hcond, e.apply_symm_apply])]
      · rw [if_neg hcond, if_neg ?_]
        intro hh
        exact hcond (by apply e.injective; rw [hh, e.apply_symm_apply])
  rw [hmat, Matrix.det_submatrix_equiv_self e.symm]

end Lemma2

/-! ## Last mile — the standard-form cycle type and Lemma 2 proper -/

section StandardForm
variable {R : Type*} [CommRing R]

/-- The standard block-cyclic form on `Fin L × Fin m` has `cycleType = replicate m L`. -/
lemma cycleType_standardForm (m L : ℕ) (hL : 2 ≤ L) :
    Equiv.Perm.cycleType ((finRotate L).prodCongr (Equiv.refl (Fin m)))
      = Multiset.replicate m L := by
  have hmp : ∀ x : Fin L × Fin m,
      Function.minimalPeriod ⇑((finRotate L).prodCongr (Equiv.refl (Fin m))) x = L := by
    intro x
    have hcoe : (⇑((finRotate L).prodCongr (Equiv.refl (Fin m))) : Fin L × Fin m → Fin L × Fin m)
        = Prod.map ⇑(finRotate L) id := by
      rw [Equiv.prodCongr_apply]; rfl
    rw [hcoe, Function.minimalPeriod_prodMap]
    have hfin : Function.minimalPeriod ⇑(finRotate L) x.1 = L := by
      obtain ⟨k, rfl⟩ : ∃ k, L = k + 2 := ⟨L - 2, by omega⟩
      have hx1 : x.1 ∈ (finRotate (k + 2)).support := by
        rw [support_finRotate]; exact Finset.mem_univ _
      rw [minimalPeriod_of_isCycle isCycle_finRotate hx1, support_finRotate,
        Finset.card_univ, Fintype.card_fin]
    rw [hfin, Function.minimalPeriod_id, Nat.lcm_one_right]
  have hres := cycleType_of_uniform_minimalPeriod
    ((finRotate L).prodCongr (Equiv.refl (Fin m))) L hL hmp
  rw [hres]
  congr 1
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_div_cancel_left m (by omega)]

/-- **Lemma 2.** `cycleType σ = replicate m L` (`2 ≤ L`, `card X = L·m`) gives the characteristic
determinant `det(1 − z·permMatrix σ) = (1 − z^L)^m`. -/
lemma det_one_sub_smul_eq_of_cycleType {X : Type*} [Fintype X] [DecidableEq X]
    (z : R) (σ : Perm X) (m L : ℕ) (hL : 2 ≤ L) (hcard : Fintype.card X = L * m)
    (hcyc : σ.cycleType = Multiset.replicate m L) :
    (1 - z • σ.permMatrix R).det = (1 - z ^ L) ^ m := by
  have hcardeq : Fintype.card X = Fintype.card (Fin L × Fin m) := by
    rw [hcard, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  let e : X ≃ Fin L × Fin m := Fintype.equivOfCardEq hcardeq
  set g₀ : Perm (Fin L × Fin m) := (finRotate L).prodCongr (Equiv.refl (Fin m)) with hg₀
  have hcc : (e.permCongr σ).cycleType = g₀.cycleType := by
    rw [cycleType_permCongr, hcyc, hg₀, cycleType_standardForm m L hL]
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_cycleType_eq hcc)
  have h1 : (1 - z • σ.permMatrix R).det = (1 - z • (e.permCongr σ).permMatrix R).det :=
    (det_permCongr_eq e σ z).symm
  have hconj : (1 - z • g₀.permMatrix R).det = (1 - z • (e.permCongr σ).permMatrix R).det := by
    rw [← hg]
    exact det_one_sub_smul_conj z g (e.permCongr σ)
  have hblock : (1 - z • g₀.permMatrix R).det = (1 - z ^ L) ^ m :=
    blockCyclic_det m L (by omega) z
  rw [h1, ← hconj, hblock]

end StandardForm

/-! ## The phase-depth determinant identity -/

section Final
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {R : Type*} [CommRing R]

/-- **Phase-depth determinant identity.**
`det(1 − z · T_c) = det(1 − z⁵ · ρ(H))` for the transfer permutation `σ_c` and the fiber
roof `ρ(H)`, over any commutative ring `R`. -/
theorem phase_depth_det_identity (c : ZMod 5 → A) (z : R) :
    (1 - z • (sigmaPerm c).permMatrix R).det
      = (1 - z ^ 5 • (rhoPerm (Htot c)).permMatrix R).det := by
  set H := Htot c with hH
  set ordH := addOrderOf H with hord
  have hordpos : 0 < ordH := by
    rw [hord]; exact (isOfFinAddOrder_of_finite H).addOrderOf_pos
  have hdvd : ordH ∣ Fintype.card A := by rw [hord]; exact addOrderOf_dvd_card
  -- card of the total state space
  have hcardS : Fintype.card (ZMod 5 × A) = 5 * Fintype.card A := by
    rw [Fintype.card_prod, ZMod.card 5]
  -- LHS via Lemma 2
  have hLcyc : (sigmaPerm c).cycleType
      = Multiset.replicate (Fintype.card (ZMod 5 × A) / (5 * ordH)) (5 * ordH) := by
    apply cycleType_of_uniform_minimalPeriod _ (5 * ordH) (by omega)
    intro x; rw [hord, hH]; exact sigmaPerm_minimalPeriod c x
  have hdvdS : (5 * ordH) ∣ Fintype.card (ZMod 5 × A) := by
    rw [hcardS]; exact Nat.mul_dvd_mul_left 5 hdvd
  have hLcard : Fintype.card (ZMod 5 × A)
      = (5 * ordH) * (Fintype.card (ZMod 5 × A) / (5 * ordH)) :=
    (Nat.mul_div_cancel' hdvdS).symm
  have hLHS : (1 - z • (sigmaPerm c).permMatrix R).det
      = (1 - z ^ (5 * ordH)) ^ (Fintype.card A / ordH) := by
    have hm : Fintype.card (ZMod 5 × A) / (5 * ordH) = Fintype.card A / ordH := by
      rw [hcardS, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 5)]
    have := det_one_sub_smul_eq_of_cycleType z (sigmaPerm c)
      (Fintype.card (ZMod 5 × A) / (5 * ordH)) (5 * ordH) (by omega) hLcard (by rw [hLcyc])
    rw [this, hm]
  rw [hLHS]
  -- RHS: split on whether ord H ≥ 2 or ord H = 1 (H = 0)
  rcases Nat.lt_or_ge ordH 2 with hlt | hge
  · -- ordH = 1, i.e. H = 0 : ρ(H) is the identity
    have hord1 : ordH = 1 := by omega
    have hH0 : H = 0 := by
      have : addOrderOf H = 1 := by rw [← hord]; exact hord1
      exact AddMonoid.addOrderOf_eq_one_iff.mp this
    have hrho1 : (rhoPerm H).permMatrix R = 1 := by
      have : rhoPerm H = 1 := by
        rw [hH0]; ext a; simp [rhoPerm]
      rw [this, Matrix.permMatrix_one]
    have hRHS : (1 - z ^ 5 • (rhoPerm H).permMatrix R).det = (1 - z ^ 5) ^ Fintype.card A := by
      rw [hrho1]
      have hsmul : (1 : Matrix A A R) - z ^ 5 • (1 : Matrix A A R)
          = (1 - z ^ 5) • (1 : Matrix A A R) := by
        rw [sub_smul, one_smul]
      rw [hsmul, Matrix.det_smul, Matrix.det_one, mul_one]
    rw [hRHS, hord1]
    simp
  · -- ordH ≥ 2 : ρ(H) has no fixed points, Lemma 2 applies with L = ordH, z ↦ z⁵
    have hRcyc : (rhoPerm H).cycleType
        = Multiset.replicate (Fintype.card A / ordH) ordH := by
      apply cycleType_of_uniform_minimalPeriod _ ordH hge
      intro a; rw [hord]; exact rhoPerm_minimalPeriod H a
    have hRcard : Fintype.card A = ordH * (Fintype.card A / ordH) :=
      (Nat.mul_div_cancel' hdvd).symm
    have hRHS : (1 - z ^ 5 • (rhoPerm H).permMatrix R).det
        = (1 - z ^ (5 * ordH)) ^ (Fintype.card A / ordH) := by
      have := det_one_sub_smul_eq_of_cycleType (z ^ 5) (rhoPerm H)
        (Fintype.card A / ordH) ordH hge hRcard (by rw [hRcyc])
      rw [this, ← pow_mul]
    rw [hRHS]

end Final

end Brockian.PhaseDepthDetIdentity
