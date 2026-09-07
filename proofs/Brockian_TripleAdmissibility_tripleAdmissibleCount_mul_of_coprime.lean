import Mathlib

namespace Brockian.TripleAdmissibility

def TripleAdmissible (M : ℕ) (a : ZMod M) : Prop :=
  IsUnit (a * (a + 2)) ∧ IsUnit ((a + 3) * (a + 5)) ∧
    IsUnit ((a + 6) * (a + 8))

noncomputable def tripleAdmissibleCount (M : ℕ) : ℕ :=
  Nat.card {a : ZMod M // TripleAdmissible M a}

/-- Triple admissibility is componentwise under the Chinese remainder map. -/
theorem tripleAdmissible_chineseRemainder_iff (m n : ℕ) (h : m.Coprime n)
    (a : ZMod (m * n)) :
    TripleAdmissible (m * n) a ↔
      TripleAdmissible m ((ZMod.chineseRemainder h a).1) ∧
      TripleAdmissible n ((ZMod.chineseRemainder h a).2) := by
  set cred := ZMod.chineseRemainder h with hcred
  -- cred is a ring isomorphism, so IsUnit is preserved
  have hunit : ∀ x : ZMod (m * n), IsUnit x ↔ IsUnit (cred x) := by
    intro x
    constructor
    · exact IsUnit.map (f := cred.toRingHom)
    · intro hx
      have heq : x = cred.symm (cred x) := by simp
      rw [heq]
      exact IsUnit.map (f := cred.symm.toRingHom) hx
  have hprod : ∀ p : ZMod m × ZMod n, IsUnit p ↔ IsUnit p.1 ∧ IsUnit p.2 := by
    intro p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨IsUnit.map (RingHom.fst (ZMod m) (ZMod n)) ⟨u, rfl⟩,
             IsUnit.map (RingHom.snd (ZMod m) (ZMod n)) ⟨u, rfl⟩⟩
    · rintro ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩
      use ⟨(u₁, u₂), (u₁⁻¹, u₂⁻¹), by simp, by simp⟩
      simp [hu₁, hu₂]
  -- cred is a ring hom, so it preserves addition
  have hadd : ∀ (x : ZMod (m * n)) (k : ZMod (m * n)), cred (x + k) = cred x + cred k :=
    fun x k => RingEquiv.map_add cred x k
  -- cred maps natural numbers to the same number in both components
  have hconst : ∀ k : ℕ, (cred (k : ZMod (m * n))).1 = (k : ZMod m) ∧ (cred (k : ZMod (m * n))).2 = (k : ZMod n) := by
    intro k
    simp [cred]
  -- Now show the key lemma for addition with small constants
  have ha2 : cred (a + 2) = (⟨(cred a).1 + 2, (cred a).2 + 2⟩ : ZMod m × ZMod n) := by
    rw [hadd]
    have hc2 : cred 2 = ((2 : ZMod m), (2 : ZMod n)) := by
      have := hconst 2
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc2]
    rfl
  -- Helper for other constants
  have ha3 : cred (a + 3) = ((cred a).1 + 3, (cred a).2 + 3) := by
    rw [hadd]
    have hc3 : cred (3 : ZMod (m * n)) = ((3 : ZMod m), (3 : ZMod n)) := by
      have := hconst 3
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc3]; rfl
  have ha5 : cred (a + 5) = ((cred a).1 + 5, (cred a).2 + 5) := by
    rw [hadd]
    have hc5 : cred (5 : ZMod (m * n)) = ((5 : ZMod m), (5 : ZMod n)) := by
      have := hconst 5
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc5]; rfl
  have ha6 : cred (a + 6) = ((cred a).1 + 6, (cred a).2 + 6) := by
    rw [hadd]
    have hc6 : cred (6 : ZMod (m * n)) = ((6 : ZMod m), (6 : ZMod n)) := by
      have := hconst 6
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc6]; rfl
  have ha8 : cred (a + 8) = ((cred a).1 + 8, (cred a).2 + 8) := by
    rw [hadd]
    have hc8 : cred (8 : ZMod (m * n)) = ((8 : ZMod m), (8 : ZMod n)) := by
      have := hconst 8
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc8]; rfl
  -- Now prove the main statement
  unfold TripleAdmissible
  -- Prove for a * (a + 2)
  have hua : IsUnit (a * (a + 2)) ↔
    IsUnit ((cred a).1 * ((cred a).1 + 2)) ∧ IsUnit ((cred a).2 * ((cred a).2 + 2)) := by
    have heq : cred (a * (a + 2)) = ((cred a).1 * ((cred a).1 + 2), (cred a).2 * ((cred a).2 + 2)) := by
      calc cred (a * (a + 2))
          = cred a * cred (a + 2) := RingEquiv.map_mul cred _ _
        _ = cred a * ((cred a).1 + 2, (cred a).2 + 2) := by rw [ha2]
        _ = ((cred a).1 * ((cred a).1 + 2), (cred a).2 * ((cred a).2 + 2)) := by rfl
    rw [hunit, heq, hprod]
  -- Prove for (a + 3) * (a + 5)
  have hub : IsUnit ((a + 3) * (a + 5)) ↔
    IsUnit (((cred a).1 + 3) * ((cred a).1 + 5)) ∧ IsUnit (((cred a).2 + 3) * ((cred a).2 + 5)) := by
    have heq : cred ((a + 3) * (a + 5)) = (((cred a).1 + 3) * ((cred a).1 + 5), ((cred a).2 + 3) * ((cred a).2 + 5)) := by
      calc cred ((a + 3) * (a + 5))
          = cred (a + 3) * cred (a + 5) := RingEquiv.map_mul cred _ _
        _ = ((cred a).1 + 3, (cred a).2 + 3) * ((cred a).1 + 5, (cred a).2 + 5) := by rw [ha3, ha5]
        _ = (((cred a).1 + 3) * ((cred a).1 + 5), ((cred a).2 + 3) * ((cred a).2 + 5)) := by simp
    rw [hunit, heq, hprod]
  -- Prove for (a + 6) * (a + 8)
  have huc : IsUnit ((a + 6) * (a + 8)) ↔
    IsUnit (((cred a).1 + 6) * ((cred a).1 + 8)) ∧ IsUnit (((cred a).2 + 6) * ((cred a).2 + 8)) := by
    have heq : cred ((a + 6) * (a + 8)) = (((cred a).1 + 6) * ((cred a).1 + 8), ((cred a).2 + 6) * ((cred a).2 + 8)) := by
      calc cred ((a + 6) * (a + 8))
          = cred (a + 6) * cred (a + 8) := RingEquiv.map_mul cred _ _
        _ = ((cred a).1 + 6, (cred a).2 + 6) * ((cred a).1 + 8, (cred a).2 + 8) := by rw [ha6, ha8]
        _ = (((cred a).1 + 6) * ((cred a).1 + 8), ((cred a).2 + 6) * ((cred a).2 + 8)) := by rfl
    rw [hunit, heq, hprod]
  rw [hua, hub, huc]
  -- LHS: (A ∧ B) ∧ (C ∧ D) ∧ (E ∧ F)
  -- RHS: (A ∧ C ∧ E) ∧ B ∧ D ∧ F
  tauto

/-- Chinese remaindering makes the triple count multiplicative. -/
theorem tripleAdmissibleCount_mul_of_coprime (m n : ℕ) (h : m.Coprime n) :
    tripleAdmissibleCount (m * n) =
      tripleAdmissibleCount m * tripleAdmissibleCount n := by
  unfold tripleAdmissibleCount
  -- Build equivalence using Chinese Remainder Theorem
  let cred := ZMod.chineseRemainder h
  have equiv : {a : ZMod (m * n) // TripleAdmissible (m * n) a} ≃
      {a : ZMod m // TripleAdmissible m a} × {b : ZMod n // TripleAdmissible n b} := by
    refine Equiv.mk ?toFun ?fromFun ?left_inv ?right_inv
    case toFun =>
      intro x
      have hx := tripleAdmissible_chineseRemainder_iff m n h x.1 |>.mp x.2
      exact Prod.mk (⟨(cred x.1).1, hx.1⟩ : {a : ZMod m // TripleAdmissible m a})
                    (⟨(cred x.1).2, hx.2⟩ : {b : ZMod n // TripleAdmissible n b})
    case fromFun =>
      intro p
      have hx : TripleAdmissible m p.1.1 := p.1.2
      have hy : TripleAdmissible n p.2.1 := p.2.2
      have hcred : cred (cred.symm (p.1.1, p.2.1)) = (p.1.1, p.2.1) := RingEquiv.apply_symm_apply cred (p.1.1, p.2.1)
      refine ⟨cred.symm (p.1.1, p.2.1), by
        rw [tripleAdmissible_chineseRemainder_iff m n h]
        rw [hcred]
        exact ⟨hx, hy⟩⟩
    case left_inv =>
      intro x
      have hcred : cred.symm (cred x.1) = x.1 := RingEquiv.symm_apply_apply cred x.1
      apply Subtype.ext
      simp only
      exact hcred
    case right_inv =>
      intro p
      have hcred : cred (cred.symm (p.1.1, p.2.1)) = (p.1.1, p.2.1) := RingEquiv.apply_symm_apply cred (p.1.1, p.2.1)
      congr 1 <;> simp [hcred]
  rw [Nat.card_congr equiv, Nat.card_prod]


end Brockian.TripleAdmissibility
