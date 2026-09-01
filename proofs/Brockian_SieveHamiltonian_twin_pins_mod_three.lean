/-
  Brockian/SieveHamiltonian.lean — THE SIEVE HAMILTONIAN CAMPAIGN
  (July 30, after the "invent the dynamics" program note).

  The object: on the arithmetic wheel Z/M (M odd squarefree), the twin
  sieve deletes residues a with a ≡ 0 or a ≡ −2 mod some ℓ ∣ M. Once
  3 ∣ M the admissible set is pinned to the coset a ≡ 2 (mod 3); the
  residual translation flow is +3 on that coset. The compressed
  Hamiltonian (Dirichlet deletion of forbidden sites from the residual
  cycle) decomposes into path Laplacians over the admissible RUNS, so
  its spectrum is exact and finite. Everything below is finite; no
  Hilbert–Pólya claim is made anywhere in this file — the operator
  limit M → ∞ is an OPEN PROGRAM subject to the G0–G6 gate ladder.

  Charter as Core.lean. The declarations below are the formal campaign targets.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.SieveHamiltonian

open Matrix

/-! ## 1. The no-go theorem: why the naive adjacency dies at 3 -/

/-- Twin admissibility pins the mod-3 residue. -/
theorem twin_pins_mod_three (a : ZMod 3) :
    (a ≠ 0 ∧ a + 2 ≠ 0) ↔ a = 2 := by
  fin_cases a <;> simp_all [ZMod]

/-- NO-GO (target): two twin-admissible integers are never at distance
1 or 2; the +1 and +2 adjacencies on any wheel containing 3 carry no
admissible edges, so their Dirichlet compressions trivialize to 2·I.
The residual flow is +3 on the surviving coset. -/
theorem no_adjacent_admissible (a b : ℤ)
    (ha : (a : ZMod 3) = 2) (hb : (b : ZMod 3) = 2)
    (h : b - a = 1 ∨ b - a = 2) : False := by
  obtain h | h := h
  · have h' : ((b - a : ℤ) : ZMod 3) = 1 := by rw [h]; norm_cast
    simp [ha, hb] at h'
  · have h' : ((b - a : ℤ) : ZMod 3) = 2 := by rw [h]; norm_cast
    simp [ha, hb] at h'
    contradiction

/-! ## 2. The run-cap and signature theorems (the mod-5 rigidity) -/

/-- RUN CAP (target, decidable): no four consecutive states of the +3
flow are all admissible mod 5 — four steps of +3 visit four distinct
mod-5 classes, but only three classes {1,2,4} are admissible. Hence
every admissible run has length ≤ 3, at every wheel level. -/
theorem run_cap :
    ¬ ∃ a : ZMod 5, ({a, a + 3, a + 6, a + 9} : Finset (ZMod 5)) ⊆
      ({1, 2, 4} : Finset (ZMod 5)) := by decide

/-- SIGNATURE (target, decidable): a maximal run of length 3 exists only
with mod-5 signature (1, 4, 2) — every ground-state triple rides the
three roads. -/
theorem run3_signature (a : ZMod 5)
    (h : ({a, a + 3, a + 6} : Finset (ZMod 5)) ⊆
      ({1, 2, 4} : Finset (ZMod 5))) : a = 1 := by
  fin_cases a <;> simp_all (config := {decide := true})

/-! ## 3. The path spectra: exact eigensystem of the length-3 block -/

/-- The Dirichlet path Laplacian on three sites. -/
def H3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, -1, 0; -1, 2, -1; 0, -1, 2]

noncomputable def silverGap : ℝ := 2 - Real.sqrt 2

/-- SILVER-GAP EIGENVECTOR (target): (1, √2, 1) is an eigenvector of H3
with eigenvalue 2 − √2. -/
theorem H3_ground :
    H3.mulVec ![1, Real.sqrt 2, 1] = silverGap • ![1, Real.sqrt 2, 1] := by
  ext i
  fin_cases i <;> simp [H3, silverGap, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring_nf
  all_goals rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]; ring_nf

/-- Middle mode (target): (1, 0, −1) with eigenvalue 2. -/
theorem H3_middle :
    H3.mulVec ![1, 0, -1] = (2 : ℝ) • ![1, 0, -1] := by
  ext i
  fin_cases i <;> simp [H3, Matrix.mulVec]

/-- Top mode (target): (1, −√2, 1) with eigenvalue 2 + √2. -/
theorem H3_top :
    H3.mulVec ![1, -Real.sqrt 2, 1] =
      (2 + Real.sqrt 2) • ![1, -Real.sqrt 2, 1] := by
  ext i
  fin_cases i <;> simp [H3, Matrix.mulVec] <;> ring_nf
  all_goals norm_num [Real.sq_sqrt]; ring

/-- Consistency checks (targets): trace 6 and determinant 4. -/
theorem H3_trace : H3.trace = 6 := by
  simp [H3, Matrix.trace, Fin.sum_univ_three]
  norm_num
theorem H3_det : H3.det = 4 := by
  simp [H3, Matrix.det_fin_three]
  norm_num

/-! ## 4. Silver Gap Rigidity — the composite statement.

With run_cap and the path decomposition, the compressed sieve
Hamiltonian at every wheel level (with 3, 5 ∣ M) has spectrum contained
in {2−√2, 1, 2, 3, 2+√2} — five lines forever — and spectral gap
exactly 2−√2 whenever a (1,4,2)-triple exists. The decomposition
itself (deleting vertices from a cycle yields a direct sum of Dirichlet
paths) is the remaining formalization obligation; it is named here and
NOT asserted. -/
def SilverGapRigidityTarget : Prop :=
  ∀ g : ℕ, g ≤ 3 → ∀ j : ℕ, 1 ≤ j → j ≤ g →
    (2 - 2 * Real.cos (Real.pi * j / (g + 1))) ∈
      ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set ℝ)

theorem silver_gap_rigidity_finite : SilverGapRigidityTarget := by
  intro g hg j hj1 hjg
  have h2_3 : Real.pi * 2 / 3 = Real.pi - Real.pi / 3 := by ring
  have h3_4 : Real.pi * 3 / 4 = Real.pi - Real.pi / 4 := by ring
  have h2_4 : Real.pi * 2 / 4 = Real.pi / 2 := by ring
  interval_cases g <;> interval_cases j <;>
    norm_num [Real.cos_pi_div_two, Real.cos_pi_div_three, Real.cos_pi_div_four,
      h2_3, h3_4, h2_4, Real.cos_pi_sub]
  · exact Or.inl (by ring_nf)
  · exact Or.inr (Or.inr (Or.inr (by ring_nf)))

/-! ## 5. The triple-count law (CRT product, Hardy–Littlewood-flavored,
purely finite). A (1,4,2)-triple at wheel level M is a residue a mod M
with a, a+3, a+6 all twin-admissible. The six constraints mod ℓ
(a ≢ 0,−2,−3,−5,−6,−8) are distinct classes for every prime ℓ ≥ 7,
giving ℓ − 6 free choices; for ℓ = 3 and ℓ = 5 the counts are 1.
Empirically verified at levels 105, 1155, 15015, 255255, 4849845:
counts 1, 5, 35, 385, 5005 = ∏_{7 ≤ ℓ ∣ M} (ℓ − 6). -/

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
      apply Prod.ext <;> apply Subtype.ext <;> simp [hcred]
  rw [Nat.card_congr equiv, Nat.card_prod]

/-- The local count at an odd prime: one choice at 3 and 5, and six
forbidden residue classes at every prime at least 7. -/
theorem tripleAdmissibleCount_prime (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    tripleAdmissibleCount p =
      if p = 3 ∨ p = 5 then 1 else p - 6 := by
  by_cases hp3 : p = 3
  · subst hp3; simp [tripleAdmissibleCount]
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · -- Subsingleton: any admissible a = 2
      suffices h : ∀ a : ZMod 3, TripleAdmissible 3 a → a = 2 from
        ⟨fun x y => Subtype.ext (h x.1 x.2 ▸ h y.1 y.2 ▸ rfl)⟩
      intro a ha
      fin_cases a <;> simp [TripleAdmissible] at ha <;> trivial
    · -- Nonempty: TripleAdmissible 3 2
      refine ⟨2, ?_⟩
      simp [TripleAdmissible]
      decide
  · by_cases hp5 : p = 5
    · subst hp5; simp [tripleAdmissibleCount]
      rw [Nat.card_eq_one_iff_unique]
      constructor
      · -- Subsingleton: any admissible a = 1
        suffices h : ∀ a : ZMod 5, TripleAdmissible 5 a → a = 1 from
          ⟨fun x y => Subtype.ext (h x.1 x.2 ▸ h y.1 y.2 ▸ rfl)⟩
        intro a ha
        fin_cases a <;> simp [TripleAdmissible] at ha <;> trivial
      · -- Nonempty: TripleAdmissible 5 1
        refine ⟨1, ?_⟩
        simp [TripleAdmissible]
        decide
    · -- p ≥ 7 case: count = p - 6
      simp [tripleAdmissibleCount]
      -- First establish p ≥ 7
      have hp7 : 7 ≤ p := by
        by_contra h
        push_neg at h
        interval_cases p <;> simp_all (config := {decide := true})
      -- In ZMod p (a field), IsUnit x ↔ x ≠ 0
      -- TripleAdmissible means a ∉ {0, -2, -3, -5, -6, -8}
      -- Use that ZMod p is a field, so IsUnit x ↔ x ≠ 0
      -- Note: Nat.card for finite types works without explicit Fintype
      -- Define the forbidden set
      let F : Finset (ZMod p) := {0, (-2 : ZMod p), (-3 : ZMod p), (-5 : ZMod p), (-6 : ZMod p), (-8 : ZMod p)}
      -- Show F has 6 elements
      have hFcard : F.card = 6 := by
        by_cases hp7' : p = 7
        · subst hp7'; decide
        · -- p ≥ 11 (can't be 8, 9, 10 since p is prime)
          have hp11 : 11 ≤ p := by
            by_contra h
            push_neg at h
            interval_cases p <;> norm_num [hp] at *
          haveI : NeZero p := ⟨by omega⟩
          -- For p ≥ 11, all elements are distinct since differences are < p
          have h2_ne_zero : (2 : ZMod p) ≠ 0 := by
            have hlt : (2 : ℕ) < p := by omega
            have h1 : ZMod.val ((2 : ℕ) : ZMod p) = 2 := ZMod.val_cast_of_lt hlt
            exact fun h => by simp [h] at h1
          have h0 : (0 : ZMod p) ≠ -2 := by simp [h2_ne_zero]
          have h1 : (0 : ZMod p) ≠ -3 := by
            intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
            have hlt : (3 : ℕ) < p := by omega
            have h2 : ZMod.val ((3 : ℕ) : ZMod p) = 3 := ZMod.val_cast_of_lt hlt
            simp [h3] at h2
          have h2 : (0 : ZMod p) ≠ -5 := by
            intro h; have h5 : (5 : ZMod p) = 0 := by linear_combination h
            have hlt : (5 : ℕ) < p := by omega
            have h2 : ZMod.val ((5 : ℕ) : ZMod p) = 5 := ZMod.val_cast_of_lt hlt
            simp [h5] at h2
          have h3 : (0 : ZMod p) ≠ -6 := by
            intro h; have h6 : (6 : ZMod p) = 0 := by linear_combination h
            have hlt : (6 : ℕ) < p := by omega
            have h2 : ZMod.val ((6 : ℕ) : ZMod p) = 6 := ZMod.val_cast_of_lt hlt
            simp [h6] at h2
          have h4 : (0 : ZMod p) ≠ -8 := by
            intro h; have h8 : (8 : ZMod p) = 0 := by linear_combination h
            have hlt : (8 : ℕ) < p := by omega
            have h2 : ZMod.val ((8 : ℕ) : ZMod p) = 8 := ZMod.val_cast_of_lt hlt
            simp [h8] at h2
          have h1_ne_zero : (1 : ZMod p) ≠ 0 := by
            have hlt : (1 : ℕ) < p := by omega
            have h1 : ZMod.val ((1 : ℕ) : ZMod p) = 1 := ZMod.val_cast_of_lt hlt
            intro heq; simp [heq] at h1
          have h5 : (-2 : ZMod p) ≠ -3 := by
            intro h; have h1 : (1 : ZMod p) = 0 := by linear_combination h
            exact h1_ne_zero h1
          have h3_ne_zero : (3 : ZMod p) ≠ 0 := by
            have hlt : (3 : ℕ) < p := by omega
            have h1 : ZMod.val ((3 : ℕ) : ZMod p) = 3 := ZMod.val_cast_of_lt hlt
            intro heq; simp [heq] at h1
          have h6 : (-2 : ZMod p) ≠ -5 := by
            intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
            exact h3_ne_zero h3
          have h7 : (-2 : ZMod p) ≠ -6 := by
            intro h; have h4 : (4 : ZMod p) = 0 := by linear_combination h
            have hlt : (4 : ℕ) < p := by omega
            have h2 : ZMod.val ((4 : ℕ) : ZMod p) = 4 := ZMod.val_cast_of_lt hlt
            simp [h4] at h2
          have h8 : (-2 : ZMod p) ≠ -8 := by
            intro h; have h6 : (6 : ZMod p) = 0 := by linear_combination h
            have hlt : (6 : ℕ) < p := by omega
            have h2 : ZMod.val ((6 : ℕ) : ZMod p) = 6 := ZMod.val_cast_of_lt hlt
            simp [h6] at h2
          -- Compute F.card = 6
          have hFcard' : F.card = 6 := by
            have h9 : (-3 : ZMod p) ≠ -5 := by
              intro h; have h2 : (2 : ZMod p) = 0 := by linear_combination h
              exact h2_ne_zero h2
            have h10 : (-3 : ZMod p) ≠ -6 := by
              intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
              exact h3_ne_zero h3
            have h11 : (-3 : ZMod p) ≠ -8 := by
              intro h; have h5 : (5 : ZMod p) = 0 := by linear_combination h
              have hlt : (5 : ℕ) < p := by omega
              have h2 : ZMod.val ((5 : ℕ) : ZMod p) = 5 := ZMod.val_cast_of_lt hlt
              simp [h5] at h2
            have h12 : (-5 : ZMod p) ≠ -6 := by
              intro h; have h1 : (1 : ZMod p) = 0 := by linear_combination h
              exact h1_ne_zero h1
            have h13 : (-5 : ZMod p) ≠ -8 := by
              intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
              exact h3_ne_zero h3
            have h14 : (-6 : ZMod p) ≠ -8 := by
              intro h; have h2 : (2 : ZMod p) = 0 := by linear_combination h
              exact h2_ne_zero h2
            have nodup : List.Nodup [0, (-2 : ZMod p), (-3 : ZMod p), (-5 : ZMod p), (-6 : ZMod p), (-8 : ZMod p)] := by
              simp [List.Nodup, List.mem_cons, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
            have : F = [0, (-2 : ZMod p), (-3 : ZMod p), (-5 : ZMod p), (-6 : ZMod p), (-8 : ZMod p)].toFinset := by simp [F]
            rw [this, List.toFinset_card_of_nodup nodup]; rfl
          exact hFcard'
      simp only [hp3, hp5, or_self, ↓reduceIte]
      -- TripleAdmissible p a ↔ a ∉ F
      have h_equiv : ∀ a : ZMod p, TripleAdmissible p a ↔ a ∉ F := by
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        intro a
        simp [TripleAdmissible, F]
        simp (config := {decide := true}) [add_eq_zero_iff_eq_neg]; tauto
      -- Use equivalence to rewrite cardinality
      have hcard : Nat.card { a : ZMod p // TripleAdmissible p a } = Nat.card { a : ZMod p // a ∉ F } := by
        exact Nat.card_congr (Equiv.subtypeEquivRight h_equiv)
      rw [hcard]
      -- Nat.card of complement = p - F.card = p - 6
      haveI : NeZero p := ⟨by omega⟩
      haveI : Fintype (ZMod p) := ZMod.fintype p
      rw [Nat.card_eq_fintype_card]
      have hsub : F ⊆ Finset.univ := Finset.subset_univ F
      calc Fintype.card { a : ZMod p // a ∉ F }
          = (Finset.univ \ F).card := by
              rw [Fintype.card_subtype]
              congr 1; ext x; simp [Finset.mem_sdiff, Finset.mem_univ]
        _ = Finset.card (Finset.univ : Finset (ZMod p)) - F.card := by
              rw [Finset.card_sdiff]; simp
        _ = p - 6 := by simp [ZMod.card, hFcard]

/-- Product formula for an arbitrary odd squarefree wheel. -/
theorem tripleAdmissibleCount_squarefree (M : ℕ)
    (hM : Squarefree M) (hodd : Odd M) :
    tripleAdmissibleCount M =
      ∏ p ∈ M.primeFactors,
        (if p = 3 ∨ p = 5 then 1 else p - 6) := by
  have h : ∀ n : ℕ, Squarefree n → Odd n →
    tripleAdmissibleCount n = ∏ p ∈ n.primeFactors, (if p = 3 ∨ p = 5 then 1 else p - 6) := by
    intro n hn_sq hn_odd
    exact Nat.strong_induction_on n (fun m ih hm_sq hm_odd => by
      by_cases hm1 : m = 1
      · subst hm1
        simp [tripleAdmissibleCount]
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨?_, ?_⟩
        · infer_instance
        · refine ⟨0, ?_⟩
          simp [TripleAdmissible]
          trivial
      · -- m > 1, so m has at least one prime factor
        have hm_gt1 : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨fun h => by simp [h] at hm_sq, hm1⟩
        have hp : m.minFac.Prime := Nat.minFac_prime hm_gt1.ne'
        have hpdvd : m.minFac ∣ m := Nat.minFac_dvd m
        -- Set p = m.minFac and q = m / p
        set p := m.minFac with hp_def
        set q := m / p with hq_def
        have hmp : m = p * q := (Nat.mul_div_cancel' hpdvd).symm
        have hq_lt : q < m := Nat.div_lt_self (by omega) hp.one_lt
        have hq_sq : Squarefree q := hm_sq.squarefree_of_dvd (Nat.div_dvd_of_dvd hpdvd)
        have hq_odd : Odd q := hm_odd.of_dvd_nat (Nat.div_dvd_of_dvd hpdvd)
        -- p and q are coprime since m is squarefree
        have hp_coprime_q : Nat.Coprime p q := by
          rw [hp.coprime_iff_not_dvd]
          intro hdvd
          have : p ^ 2 ∣ m := by
            calc p ^ 2 = p * p := by ring
              _ ∣ p * q := Nat.mul_dvd_mul_left p hdvd
              _ = m := hmp.symm
          have hnsq : ¬ Squarefree (p ^ 2) := by
            intro hsq
            rw [Squarefree] at hsq
            specialize hsq p
            simp [pow_two] at hsq
            exact hp.ne_one hsq
          exact absurd (hm_sq.squarefree_of_dvd this) hnsq
        -- Rewrite m = p * q
        rw [hmp]
        -- Use multiplicativity
        rw [tripleAdmissibleCount_mul_of_coprime p q hp_coprime_q]
        -- p is odd since m is odd
        have hp_odd : Odd p := hm_odd.of_dvd_nat hpdvd
        -- Use the prime case for p
        rw [tripleAdmissibleCount_prime p hp hp_odd]
        -- Use induction hypothesis for q
        rw [ih q hq_lt hq_sq hq_odd]
        -- p ∉ q.primeFactors since p and q are coprime
        have hp_not_in_q : p ∉ q.primeFactors := by
          intro h
          have hdiv : p ∣ q := Nat.mem_primeFactors.mp h |>.2.1
          rw [Nat.Coprime] at hp_coprime_q
          have := Nat.dvd_gcd (dvd_refl p) hdiv
          simp [hp_coprime_q] at this
          exact hp.ne_one this
        have hq_ne_zero : q ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hp.pos)
        rw [Nat.primeFactors_mul hp.ne_zero hq_ne_zero]
        rw [hp.primeFactors]
        rw [Finset.prod_union (Finset.disjoint_singleton_left.mpr hp_not_in_q)]
        simp) hn_sq hn_odd
  exact h M hM hodd

theorem triple_count (M : ℕ) (hM : Squarefree M) (h3 : 3 ∣ M) (h5 : 5 ∣ M)
    (hodd : Odd M) :
    Nat.card {a : ZMod M //
        IsUnit (a * (a + 2)) ∧ IsUnit ((a + 3) * (a + 5)) ∧
        IsUnit ((a + 6) * (a + 8))} =
      ∏ ℓ ∈ M.primeFactors.filter (7 ≤ ·), (ℓ - 6) := by
  have eq1 := tripleAdmissibleCount_squarefree M hM hodd
  unfold tripleAdmissibleCount at eq1
  simp only [TripleAdmissible] at eq1
  rw [eq1]
  -- The RHS uses filter, let's rewrite to match
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hne2 : p ≠ 2 := by
    intro h
    rw [h] at hp
    have hdvd : 2 ∣ M := Nat.dvd_of_mem_primeFactors hp
    exact Nat.not_even_iff_odd.mpr hodd (Nat.even_iff.mpr (by omega : M % 2 = 0))
  split_ifs
  · -- p = 3 ∨ p = 5, 7 ≤ p → contradiction
    exfalso; clear eq1 h3 h5 hodd hM hp hprime hne2; omega
  · -- p = 3 ∨ p = 5, ¬7 ≤ p → 1 = 1
    rfl
  · -- ¬(p = 3 ∨ p = 5), 7 ≤ p → p - 6 = p - 6
    rfl
  · -- ¬(p = 3 ∨ p = 5), ¬7 ≤ p → contradiction
    exfalso
    clear eq1 h3 h5 hodd hM hp
    have hp2 : p ≥ 2 := hprime.two_le
    have hp3 : p ≠ 3 := fun h => ‹¬(p = 3 ∨ p = 5)› (Or.inl h)
    have hp5 : p ≠ 5 := fun h => ‹¬(p = 3 ∨ p = 5)› (Or.inr h)
    have hp7 : p < 7 := not_le.mp ‹_›
    interval_cases p <;> simp_all (config := {decide := true})

end Brockian.SieveHamiltonian

