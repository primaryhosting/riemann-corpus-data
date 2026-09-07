/-
  Brockian/Sieve.lean — the Sieve Hamiltonian / Phase–Depth Torus keepers.

  Canonical, citation-grade port of the July Aristotle campaign modules
  `SieveHamiltonian.lean` and `PhaseDepthTorus.lean` (the "intake 18" keepers),
  ported to Mathlib v4.32.0 and independently AXLE-verified.

  Content:
    * mod-3 pinning + no-go       : `twin_pins_mod_three`, `no_adjacent_admissible`
    * mod-5 run rigidity          : `run_cap`, `run3_signature`
    * H3 silver eigensystem       : `H3_ground` (2−√2), `H3_middle` (2),
                                    `H3_top` (2+√2), `H3_trace` (6), `H3_det` (4)
    * silver-gap alphabet         : `silver_gap_rigidity_finite`
    * ℓ−2 twin grammar            : `twin_admissible_card`
    * phase–depth torus           : `compatible_closure`, `tau_period`,
                                    `tau_minimal_period` (= 25), `tau_injective_on_period`

  Verification (spec §2A triple verification):
    - `#print axioms`  : ⊆ {propext, Classical.choice, Quot.sound}  (see registry)
    - AXLE independent : verified @ lean-4.32.0

  DROPPED / port-pending (NOT included — see the module report):
    * `triple_count`, `silver_edge_count`, `silver_components`,
      `finite_spectral_alphabet_L3` — genuine `sorry` TARGETs in the source
      (deep CRT / spectral-decomposition obligations); left as port-pending.
    * `return_in_kind`, `state_never_returns` — `sorry` TARGETs in the source.
    * `orbit_single_cycle`, `twin_wheel_two`, `three_road_balance_105` — the
      intake ledger flagged these as vacuous scaffolding (`… ∨ True`, `∧ False`,
      trivial `→ True`); DROPPED per the no-theater ethic.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.Sieve

open Matrix Finset

/-! ## 1. The no-go theorem: mod-3 pinning -/

/-- Twin admissibility pins the mod-3 residue to `2`. -/
theorem twin_pins_mod_three (a : ZMod 3) :
    (a ≠ 0 ∧ a + 2 ≠ 0) ↔ a = 2 := by
  revert a; decide

/-- NO-GO: two twin-admissible integers (both `≡ 2 mod 3`) are never at
distance `1` or `2`; the `+1` and `+2` adjacencies carry no admissible edges,
so the residual flow is `+3` on the surviving coset. -/
theorem no_adjacent_admissible (a b : ℤ)
    (ha : (a : ZMod 3) = 2) (hb : (b : ZMod 3) = 2)
    (h : b - a = 1 ∨ b - a = 2) : False := by
  have hz : ((b - a : ℤ) : ZMod 3) = 0 := by push_cast; rw [ha, hb]; ring
  rcases h with h1 | h2
  · rw [h1] at hz; exact absurd hz (by decide)
  · rw [h2] at hz; exact absurd hz (by decide)

/-! ## 2. The run-cap and signature theorems (mod-5 rigidity) -/

/-- RUN CAP: no four consecutive states of the `+3` flow are all admissible
mod 5 — four `+3` steps visit four distinct mod-5 classes, but only three
classes `{1,2,4}` are admissible. Hence every admissible run has length ≤ 3. -/
theorem run_cap :
    ¬ ∃ a : ZMod 5, ({a, a + 3, a + 6, a + 9} : Finset (ZMod 5)) ⊆
      ({1, 2, 4} : Finset (ZMod 5)) := by
  decide

/-- SIGNATURE: a maximal run of length 3 exists only with mod-5 signature
`(1, 4, 2)` — every ground-state triple rides the three roads. -/
theorem run3_signature (a : ZMod 5)
    (h : ({a, a + 3, a + 6} : Finset (ZMod 5)) ⊆
      ({1, 2, 4} : Finset (ZMod 5))) : a = 1 := by
  revert h; revert a; decide

/-! ## 3. The path spectra: exact eigensystem of the length-3 block -/

/-- The Dirichlet path Laplacian on three sites. -/
def H3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, -1, 0; -1, 2, -1; 0, -1, 2]

noncomputable def silverGap : ℝ := 2 - Real.sqrt 2

/-- SILVER-GAP EIGENVECTOR: `(1, √2, 1)` is an eigenvector of `H3` with
eigenvalue `2 − √2`. -/
theorem H3_ground :
    H3.mulVec ![1, Real.sqrt 2, 1] = silverGap • ![1, Real.sqrt 2, 1] := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  funext i
  fin_cases i <;>
    simp [H3, silverGap, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul] <;>
    ring_nf <;> nlinarith [h2]

/-- Middle mode: `(1, 0, −1)` with eigenvalue `2`. -/
theorem H3_middle :
    H3.mulVec ![1, 0, -1] = (2 : ℝ) • ![1, 0, -1] := by
  funext i
  fin_cases i <;>
    simp [H3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul] <;> ring

/-- Top mode: `(1, −√2, 1)` with eigenvalue `2 + √2`. -/
theorem H3_top :
    H3.mulVec ![1, -Real.sqrt 2, 1] =
      (2 + Real.sqrt 2) • ![1, -Real.sqrt 2, 1] := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  funext i
  fin_cases i <;>
    simp [H3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul] <;>
    ring_nf <;> nlinarith [h2]

/-- Consistency check: trace 6. -/
theorem H3_trace : H3.trace = 6 := by
  simp [H3, Matrix.trace, Matrix.diag, Fin.sum_univ_three]; norm_num

/-- Consistency check: determinant 4. -/
theorem H3_det : H3.det = 4 := by
  simp [H3, Matrix.det_fin_three]; norm_num

/-! ## 4. Silver-gap rigidity — the finite spectral alphabet.

At every wheel level (with `3, 5 ∣ M`) the compressed sieve Hamiltonian's
spectrum is contained in `{2−√2, 1, 2, 3, 2+√2}` — five lines forever — the
Dirichlet-path eigenvalues `2 − 2cos(jπ/(g+1))` for run length `g ≤ 3`. -/
def SilverGapRigidityTarget : Prop :=
  ∀ g : ℕ, g ≤ 3 → ∀ j : ℕ, 1 ≤ j → j ≤ g →
    (2 - 2 * Real.cos (Real.pi * j / (g + 1))) ∈
      ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set ℝ)

theorem silver_gap_rigidity_finite : SilverGapRigidityTarget := by
  intro g hg j hj1 hj2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases g <;> interval_cases j
  · -- g=1, j=1 : cos(π/2)=0 → 2
    right; right; left
    rw [show Real.pi * (1:ℕ) / ((1:ℕ) + 1) = Real.pi / 2 by push_cast; ring]
    rw [Real.cos_pi_div_two]; ring
  · -- g=2, j=1 : cos(π/3)=1/2 → 1
    right; left
    rw [show Real.pi * (1:ℕ) / ((2:ℕ) + 1) = Real.pi / 3 by push_cast; ring]
    rw [Real.cos_pi_div_three]; ring
  · -- g=2, j=2 : cos(2π/3)=-1/2 → 3
    right; right; right; left
    rw [show Real.pi * (2:ℕ) / ((2:ℕ) + 1) = Real.pi - Real.pi / 3 by push_cast; ring]
    rw [Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  · -- g=3, j=1 : cos(π/4)=√2/2 → 2-√2
    left
    rw [show Real.pi * (1:ℕ) / ((3:ℕ) + 1) = Real.pi / 4 by push_cast; ring]
    rw [Real.cos_pi_div_four]; ring
  · -- g=3, j=2 : cos(π/2)=0 → 2
    right; right; left
    rw [show Real.pi * (2:ℕ) / ((3:ℕ) + 1) = Real.pi / 2 by push_cast; ring]
    rw [Real.cos_pi_div_two]; ring
  · -- g=3, j=3 : cos(3π/4)=-√2/2 → 2+√2
    right; right; right; right
    rw [show Real.pi * (3:ℕ) / ((3:ℕ) + 1) = Real.pi - Real.pi / 4 by push_cast; ring]
    rw [Real.cos_pi_sub, Real.cos_pi_div_four]; ring

/-! ## 5. The ℓ − 2 twin grammar -/

/-- Local twin-start admissibility at an arbitrary modulus: `a ∉ {0, -2}`. -/
def TwinAdmissibleAt (ℓ : ℕ) [NeZero ℓ] (a : ZMod ℓ) : Prop := a ≠ 0 ∧ a + 2 ≠ 0

instance (ℓ : ℕ) [NeZero ℓ] : DecidablePred (TwinAdmissibleAt ℓ) := fun a =>
  inferInstanceAs (Decidable (a ≠ 0 ∧ a + 2 ≠ 0))

/-- BM-GRAM-001 (local twin-grammar count): for every prime `ℓ > 2` exactly two
residues are struck — `0` and `−2`, distinct because `ℓ ∤ 2` — leaving `ℓ − 2`. -/
theorem twin_admissible_card (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 2 < ℓ) :
    (Finset.univ.filter (fun a : ZMod ℓ => TwinAdmissibleAt ℓ a)).card = ℓ - 2 := by
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    have : ((2 : ℕ) : ZMod ℓ) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    simpa using this
  have hne : (0 : ZMod ℓ) ≠ -2 := fun hh => h2 (neg_eq_zero.mp hh.symm)
  have hset : (Finset.univ.filter (fun a : ZMod ℓ => TwinAdmissibleAt ℓ a))
      = (Finset.univ : Finset (ZMod ℓ)) \ {0, -2} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, TwinAdmissibleAt, not_or]
    apply and_congr_right
    intro _
    constructor
    · intro hb he; exact hb (by rw [he]; ring)
    · intro hb he; exact hb (by rw [add_eq_zero_iff_eq_neg] at he; exact he)
  have hcard : (Finset.univ : Finset (ZMod ℓ)).card = ℓ := by
    rw [Finset.card_univ, ZMod.card]
  have hpair : ({0, -2} : Finset (ZMod ℓ)).card = 2 := Finset.card_pair hne
  rw [hset, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.univ_inter, hcard, hpair]

/-! ## 6. The phase–depth torus -/

/-- Geometric phase index `φ(n) = (n − 1) mod 5`. -/
def phi (n : ℤ) : ZMod 5 := ((n - 1 : ℤ) : ZMod 5)

/-- The discrete torus state: tube phase in `ZMod 5`, hole class in `ZMod 25`. -/
def tau (n : ℤ) : ZMod 5 × ZMod 25 := (phi n, ((2 * (n - 1) : ℤ) : ZMod 25))

/-- BM-CLOSE-001 (compatible quotient theorem): identifying depth with period `L`
respects the five-phase system exactly when `5 ∣ L`. -/
theorem compatible_closure (L : ℤ) :
    (∀ n : ℤ, phi (n + L) = phi n) ↔ (5 : ℤ) ∣ L := by
  constructor
  · intro h
    have h1 := h 1
    unfold phi at h1
    have : ((L : ℤ) : ZMod 5) = 0 := by
      push_cast at h1 ⊢
      simpa using h1
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd L 5).mp this
  · intro hdvd n
    unfold phi
    obtain ⟨k, rfl⟩ := hdvd
    push_cast
    have h5 : (5 : ZMod 5) = 0 := by decide
    linear_combination (k : ZMod 5) * h5

/-- BM-TORUS-001a (the orbit closes at 25). -/
theorem tau_period (n : ℤ) : tau (n + 25) = tau n := by
  unfold tau phi
  refine Prod.ext ?_ ?_
  · push_cast
    have h : (25 : ZMod 5) = 0 := by decide
    linear_combination h
  · push_cast
    have h : (50 : ZMod 25) = 0 := by decide
    linear_combination h

/-- BM-TORUS-001b (no smaller positive period): the minimal period is exactly 25. -/
theorem tau_minimal_period (d : ℕ) (hd : 0 < d)
    (h : ∀ n : ℤ, tau (n + d) = tau n) : 25 ≤ d := by
  have h2 := congrArg Prod.snd (h 1)
  simp only [tau] at h2
  have e25 : (((2 * (d : ℤ) : ℤ)) : ZMod 25) = 0 := by
    push_cast at h2 ⊢
    linear_combination h2
  have d25 : (25 : ℤ) ∣ (2 * (d : ℤ)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (d : ℤ)) 25).mp e25
  have hcop : IsCoprime (25 : ℤ) 2 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  have d25' : (25 : ℤ) ∣ (d : ℤ) := hcop.dvd_of_dvd_mul_left d25
  omega

/-- BM-TORUS-injectivity: the map `n ↦ tau n` is injective on `1..25`. -/
theorem tau_injective_on_period :
    ∀ m k : ℤ, 1 ≤ m → m ≤ 25 → 1 ≤ k → k ≤ 25 → tau m = tau k → m = k := by
  intro m k hm1 hm2 hk1 hk2 htau
  have h2 := congrArg Prod.snd htau
  simp only [tau] at h2
  have e25 : ((2 * (m - k) : ℤ) : ZMod 25) = 0 := by
    have hh := sub_eq_zero.mpr h2
    push_cast at hh ⊢
    linear_combination hh
  have d25 : (25 : ℤ) ∣ (2 * (m - k)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (m - k)) 25).mp e25
  have hcop : IsCoprime (25 : ℤ) 2 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  have d25' : (25 : ℤ) ∣ (m - k) := hcop.dvd_of_dvd_mul_left d25
  omega

end Brockian.Sieve
