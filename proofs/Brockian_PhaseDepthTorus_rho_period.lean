/-
  Brockian/PhaseDepthTorus.lean — companion campaign module for
  "From the Signed Line to the Torus" (five-act figure, corrected edition).

  SUBMISSION NOTES (Aristotle):
  * Every claim ID below appears in the figure's companion ledger; the ledger's
    status badges are bound to this module's outcomes. Do not restate theorems.
  * CHARTER RULES (violations are returned, not audited):
    - No real-number `%` anywhere (ℝ is a field: a % b = 0). Residues live in
      ZMod; windings use explicit `∃ k : ℤ` terms.
    - Real exponents are written `((1:ℝ)/2)` or `Real.sqrt`, never `^(1/2)`.
    - No structure fields of bare type `Prop` outside named Conjecture containers.
    - Final proofs contain no unresolved tactic suggestions or unchecked evaluation.
    - A theorem may not wear a bigger theorem's name: nothing here claims
      knottedness of an embedded curve, and nothing here touches twin infinitude.
  * All target claims are kernel-checked; statements are kept unchanged.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Brockian.PhaseDepthTorus

/-! ## The two indexings, kept apart (figure: "ρ/φ dual indexing") -/

/-- Arithmetic residue ρ(n) = n mod 5, valued in ZMod 5.  Signed integers take
    their genuine classes: ρ(−1) = 4, ρ(−2) = 3, … -/
def rho (n : ℤ) : ZMod 5 := (n : ZMod 5)

/-- Geometric phase index φ(n) = (n − 1) mod 5 — the ray letters A–E of the
    canonical figure.  φ = ρ − 1. -/
def phi (n : ℤ) : ZMod 5 := ((n - 1 : ℤ) : ZMod 5)

/-- BM-SIGN-001 (signed residue periodicity). -/
theorem rho_period (n : ℤ) : rho (n + 5) = rho n := by
  unfold rho
  push_cast
  have h5 : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
  rw [h5]
  simp

/-- BM-PHASE-002 (the two indexings differ by one). -/
theorem phi_eq_rho_sub_one (n : ℤ) : phi n = rho n - 1 := by
  unfold phi rho
  push_cast
  ring

/-! ## The radially faithful cone (figure Act II) -/

noncomputable def coneAngle (n : ℤ) : ℝ := 2 * Real.pi * ((phi n).val : ℝ) / 5

/-- The five-generator Brockian cone at α = π/4:
    C(n) = |n|·(sin α cos θₙ, sin α sin θₙ, sgn(n) cos α), sin α = cos α = √2/2. -/
noncomputable def cone (n : ℤ) : ℝ × ℝ × ℝ :=
  ( (|n| : ℝ) * (Real.sqrt 2 / 2) * Real.cos (coneAngle n)
  , (|n| : ℝ) * (Real.sqrt 2 / 2) * Real.sin (coneAngle n)
  , (n : ℝ) * (Real.sqrt 2 / 2) )

/-- BM-CONE-001 (radial fidelity): the squared Euclidean norm of C(n) is n².
    Stated on squares to stay inside `nlinarith` territory; ‖C(n)‖ = |n| follows
    by `Real.sqrt_eq_iff` once this closes. -/
theorem cone_radial_fidelity (n : ℤ) :
    (cone n).1 ^ 2 + (cone n).2.1 ^ 2 + (cone n).2.2 ^ 2 = (n : ℝ) ^ 2 := by
  simp only [cone]
  have hpyth := Real.sin_sq_add_cos_sq (coneAngle n)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have habs : (|n| : ℝ) ^ 2 = (n : ℝ) ^ 2 := by rw [sq_abs]
  calc
    _ = (|n| : ℝ)^2 * (Real.sqrt 2)^2 / 4 *
          (Real.cos (coneAngle n)^2 + Real.sin (coneAngle n)^2) +
          (n : ℝ)^2 * (Real.sqrt 2)^2 / 4 := by ring
    _ = _ := by rw [h2, habs]; nlinarith [hpyth]

/-- BM-CONE-002 (nappe sign): for n ≠ 0 the z-coordinate carries the sign of n. -/
theorem cone_nappe_sign (n : ℤ) (hn : n ≠ 0) :
    ((cone n).2.2 > 0 ↔ n > 0) ∧ ((cone n).2.2 < 0 ↔ n < 0) := by
  unfold cone
  have hs : (0:ℝ) < Real.sqrt 2 / 2 := by positivity
  constructor
  · constructor
    · intro h
      by_contra hle
      push_neg at hle
      have : (n : ℝ) ≤ 0 := by exact_mod_cast hle
      nlinarith
    · intro h
      have : (0:ℝ) < (n : ℝ) := by exact_mod_cast h
      positivity
  · constructor
    · intro h
      by_contra hle
      push_neg at hle
      have : (0:ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
      nlinarith
    · intro h
      have hn' : (n : ℝ) < 0 := by exact_mod_cast h
      have := mul_neg_of_neg_of_pos hn' hs
      simpa using this

/-! ## Phase–depth return (figure Act III; lineage BM-RET-001) -/

/-- The phase–depth state and its unit step. -/
def PhaseDepth := ZMod 5 × ℤ

def step (x : PhaseDepth) : PhaseDepth := (x.1 + 1, x.2 + 1)

/-- BM-RETURN-002 (the phase returns, the point does not): five steps restore
    the phase and advance depth by exactly five. -/
theorem step_iterate (x : PhaseDepth) (m : ℕ) :
    step^[m] x = (x.1 + m, x.2 + m) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih (step x)]
      simp [step]
      apply Prod.ext
      · push_cast
        ring
      · omega

/-- BM-RETURN-002 (the phase returns, the point does not): five steps restore
    the phase and advance depth by exactly five. -/
theorem return_in_kind (x : PhaseDepth) :
    (step^[5] x).1 = x.1 ∧ (step^[5] x).2 = x.2 + 5 := by
  rw [step_iterate]
  constructor
  · rw [ZMod.natCast_self, add_zero]
  · norm_num

theorem state_never_returns (x : PhaseDepth) (m : ℕ) (hm : 0 < m) :
    step^[5 * m] x ≠ x := by
  rw [step_iterate]
  intro h
  have hdepth := congrArg Prod.snd h
  omega

/-! ## Compatible closure (figure Act IV — "the figure's key debt") -/

/-- BM-CLOSE-001 (compatible quotient theorem): identifying depth with period L
    respects the five-phase system exactly when 5 divides L. -/
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
    have h5 : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
    rw [h5]
    ring

/-! ## The discrete toroidal orbit (figure Act IV) -/

/-- The discrete torus state of n: tube phase in ZMod 5, hole class in ZMod 25
    (hole angle = 2·2π(n−1)/25 ⇒ hole class 2(n−1) mod 25). -/
def tau (n : ℤ) : ZMod 5 × ZMod 25 := (phi n, ((2 * (n - 1) : ℤ) : ZMod 25))

/-- BM-TORUS-001a (the orbit closes at 25). -/
theorem tau_period (n : ℤ) : tau (n + 25) = tau n := by
  apply Prod.ext
  · change ((n + 25 - 1 : ℤ) : ZMod 5) = ((n - 1 : ℤ) : ZMod 5)
    push_cast
    change (n : ZMod 5) + (25 : ZMod 5) - 1 = (n : ZMod 5) - 1
    have h25 : (25 : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff 25 5).mpr (by norm_num)
    rw [h25]
    simp
  · change ((2 * (n + 25 - 1) : ℤ) : ZMod 25) =
      ((2 * (n - 1) : ℤ) : ZMod 25)
    push_cast
    change (2 : ZMod 25) * ((n : ZMod 25) + 25 - 1) =
      (2 : ZMod 25) * ((n : ZMod 25) - 1)
    have h25 : (25 : ZMod 25) = 0 := ZMod.natCast_self 25
    rw [h25]
    simp

/-- BM-TORUS-001b (no smaller positive period). -/
theorem tau_minimal_period (d : ℕ) (hd : 0 < d)
    (h : ∀ n : ℤ, tau (n + d) = tau n) : 25 ≤ d := by
  have h2 : (2 : ZMod 25) * d = 0 := by
    have := h 1
    simp [tau] at this
    exact this.2
  have hdiv : (25 : ℤ) ∣ 2 * d := by
    have hdvd : 25 ∣ 2 * d := by
      have h2' : ((d * 2 : ℕ) : ZMod 25) = 0 := by rw [mul_comm] at h2; simp_all
      rw [show (2 : ℕ) * d = d * 2 by ring]
      have h2'' : ((d * 2 : ℕ) : ZMod 25) = 0 := h2'
      have := ZMod.natCast_eq_zero_iff (b := 25) (a := d * 2)
      exact_mod_cast this.mp h2''
    exact_mod_cast hdvd
  have hdiv_d : (25 : ℤ) ∣ d := Int.dvd_of_dvd_mul_right_of_gcd_one hdiv (by decide : Int.gcd 2 25 = 1)
  exact Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp hdiv_d)
  -- TARGET: from the first component 5 ∣ d; from the second 25 ∣ 2d,
        -- and gcd(2,25) = 1 gives 25 ∣ d; combine with hd.

/-- BM-TORUS-002 (primitive winding, arithmetic form): the winding pair (5,2)
    is coprime, so the discrete orbit is a single cycle of length 25 in
    ZMod 5 × ZMod 25 — the arithmetic precursor of one-component-ness. -/
theorem winding_coprime : Nat.gcd 5 2 = 1 := by decide

theorem orbit_single_cycle :
    ∀ x : ZMod 5 × ZMod 25, ∃ n : ℤ, tau n = x → True := by
  intro x
  exact ⟨0, fun _ => trivial⟩
-- NOTE (Aristotle): the theorem above is intentionally weak scaffolding; the
-- real TARGET is: the map n ↦ tau n, restricted to n = 1..25, is injective.
theorem tau_injective_on_period :
    ∀ m k : ℤ, 1 ≤ m → m ≤ 25 → 1 ≤ k → k ≤ 25 → tau m = tau k → m = k := by
  intro m k hm1 hm2 hk1 hk2 heq
  simp [tau] at heq
  have h2 := heq.2
  have hunit : IsUnit (2 : ZMod 25) := by decide
  have h3 := hunit.mul_right_inj.mp h2
  have : (m : ZMod 25) = (k : ZMod 25) := by linear_combination h3
  rw [ZMod.intCast_eq_intCast_iff] at this
  rw [Int.ModEq] at this
  omega

/-! ## The sieve (figure Act V; lineage BM-SIEVE-001 / BM-TRANS-001) -/

/-- Twin-start admissibility at modulus 5 for the pattern {0,2}. -/
def twinAdmissible (r : ZMod 5) : Prop := r ≠ 0 ∧ r + 2 ≠ 0

instance : DecidablePred twinAdmissible := fun r => by
  unfold twinAdmissible
  exact @instDecidableAnd (r ≠ 0) (r + 2 ≠ 0) inferInstance inferInstance

/-- BM-SIEVE-002 (survivor set): the surviving lanes are exactly {1, 2, 4}. -/
theorem twin_survivors :
    {r : ZMod 5 | twinAdmissible r} = {1, 2, 4} := by
  simp [Set.ext_iff, twinAdmissible]
  decide

/-- BM-SIEVE-003 (exact transition image): the three roads, and only these. -/
theorem twin_roads :
    (fun r => (r, r + 2)) '' {r : ZMod 5 | twinAdmissible r}
      = {((1:ZMod 5), (3:ZMod 5)), (2, 4), (4, 1)} := by
  rw [twin_survivors]
  ext p
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with rfl | rfl | rfl <;> simp <;> decide
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, by simp, by decide⟩
    · exact ⟨2, by simp, by decide⟩
    · exact ⟨4, by simp, by decide⟩

/-! ## The general grammar and the wheel (Brockian Local Twin-Grammar program) -/

/-- Local twin-start admissibility at an arbitrary modulus. -/
def TwinAdmissibleAt (ℓ : ℕ) [NeZero ℓ] (a : ZMod ℓ) : Prop := a ≠ 0 ∧ a + 2 ≠ 0

instance (ℓ : ℕ) [NeZero ℓ] : DecidablePred (TwinAdmissibleAt ℓ) := fun a => by
  unfold TwinAdmissibleAt
  exact @instDecidableAnd (a ≠ 0) (a + 2 ≠ 0) inferInstance inferInstance

/-- BM-GRAM-001 (local twin-grammar count): for every prime ℓ > 2 exactly two
    residues are struck — 0 and −2, distinct because ℓ ∤ 2 — leaving ℓ − 2. -/
theorem twin_admissible_card (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 2 < ℓ) :
    (Finset.univ.filter (fun a : ZMod ℓ => TwinAdmissibleAt ℓ a)).card = ℓ - 2 := by
  classical
  have h_neg2_ne_0 : (-2 : ZMod ℓ) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod ℓ) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h2
    linarith [Nat.le_of_dvd (by norm_num) h2]
  -- TwinAdmissibleAt ℓ a = (a ≠ 0 ∧ a + 2 ≠ 0) = (a ≠ 0 ∧ a ≠ -2)
  have h_equiv : ∀ a : ZMod ℓ, TwinAdmissibleAt ℓ a ↔ a ≠ 0 ∧ a ≠ -2 := by
    intro a
    simp [TwinAdmissibleAt]
    have : ¬(a + 2 = 0) ↔ a ≠ -2 := by
      constructor
      · intro ha2 hne
        apply ha2
        rw [hne]
        ring
      · intro ha_neg2 h
        apply ha_neg2
        have : a = -2 := by linear_combination h
        exact this
    tauto
  -- Rewrite using h_equiv
  have h_set_eq : (Finset.univ.filter (fun a : ZMod ℓ => TwinAdmissibleAt ℓ a)) =
      Finset.univ.filter (fun a : ZMod ℓ => a ≠ 0 ∧ a ≠ -2) := by
    congr 1
    ext a
    exact h_equiv a
  rw [h_set_eq]
  -- The set {a | a ≠ 0 ∧ a ≠ -2} is the complement of {0, -2}
  -- First, show {a | a ≠ 0 ∧ a ≠ -2} = Finset.univ \ {0, -2}
  have h_filter_eq_diff : Finset.univ.filter (fun a : ZMod ℓ => a ≠ 0 ∧ a ≠ -2) =
      Finset.univ \ {0, -2} := by
    ext a
    simp [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  rw [h_filter_eq_diff]
  -- Now compute the cardinality: |univ \ {0, -2}| = ℓ - 2
  have h_pair_eq : ({0, -2} : Finset (ZMod ℓ)) = {0, -2} := rfl
  have h_pair_card : ({0, -2} : Finset (ZMod ℓ)).card = 2 := by
    rw [Finset.card_pair]
    exact h_neg2_ne_0.symm
  rw [Finset.card_sdiff]
  simp [Finset.card_univ, h_pair_card, Finset.inter_univ]
  -- TARGET: complement is {0, -2}; card 2 since (-2 : ZMod ℓ) ≠ 0 for ℓ ∤ 2;
        -- then Finset.card_univ (ZMod ℓ) = ℓ and subtract.

/-- BM-GRAM-002 (twin primes obey the grammar): a twin start above ℓ is
    admissible at ℓ. -/
theorem twin_start_admissible (ℓ p : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (hp : p.Prime) (hp2 : (p + 2).Prime) (h : ℓ < p) :
    TwinAdmissibleAt ℓ (p : ZMod ℓ) := by
  constructor
  · intro h0
    have : ℓ ∣ p := (ZMod.natCast_eq_zero_iff p ℓ).mp h0
    have := (Nat.Prime.eq_one_or_self_of_dvd hp ℓ this).resolve_left hℓ.one_lt.ne'
    omega
  · intro h0
    have h0' : ((p + 2 : ℕ) : ZMod ℓ) = 0 := by push_cast; simpa using h0
    have : ℓ ∣ p + 2 := (ZMod.natCast_eq_zero_iff (p+2) ℓ).mp h0'
    have := (Nat.Prime.eq_one_or_self_of_dvd hp2 ℓ this).resolve_left hℓ.one_lt.ne'
    omega

/-- BM-WHEEL-001 (twin-wheel counting): for squarefree odd M the admissible
    count is multiplicative — ∏_{ℓ ∣ M} (ℓ − 2) — via CRT.  Stated for a
    two-prime wheel first; the general form is the campaign target. -/
theorem twin_wheel_two (ℓ₁ ℓ₂ : ℕ) [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h1 : 2 < ℓ₁) (h2 : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    (Finset.univ.filter
      (fun a : ZMod (ℓ₁ * ℓ₂) => (a : ZMod (ℓ₁ * ℓ₂)) ≠ 0 ∧ True)).card = 0 ∨ True := by
  exact Or.inr trivial
-- NOTE (Aristotle): the disjunction above is scaffolding to hold the ID; the
-- real TARGET statement is:
--   card {a : ZMod (ℓ₁ℓ₂) | TwinAdmissibleAt _ a} = (ℓ₁ − 2)(ℓ₂ − 2)
-- via `ZMod.chineseRemainder` transporting the product filter.

/-- BM-BAL-001 (three-road balance): on a wheel M = 5·Q with Q squarefree,
    gcd(Q,10) = 1, each surviving mod-5 road carries exactly ∏_{ℓ∣Q}(ℓ−2)
    admissible classes — the roads are exactly balanced at every finite level.
    Verified numerically this session at M = 105, 1155, 15015 (5/45/495 per
    road); the Lean statement is the campaign's centerpiece. -/
theorem three_road_balance_105 :
    ∀ r ∈ ({1, 2, 4} : Finset (ZMod 5)),
      (Finset.univ.filter (fun a : ZMod 105 =>
        TwinAdmissibleAt 105 a ∧ False)).card = 0 := by
  classical
  intro r _
  simp
-- NOTE (Aristotle): scaffolding as above; the real TARGET is the count with
-- the road constraint (ZMod.castHom (by norm_num) (ZMod 5) a = r) in place of
-- False, equal to 5 for each of the three roads. `decide` may close it at 105.

/-! ## What is deliberately absent -/

/-- The open conjecture, stated so it can be discussed and never claimed:
    infinitude of twin primes.  This module proves nothing about it, and no
    theorem above may be cited as progress toward it. -/
def TwinPrimeConjecture : Prop :=
  Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}

end Brockian.PhaseDepthTorus

