/-
  Brockian/CyclotomicRealDegree.lean — the composite-`n` real cyclotomic degree
  and the classification of which `n` give a QUADRATIC real subfield.

  `Brockian/GaloisGeneralDegree.lean` proved, for every odd PRIME `p`,

        `[ℚ(2cos 2π/p) : ℚ] = (p − 1) / 2`,

  isolating the golden quadratic at `p = 5`.  This file generalizes the degree
  computation to ALL `n ≥ 3` — the maximal real subfield `ℚ(ζ_n)⁺` of the `n`-th
  cyclotomic field has degree `φ(n)/2` (Euler totient) — and then classifies the
  `n` whose real subfield is a QUADRATIC field.

  ## Proof architecture (same classical tower as `GaloisGeneralDegree`, now for
     general `n`, the only prime-specific step being the cyclotomic degree)

  With `ζ = exp(2πi/n)` (`Complex.isPrimitiveRoot_exp`) and `α = ζ + ζ⁻¹`:

    * `[ℚ(ζ):ℚ] = φ(n)`          — `cyclotomic_eq_minpoly_rat` + `natDegree_cyclotomic`
                                   (for a PRIME this was `Nat.totient_prime`; here we
                                   keep the general totient value).
    * `ζ ∉ ℚ(α)`                 — complex conjugation fixes all of `ℚ(α)` (`α` real,
                                   `conj ζ = ζ⁻¹`); fixing `ζ` forces `ζ² = 1`, i.e.
                                   `n ∣ 2`, impossible for `n ≥ 3`.
    * `[ℚ(ζ):ℚ(α)] = 2`          — `ζ` is a root of the monic `X² − αX + 1` over `ℚ(α)`
                                   and `ζ ∉ ℚ(α)`.
    * tower law                   `φ(n) = [ℚ(ζ):ℚ(α)] · [ℚ(α):ℚ] = 2 · [ℚ(α):ℚ]`.

  The classification `φ(n) = 4 ⟺ n ∈ {5,8,10,12}` bounds `n` arithmetically:
  every prime `p ∣ n` has `φ(p) = p − 1 ∣ φ(n) = 4`, so `p ∈ {2,3,5}`, and each
  prime-power exponent is bounded by `φ(p^k) ∣ 4`, whence `n ∣ 120`; a finite check
  over the divisors of `120` finishes it.

  ## What is proved (AXLE-verified at lean-4.32.0, axioms ⊆
     {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`)

    * `spectral_natDegree_two_mul` — for every `n ≥ 3`,
                                     `[ℚ(2cos 2π/n):ℚ] · 2 = φ(n)`  (the tower identity).
    * `spectral_degree_general`    — **the general theorem (#6)**: for every `n ≥ 3`,
                                     `[ℚ(2cos 2π/n):ℚ] = φ(n)/2`.
    * `quadratic_iff_totient_four` — for every `n ≥ 3`, the real subfield is QUADRATIC
                                     (`degree = 2`) iff `φ(n) = 4`.
    * `totient_eq_four_iff`        — **the arithmetic classification**:
                                     `φ(n) = 4 ⟺ n ∈ {5,8,10,12}`.
    * `quadratic_iff_mem`          — **the full classification (#8)**: for every `n ≥ 3`,
                                     `[ℚ(2cos 2π/n):ℚ] = 2 ⟺ n ∈ {5,8,10,12}`.
    * `pentagon_quadratic`         — the pentagon (`n = 5`) is a quadratic case (the golden
                                     field `ℚ(√5)`; cf. `GaloisWhyFive.degree_five`).

  ## What is NOT proved

    * `n ∈ {0,1,2}` is excluded (`n ≥ 3` hypothesis): there `2cos(2π/n) ∈ ℚ`
      (degrees `2cos 0 = 2`, `2cos π = −2`), the degenerate boundary, not the
      maximal-real-subfield regime.  The theorem is fully general for `n ≥ 3`.
    * The specific golden identification `2cos(2π/10) = φ` (the `n = 10` member of the
      quadratic family) is not re-derived here; only `n = 5` is tied to `ℚ(√5)` via
      `GaloisWhyFive`.  Both `n = 5` and `n = 10` are covered by `quadratic_iff_mem`
      as quadratic cases; the field being *golden* is proved only for `n = 5`.

  ## Precise remaining obstruction

    * None for the stated targets.  Both the general degree `φ(n)/2` (all `n ≥ 3`) and
      the quadratic classification `n ∈ {5,8,10,12}` are closed.  They rest on
      Mathlib's `Polynomial.cyclotomic.irreducible_rat` and `natDegree_cyclotomic`,
      both fully proved in Mathlib.
-/
import Mathlib
import Brockian.GaloisWhyFive
import Brockian.GaloisGeneralDegree

namespace Brockian.CyclotomicRealDegree

open Polynomial
open scoped IntermediateField
open Brockian.GaloisWhyFive (spectralGen)

/-- **Tower identity for the general real subfield.**  For every `n ≥ 3`,
`[ℚ(2cos 2π/n):ℚ] · 2 = φ(n)`.  This is the degree-`2` tower
`ℚ ⊆ ℚ(2cos 2π/n) ⊆ ℚ(ζ_n)` combined with `[ℚ(ζ_n):ℚ] = φ(n)`. -/
theorem spectral_natDegree_two_mul {n : ℕ} (hn : 3 ≤ n) :
    (minpoly ℚ (spectralGen n)).natDegree * 2 = Nat.totient n := by
  have hn0 : n ≠ 0 := by omega
  -- The primitive n-th root of unity ζ = exp(2πi/n).
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) with hζ_def
  have hζ : IsPrimitiveRoot ζ n := by rw [hζ_def]; exact Complex.isPrimitiveRoot_exp n hn0
  have hpow : ζ ^ n = 1 := hζ.pow_eq_one
  have hz : ζ ≠ 0 := by
    intro h; rw [h, zero_pow hn0] at hpow; exact one_ne_zero hpow.symm
  have hζinv : ζ⁻¹ = ζ ^ (n - 1) := by
    have h1 : ζ * ζ ^ (n - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]; exact hpow
    exact (eq_inv_of_mul_eq_one_right h1).symm
  -- Argument identity and modulus/real-part of ζ.
  have harg : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
            = ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hnorm : ‖ζ‖ = 1 := by rw [hζ_def, harg]; exact Complex.norm_exp_ofReal_mul_I _
  have hre : ζ.re = Real.cos (2 * Real.pi / (n : ℝ)) := by
    rw [hζ_def, harg]; exact Complex.exp_ofReal_mul_I_re _
  have hconjζ : (starRingEnd ℂ) ζ = ζ⁻¹ := (Complex.inv_eq_conj hnorm).symm
  -- The real spectral generator α = ζ + ζ⁻¹.
  set α : ℂ := ζ + ζ⁻¹ with hα
  -- every element of ℚ(α) is fixed by complex conjugation.
  have hfix : ∀ x, x ∈ (ℚ⟮α⟯ : IntermediateField ℚ ℂ) → (starRingEnd ℂ) x = x := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [hα, map_add, map_inv₀, hconjζ, inv_inv]; ring
    | algebraMap q => simp
    | add a b _ _ iha ihb => rw [map_add, iha, ihb]
    | inv a _ iha => rw [map_inv₀, iha]
    | mul a b _ _ iha ihb => rw [map_mul, iha, ihb]
  -- ζ ∉ ℚ(α): otherwise conjugation fixes ζ, forcing ζ² = 1, i.e. n ∣ 2 — impossible for n ≥ 3.
  have hζ_notin : ζ ∉ (ℚ⟮α⟯ : IntermediateField ℚ ℂ) := by
    intro hmem
    have h1 := hfix ζ hmem
    rw [hconjζ] at h1
    have hsq : ζ ^ 2 = 1 := by
      have hmc : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hz
      rw [h1] at hmc
      rw [pow_two]; exact hmc
    have hdvd : n ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp hsq
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  -- α = 2 cos(2π/n) = spectralGen n (as a complex number).
  have halpha : α = ((spectralGen n : ℝ) : ℂ) := by
    rw [hα, ← hconjζ, Complex.add_conj, hre]
    simp only [spectralGen]
  -- Integrality.
  have hζint : IsIntegral ℚ ζ := (hζ.isIntegral (by omega : 0 < n)).tower_top
  have hζintK : IsIntegral (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) ζ := hζint.tower_top
  have hαint : IsIntegral ℚ α := by
    rw [hα, hζinv]; exact hζint.add (hζint.pow (n - 1))
  -- [ℚ(ζ):ℚ(α)] = 2.
  have hself : α ∈ (ℚ⟮α⟯ : IntermediateField ℚ ℂ) :=
    IntermediateField.mem_adjoin_simple_self ℚ α
  have hq_aeval :
      (Polynomial.aeval ζ)
        (X ^ 2 - C (⟨α, hself⟩ : ↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) * X + 1) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one]
    rw [show (algebraMap (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) ℂ)
          (⟨α, hself⟩ : ↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) = α from rfl, hα]
    have hmul : ζ⁻¹ * ζ = 1 := inv_mul_cancel₀ hz
    linear_combination -hmul
  have hqmonic :
      (X ^ 2 - C (⟨α, hself⟩ : ↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) * X + 1 :
        (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ))[X]).Monic := by monicity!
  have hqdeg :
      (X ^ 2 - C (⟨α, hself⟩ : ↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) * X + 1 :
        (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ))[X]).natDegree = 2 := by compute_degree!
  have hdeg2 : (minpoly (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) ζ).natDegree = 2 := by
    refine le_antisymm ?_ ?_
    · calc (minpoly (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) ζ).natDegree
            ≤ (X ^ 2 - C (⟨α, hself⟩ : ↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) * X + 1 :
                (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ))[X]).natDegree :=
              Polynomial.natDegree_le_natDegree
                (minpoly.min (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) ζ hqmonic hq_aeval)
        _ = 2 := hqdeg
    · rw [minpoly.two_le_natDegree_iff hζintK]
      intro hmem
      rw [RingHom.mem_range] at hmem
      obtain ⟨y, hy⟩ := hmem
      apply hζ_notin
      rw [← hy]
      exact SetLike.coe_mem y
  -- The tower [ℚ(α):ℚ] · [ℚ(ζ):ℚ(α)] = [ℚ(ζ):ℚ], with [ℚ(ζ):ℚ] = φ(n).
  have hdK : Module.finrank ℚ (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) = (minpoly ℚ α).natDegree :=
    IntermediateField.adjoin.finrank hαint
  have hfinM_rel : Module.finrank (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) (ℚ⟮α⟯⟮ζ⟯) = 2 := by
    rw [IntermediateField.adjoin.finrank hζintK]; exact hdeg2
  have hfinM_abs : Module.finrank ℚ (ℚ⟮α⟯⟮ζ⟯) = Nat.totient n := by
    have hαle : (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮ζ⟯ := by
      rw [IntermediateField.adjoin_simple_le_iff, hα]
      exact add_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ)
        (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ))
    have hMrs : (ℚ⟮α⟯⟮ζ⟯).restrictScalars ℚ = (ℚ⟮ζ⟯ : IntermediateField ℚ ℂ) :=
      (IntermediateField.restrictScalars_adjoin_eq_sup ℚ (ℚ⟮α⟯ : IntermediateField ℚ ℂ)
        ({ζ} : Set ℂ)).trans (sup_eq_right.mpr hαle)
    have hfz : Module.finrank ℚ (↥(ℚ⟮ζ⟯ : IntermediateField ℚ ℂ)) = Nat.totient n := by
      rw [IntermediateField.adjoin.finrank hζint, ← cyclotomic_eq_minpoly_rat hζ (by omega),
        natDegree_cyclotomic n ℚ]
    calc Module.finrank ℚ (ℚ⟮α⟯⟮ζ⟯)
          = Module.finrank ℚ (↥((ℚ⟮α⟯⟮ζ⟯).restrictScalars ℚ)) := rfl
      _ = Module.finrank ℚ (↥(ℚ⟮ζ⟯ : IntermediateField ℚ ℂ)) := by rw [hMrs]
      _ = Nat.totient n := hfz
  have htower :
      Module.finrank ℚ (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ))
        * Module.finrank (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) (ℚ⟮α⟯⟮ζ⟯)
        = Module.finrank ℚ (ℚ⟮α⟯⟮ζ⟯) :=
    Module.finrank_mul_finrank ℚ (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) (ℚ⟮α⟯⟮ζ⟯)
  have hkey : (minpoly ℚ α).natDegree * 2 = Nat.totient n := by
    rw [← hdK, ← hfinM_rel, htower, hfinM_abs]
  -- Bridge the real generator's minimal polynomial to the complex one.
  have hbridge :
      (minpoly ℚ (spectralGen n)).natDegree = (minpoly ℚ α).natDegree := by
    rw [halpha,
      show ((spectralGen n : ℝ) : ℂ) = algebraMap ℝ ℂ (spectralGen n) from rfl,
      minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective ℝ ℂ)]
  rw [hbridge]; exact hkey

/-- **General degree of the real cyclotomic subfield (#6).**  For every `n ≥ 3`,
`[ℚ(2cos 2π/n) : ℚ] = φ(n)/2` — the degree of the maximal real subfield
`ℚ(ζ_n)⁺` of the `n`-th cyclotomic field.  Generalizes the odd-prime theorem
`GaloisGeneralDegree.real_subfield_degree` to all `n`, using the full Euler
totient in place of `p − 1`. -/
theorem spectral_degree_general {n : ℕ} (hn : 3 ≤ n) :
    (minpoly ℚ (spectralGen n)).natDegree = Nat.totient n / 2 := by
  have h := spectral_natDegree_two_mul hn
  omega

/-- **Quadratic ⟺ `φ(n) = 4`.**  For every `n ≥ 3`, the real subfield
`ℚ(2cos 2π/n)` is a quadratic field (`degree = 2`) iff `φ(n) = 4`.  Immediate from
the tower identity `degree · 2 = φ(n)`. -/
theorem quadratic_iff_totient_four {n : ℕ} (hn : 3 ≤ n) :
    (minpoly ℚ (spectralGen n)).natDegree = 2 ↔ Nat.totient n = 4 := by
  have h := spectral_natDegree_two_mul hn
  omega

/-- **The arithmetic classification `φ(n) = 4 ⟺ n ∈ {5,8,10,12}`.**  Every prime
`p ∣ n` satisfies `p − 1 = φ(p) ∣ φ(n) = 4`, so `p ∈ {2,3,5}`, and each prime-power
exponent is bounded by `φ(p^k) ∣ 4` (`2^k ∣ 8`, `3^k ∣ 3`, `5^k ∣ 5`), whence
`n ∣ 120`.  A finite check over the sixteen divisors of `120` finishes. -/
theorem totient_eq_four_iff {n : ℕ} :
    Nat.totient n = 4 ↔ n = 5 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
  constructor
  · intro h
    have hdvd120 : n ∣ 120 := by
      rw [Nat.dvd_iff_prime_pow_dvd_dvd 120 n]
      intro p k hpP hpk
      have hp : p.Prime := hpP
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; simpa using one_dvd (120 : ℕ)
      -- k ≥ 1, so p ∣ n.
      have hpdvdn : p ∣ n := dvd_trans (dvd_pow_self p hkpos.ne') hpk
      -- (p - 1) ∣ 4, hence p ≤ 5.
      have hpsub : (p - 1) ∣ 4 := by
        have hd := Nat.totient_dvd_of_dvd hpdvdn
        rwa [Nat.totient_prime hp, h] at hd
      have hp5 : p ≤ 5 := by
        have : p - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hpsub
        omega
      have hp2le : 2 ≤ p := hp.two_le
      -- φ(p^k) ∣ 4.
      have htk : Nat.totient (p ^ k) ∣ 4 := by
        have hd := Nat.totient_dvd_of_dvd hpk
        rwa [h] at hd
      rw [Nat.totient_prime_pow hp hkpos] at htk
      -- Case on p ∈ {2,3,4,5}; p = 4 is not prime.
      interval_cases p
      · -- p = 2 : 2^(k-1) ∣ 4 ⇒ k ≤ 3 ⇒ 2^k ∣ 120.
        have hle : (2 : ℕ) ^ (k - 1) * (2 - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) htk
        have hb : (2 : ℕ) ^ (k - 1) ≤ 4 := by simpa using hle
        have hk3 : k ≤ 3 := by
          by_contra hc
          have h3 : (2 : ℕ) ^ 3 ≤ 2 ^ (k - 1) := pow_le_pow_right' (by norm_num) (by omega)
          have : (8 : ℕ) ≤ 4 := by
            calc (8 : ℕ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (k - 1) := h3
              _ ≤ 4 := hb
          omega
        exact dvd_trans (pow_dvd_pow 2 hk3) (by norm_num)
      · -- p = 3 : 3^(k-1) ∣ 2 ⇒ k ≤ 1 ⇒ 3^k ∣ 120.
        have hle : (3 : ℕ) ^ (k - 1) * (3 - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) htk
        have hb : (3 : ℕ) ^ (k - 1) ≤ 2 := by
          have h2 : (3 : ℕ) ^ (k - 1) * 2 ≤ 4 := by simpa using hle
          omega
        have hk1 : k ≤ 1 := by
          by_contra hc
          have h1 : (3 : ℕ) ^ 1 ≤ 3 ^ (k - 1) := pow_le_pow_right' (by norm_num) (by omega)
          have : (3 : ℕ) ≤ 2 := by
            calc (3 : ℕ) = 3 ^ 1 := by norm_num
              _ ≤ 3 ^ (k - 1) := h1
              _ ≤ 2 := hb
          omega
        exact dvd_trans (pow_dvd_pow 3 hk1) (by norm_num)
      · -- p = 4 : not prime.
        exact absurd hp (by decide)
      · -- p = 5 : 5^(k-1) ∣ 1 ⇒ k ≤ 1 ⇒ 5^k ∣ 120.
        have hle : (5 : ℕ) ^ (k - 1) * (5 - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) htk
        have hb : (5 : ℕ) ^ (k - 1) ≤ 1 := by
          have h2 : (5 : ℕ) ^ (k - 1) * 4 ≤ 4 := by simpa using hle
          omega
        have hk1 : k ≤ 1 := by
          by_contra hc
          have h1 : (5 : ℕ) ^ 1 ≤ 5 ^ (k - 1) := pow_le_pow_right' (by norm_num) (by omega)
          have : (5 : ℕ) ≤ 1 := by
            calc (5 : ℕ) = 5 ^ 1 := by norm_num
              _ ≤ 5 ^ (k - 1) := h1
              _ ≤ 1 := hb
          omega
        exact dvd_trans (pow_dvd_pow 5 hk1) (by norm_num)
    -- n ∣ 120 : finite check over the divisors of 120.
    have hmem : n ∈ Nat.divisors 120 := Nat.mem_divisors.mpr ⟨hdvd120, by norm_num⟩
    fin_cases hmem <;> revert h <;> decide
  · rintro (rfl | rfl | rfl | rfl) <;> decide

/-- **Full classification of the quadratic real subfields (#8).**  For every `n ≥ 3`,
`[ℚ(2cos 2π/n):ℚ] = 2` iff `n ∈ {5,8,10,12}` — exactly the four `n` with `φ(n) = 4`.
The pentagon's golden field `ℚ(√5)` is the `n = 5` (and `n = 10`) member. -/
theorem quadratic_iff_mem {n : ℕ} (hn : 3 ≤ n) :
    (minpoly ℚ (spectralGen n)).natDegree = 2 ↔ n = 5 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
  rw [quadratic_iff_totient_four hn, totient_eq_four_iff]

/-- **The pentagon is quadratic.**  `n = 5` gives a real quadratic subfield — the
golden field `ℚ(√5)` (`GaloisWhyFive.degree_five` / `spectralGen_five`). -/
theorem pentagon_quadratic : (minpoly ℚ (spectralGen 5)).natDegree = 2 :=
  (quadratic_iff_mem (by norm_num)).mpr (by tauto)

end Brockian.CyclotomicRealDegree
