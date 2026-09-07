/-
  Brockian/GaloisGeneralDegree.lean — the GENERAL Galois-degree "why five".

  `Brockian/GaloisWhyFive.lean` computes `[ℚ(2cos(2π/p)):ℚ]` for the concrete
  primes `p ∈ {3, 5, 7}` (degrees `1, 2, 3`), leaving the general theorem OPEN.
  This file closes it: for EVERY odd prime `p`,

        `[ℚ(2cos(2π/p)) : ℚ] = (p − 1) / 2`,

  the degree of the maximal real subfield `ℚ(ζ_p)⁺ = ℚ(ζ_p + ζ_p⁻¹)` of the
  `p`-th cyclotomic field.  The golden quadratic (`= 2`) is then forced for
  exactly one prime — `p = 5` — as a general theorem, not just a `{3,5,7}` check.

  ## Proof architecture (the classical tower, made executable)

  With `ζ = exp(2πi/p)` (`Complex.isPrimitiveRoot_exp`) and `α = ζ + ζ⁻¹`:

    * `[ℚ(ζ):ℚ] = p − 1`         — cyclotomic degree
                                   (`cyclotomic_eq_minpoly_rat` + `natDegree_cyclotomic`
                                    + `Nat.totient_prime`).
    * `ζ ∉ ℚ(α)`                 — complex conjugation fixes all of `ℚ(α)`
                                   (`adjoin_induction`; `α` is real, `conj ζ = ζ⁻¹`),
                                   but fixing `ζ` would force `ζ² = 1`, impossible for
                                   an odd prime order.  This is the degree-2 step, PROVED
                                   (not assumed).
    * `[ℚ(ζ):ℚ(α)] = 2`          — `ζ` is a root of the monic `X² − αX + 1` over `ℚ(α)`
                                   (`minpoly.min` ⇒ `≤ 2`) and `ζ ∉ ℚ(α)`
                                   (`minpoly.two_le_natDegree_iff` ⇒ `≥ 2`).
    * tower law                   `[ℚ(ζ):ℚ] = [ℚ(ζ):ℚ(α)] · [ℚ(α):ℚ]`
                                   (`Module.finrank_mul_finrank`, with
                                    `adjoin_simple_adjoin_simple` identifying
                                    `ℚ(α)(ζ) = ℚ(ζ)`), whence `p − 1 = 2 · [ℚ(α):ℚ]`.

  ## What is proved (AXLE-verified at lean-4.32.0, axioms ⊆
     {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`)

    * `real_subfield_degree`      — **the general theorem**: for every prime `p ≠ 2`,
                                     `[ℚ(2cos(2π/p)):ℚ] = (p−1)/2`.
    * `quadratic_iff_five_general`— **the general "why five"**: for every prime `p ≠ 2`,
                                     the spectral field is quadratic (`degree = 2`) iff `p = 5`.

  ## What is NOT proved

    * `p = 2` is excluded (there `2cos(π) = −2 ∈ ℚ`, degree 1, a degenerate boundary
      case, not the maximal-real-subfield regime).  This is the only omission; the
      odd-prime theorem is fully general.

  ## Precise remaining obstruction

    * None for the stated target.  The previously-open general degree theorem
      `[ℚ(2cos(2π/p)):ℚ] = (p−1)/2` (all odd primes) is closed here.  It rests on
      Mathlib's `Polynomial.cyclotomic.irreducible_rat` (irreducibility of the
      cyclotomic polynomial over `ℚ`), which is itself fully proved in Mathlib.
-/
import Mathlib
import Brockian.GaloisWhyFive

namespace Brockian.GaloisGeneralDegree

open Polynomial
open scoped IntermediateField

/-- **General degree of the spectral field.**  For every prime `p ≠ 2`,
`[ℚ(2cos(2π/p)) : ℚ] = (p − 1)/2` — the degree of the maximal real subfield
`ℚ(ζ_p)⁺` of the `p`-th cyclotomic field.  Extends the `{3,5,7}` computations of
`GaloisWhyFive` to a theorem for all odd primes. -/
theorem real_subfield_degree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p)).natDegree = (p - 1) / 2 := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  -- The primitive p-th root of unity ζ = exp(2πi/p).
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) with hζ_def
  have hζ : IsPrimitiveRoot ζ p := by rw [hζ_def]; exact Complex.isPrimitiveRoot_exp p hp0
  have hpow : ζ ^ p = 1 := hζ.pow_eq_one
  have hz : ζ ≠ 0 := by
    intro h; rw [h, zero_pow hp0] at hpow; exact one_ne_zero hpow.symm
  have hζinv : ζ⁻¹ = ζ ^ (p - 1) := by
    have h1 : ζ * ζ ^ (p - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]; exact hpow
    exact (eq_inv_of_mul_eq_one_right h1).symm
  -- Argument identity and modulus/real-part of ζ.
  have harg : (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))
            = ((2 * Real.pi / (p : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hnorm : ‖ζ‖ = 1 := by rw [hζ_def, harg]; exact Complex.norm_exp_ofReal_mul_I _
  have hre : ζ.re = Real.cos (2 * Real.pi / (p : ℝ)) := by
    rw [hζ_def, harg]; exact Complex.exp_ofReal_mul_I_re _
  have hconjζ : (starRingEnd ℂ) ζ = ζ⁻¹ := (Complex.inv_eq_conj hnorm).symm
  -- The real spectral generator α = ζ + ζ⁻¹.
  set α : ℂ := ζ + ζ⁻¹ with hα
  -- α ∈ ℚ(α); every element of ℚ(α) is fixed by complex conjugation.
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
  -- ζ ∉ ℚ(α): otherwise conjugation fixes ζ, forcing ζ² = 1 — impossible for order p ≠ 2.
  have hζ_notin : ζ ∉ (ℚ⟮α⟯ : IntermediateField ℚ ℂ) := by
    intro hmem
    have h1 := hfix ζ hmem
    rw [hconjζ] at h1
    have hsq : ζ ^ 2 = 1 := by
      have hmc : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hz
      rw [h1] at hmc
      rw [pow_two]; exact hmc
    have hdvd : p ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp hsq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  -- α = 2 cos(2π/p) = spectralGen p (as a complex number).
  have halpha : α = ((Brockian.GaloisWhyFive.spectralGen p : ℝ) : ℂ) := by
    rw [hα, ← hconjζ, Complex.add_conj, hre]
    simp only [Brockian.GaloisWhyFive.spectralGen]
  -- Integrality.
  have hζint : IsIntegral ℚ ζ := (hζ.isIntegral hp.pos).tower_top
  have hζintK : IsIntegral (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) ζ := hζint.tower_top
  have hαint : IsIntegral ℚ α := by
    rw [hα, hζinv]; exact hζint.add (hζint.pow (p - 1))
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
  -- The tower [ℚ(α):ℚ] · [ℚ(ζ):ℚ(α)] = [ℚ(ζ):ℚ], with [ℚ(ζ):ℚ] = p − 1.
  have hdK : Module.finrank ℚ (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) = (minpoly ℚ α).natDegree :=
    IntermediateField.adjoin.finrank hαint
  have hfinM_rel : Module.finrank (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) (ℚ⟮α⟯⟮ζ⟯) = 2 := by
    rw [IntermediateField.adjoin.finrank hζintK]; exact hdeg2
  have hfinM_abs : Module.finrank ℚ (ℚ⟮α⟯⟮ζ⟯) = p - 1 := by
    have hαle : (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮ζ⟯ := by
      rw [IntermediateField.adjoin_simple_le_iff, hα]
      exact add_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ)
        (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ))
    have hMrs : (ℚ⟮α⟯⟮ζ⟯).restrictScalars ℚ = (ℚ⟮ζ⟯ : IntermediateField ℚ ℂ) :=
      (IntermediateField.restrictScalars_adjoin_eq_sup ℚ (ℚ⟮α⟯ : IntermediateField ℚ ℂ)
        ({ζ} : Set ℂ)).trans (sup_eq_right.mpr hαle)
    have hfz : Module.finrank ℚ (↥(ℚ⟮ζ⟯ : IntermediateField ℚ ℂ)) = p - 1 := by
      rw [IntermediateField.adjoin.finrank hζint, ← cyclotomic_eq_minpoly_rat hζ hp.pos,
        natDegree_cyclotomic p ℚ, Nat.totient_prime hp]
    calc Module.finrank ℚ (ℚ⟮α⟯⟮ζ⟯)
          = Module.finrank ℚ (↥((ℚ⟮α⟯⟮ζ⟯).restrictScalars ℚ)) := rfl
      _ = Module.finrank ℚ (↥(ℚ⟮ζ⟯ : IntermediateField ℚ ℂ)) := by rw [hMrs]
      _ = p - 1 := hfz
  have htower :
      Module.finrank ℚ (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ))
        * Module.finrank (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) (ℚ⟮α⟯⟮ζ⟯)
        = Module.finrank ℚ (ℚ⟮α⟯⟮ζ⟯) :=
    Module.finrank_mul_finrank ℚ (↥(ℚ⟮α⟯ : IntermediateField ℚ ℂ)) (ℚ⟮α⟯⟮ζ⟯)
  have hkey : (minpoly ℚ α).natDegree * 2 = p - 1 := by
    rw [← hdK, ← hfinM_rel, htower, hfinM_abs]
  -- Bridge the real generator's minimal polynomial to the complex one.
  have hbridge :
      (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p)).natDegree = (minpoly ℚ α).natDegree := by
    rw [halpha,
      show ((Brockian.GaloisWhyFive.spectralGen p : ℝ) : ℂ)
          = algebraMap ℝ ℂ (Brockian.GaloisWhyFive.spectralGen p) from rfl,
      minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective ℝ ℂ)]
  rw [hbridge]
  omega

/-- **General "why five".**  For every prime `p ≠ 2`, the spectral field
`ℚ(2cos(2π/p))` is a quadratic field (`[ℚ(2cos(2π/p)):ℚ] = 2`) if and only if
`p = 5`.  The pentagon's golden field `ℚ(√5)` is the unique real-quadratic
spectral field among all primes — not merely among `{3,5,7}`. -/
theorem quadratic_iff_five_general {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p)).natDegree = 2 ↔ p = 5 := by
  rw [real_subfield_degree hp hp2]
  obtain ⟨k, rfl⟩ := hp.odd_of_ne_two hp2
  omega

end Brockian.GaloisGeneralDegree
