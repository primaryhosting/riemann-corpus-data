import Mathlib
/-!
# Squarefree count via the Möbius sieve.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib`; no non-core/Archive
namespaces or invented lemmas.
-/
namespace BrockianSieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `∑_{d ∣ n} μ d = 1` if `n = 1` and `0` otherwise. -/
private lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f => f n) (ArithmeticFunction.moebius_mul_coe_zeta)
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun a b => (μ a : ℤ) * ((zeta : ArithmeticFunction ℤ) b))] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Nat.mem_divisors] at hd
  have hne : n / d ≠ 0 := by
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hd.2)
    exact Nat.div_ne_zero_iff.mpr ⟨by omega, Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1⟩
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hne]

/-- If `n = a ^ 2 * b` with `b` squarefree, then `d ^ 2 ∣ n ↔ d ∣ a`. -/
private lemma sq_dvd_iff_dvd {n a b d : ℕ} (hn : n ≠ 0) (h : n = a ^ 2 * b)
    (hb : Squarefree b) : d ^ 2 ∣ n ↔ d ∣ a := by
  have ha : a ≠ 0 := by rintro rfl; simp [h] at hn
  have hb0 : b ≠ 0 := by rintro rfl; simp [h] at hn
  constructor
  · intro hd
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
    rw [← Nat.factorization_le_iff_dvd hd0 ha]
    intro p
    have h2 : (d ^ 2).factorization p ≤ n.factorization p :=
      (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hn).mpr hd p
    have hbp : b.factorization p ≤ 1 := hb.natFactorization_le_one p
    rw [h, Nat.factorization_mul (pow_ne_zero 2 ha) hb0] at h2
    simp [Nat.factorization_pow] at h2 ⊢
    omega
  · intro hd
    exact h ▸ Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd 2) b

/-- The Möbius sum over all `d` with `d ^ 2 ∣ n` is the squarefree indicator of `n`. -/
private lemma sum_moebius_sq_dvd {x n : ℕ} (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ)
      = if Squarefree n then 1 else 0 := by
  have hn : n ≠ 0 := by omega
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  -- `n = b ^ 2 * a` with `a` squarefree
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; omega
  have hkey : ∀ d : ℕ, d ^ 2 ∣ n ↔ d ∣ b := fun d => sq_dvd_iff_dvd hn hab.symm ha
  have hset : (Finset.Icc 1 x).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, hkey d]
    constructor
    · rintro ⟨-, hd⟩; exact ⟨hd, hb0⟩
    · rintro ⟨hd, -⟩
      refine ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hb0), ?_⟩, hd⟩
      have hdb : d ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hd
      have hbn : b ≤ n := by
        calc b ≤ b ^ 2 := by nlinarith [Nat.one_le_iff_ne_zero.mpr hb0]
          _ ≤ b ^ 2 * a := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ha0)
          _ = n := hab
      omega
  rw [hset, sum_moebius_divisors]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · rintro rfl
    simpa using hab ▸ (by simpa using ha : Squarefree (1 ^ 2 * a))
  · intro hsf
    have hbb : b * b ∣ n := by rw [← hab]; exact ⟨a, by ring⟩
    exact Nat.isUnit_iff.mp (hsf b hbb)

/-- The number of squarefree integers in `[1, x]` equals `∑_{d : d^2 ≤ x} μ(d) ⌊x / d^2⌋`.
(Sanity: `x = 10`: LHS `#{1,2,3,5,6,7,10} = 7`; RHS `= 10 − ⌊10/4⌋ − ⌊10/9⌋ = 10 − 2 − 1 = 7`.)
Proof idea: `μ(d)^2 = ∑_{e^2 ∣ d} μ(e)` (squarefree indicator) summed over `d ≤ x`, then swap
the order of summation grouping by `e`. -/
theorem squarefree_count (x : ℕ) :
    (((Finset.Icc 1 x).filter Squarefree).card : ℤ)
      = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ≤ x),
          ArithmeticFunction.moebius d * ((x / d ^ 2 : ℕ) : ℤ) := by
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by ext n; simp; omega
  -- `⌊x / d ^ 2⌋` counts the multiples of `d ^ 2` in `[1, x]`
  have hdiv : ∀ d : ℕ, ((x / d ^ 2 : ℕ) : ℤ)
      = (((Finset.Icc 1 x).filter (fun n => d ^ 2 ∣ n)).card : ℤ) := by
    intro d
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  calc (((Finset.Icc 1 x).filter Squarefree).card : ℤ)
      = ∑ n ∈ Finset.Icc 1 x, (if Squarefree n then (1 : ℤ) else 0) := by simp
    _ = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        simp only [Finset.mem_Icc] at hn
        rw [sum_moebius_sq_dvd hn.1 hn.2]
    _ = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x, (if d ^ 2 ∣ n then (μ d : ℤ) else 0) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_filter _ _
    _ = ∑ d ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x, (if d ^ 2 ∣ n then (μ d : ℤ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ≤ x),
          ArithmeticFunction.moebius d * ((x / d ^ 2 : ℕ) : ℤ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hdiv d, ← Finset.sum_filter]
        by_cases h : d ^ 2 ≤ x
        · simp only [h, if_true]
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        · simp only [h, if_false]
          have hemp : (Finset.Icc 1 x).filter (fun n => d ^ 2 ∣ n) = ∅ := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
            rintro ⟨hn1, hnx⟩ hdvd
            exact h (le_trans (Nat.le_of_dvd (by omega) hdvd) hnx)
          simp [hemp]

end BrockianSieve

