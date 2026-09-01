import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/
theorem negMulLog_le_sub (x r : ℝ) (hx : 0 ≤ x) (hr : 0 < r) :
    Real.negMulLog x ≤ (r - x) + x * (-Real.log r) := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [Real.negMulLog, ← h]; linarith
  · have h1 : Real.log (r / x) ≤ r / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (r / x) = Real.log r - Real.log x :=
      Real.log_div (ne_of_gt hr) (ne_of_gt h)
    have h3 := mul_le_mul_of_nonneg_left h1 hx
    rw [h2] at h3
    have hxx : x * (r / x - 1) = r - x := by field_simp
    rw [hxx] at h3
    simp only [Real.negMulLog]
    nlinarith

/-- **Gibbs' inequality.**  The Shannon entropy of a probability vector `p` is bounded by its
cross-entropy against any positive sub-probability reference vector `r`. -/
theorem entropy_le_of_reference {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) (hrsum : ∑ i, r i ≤ 1) :
    ∑ i, Real.negMulLog (p i) ≤ ∑ i, p i * (-Real.log (r i)) := by
  have h : ∑ i, Real.negMulLog (p i)
      ≤ ∑ i : Fin N, ((r i - p i) + p i * (-Real.log (r i))) :=
    Finset.sum_le_sum (fun i _ => negMulLog_le_sub (p i) (r i) (hp i) (hr i))
  refine h.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum]
  linarith

/-! ## Rearrangement facts -/

/-- A strictly monotone map between `Fin` types cannot decrease indices. -/
theorem fin_le_of_strictMono {n m : ℕ} {f : Fin n → Fin m} (hf : StrictMono f) (a : Fin n) :
    (a : ℕ) ≤ (f a : ℕ) := by
  obtain ⟨x, hx⟩ := a
  induction x with
  | zero => simp
  | succ y ih =>
      have hy : y < n := by omega
      have h1 : (f ⟨y, hy⟩ : ℕ) < (f ⟨y + 1, hx⟩ : ℕ) := hf (by simp [Fin.lt_def])
      have h2 := ih hy
      simp only at *
      omega

/-- Sum over a finset of `Fin N`, re-expressed along its monotone enumeration. -/
theorem sum_eq_sum_orderEmb {N : ℕ} (t : Finset (Fin N)) (p : Fin N → ℝ) :
    ∑ i ∈ t, p i = ∑ a : Fin t.card, p (t.orderEmbOfFin rfl a) := by
  have h : t = Finset.map (t.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · intro hi
      have hr : i ∈ Set.range (t.orderEmbOfFin (rfl : t.card = t.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hi
      obtain ⟨a, ha⟩ := hr
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩; exact Finset.orderEmbOfFin_mem t rfl a
  conv_lhs => rw [h]
  rw [Finset.sum_map]
  rfl

/-- Sum over the first `j` indices, written as a sum over `Fin j`. -/
theorem sum_castLE_eq {N j : ℕ} (h : j ≤ N) (p : Fin N → ℝ) :
    ∑ a : Fin j, p (Fin.castLE h a)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), p i := by
  have hset : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j))
      = Finset.map ⟨Fin.castLE h, Fin.castLE_injective h⟩ (Finset.univ : Finset (Fin j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, by simp⟩
    · rintro ⟨a, rfl⟩; simp
  rw [hset, Finset.sum_map]
  rfl

/-- For a nonincreasing nonnegative vector, no set of at most `k` indices carries more
weight than the first `k` indices. -/
theorem sum_le_sum_first {N : ℕ} {p : Fin N → ℝ} (hanti : Antitone p) (hp : ∀ i, 0 ≤ p i)
    (t : Finset (Fin N)) (k : ℕ) (hcard : t.card ≤ k) :
    ∑ i ∈ t, p i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), p i := by
  have hjN : t.card ≤ N := by simpa using Finset.card_le_univ t
  rw [sum_eq_sum_orderEmb t p]
  have step1 : ∑ a : Fin t.card, p (t.orderEmbOfFin rfl a)
      ≤ ∑ a : Fin t.card, p (Fin.castLE hjN a) := by
    refine Finset.sum_le_sum (fun a _ => hanti ?_)
    exact (Fin.le_def).2 (fin_le_of_strictMono (t.orderEmbOfFin rfl).strictMono a)
  refine step1.trans ?_
  rw [sum_castLE_eq hjN p]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hp i)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  omega

/-! ## Layer-cake identities -/

/-- Weighted layer-cake identity: a weighted mean is the weighted sum of the tail masses. -/
theorem weighted_layer_cake {N : ℕ} (p : Fin N → ℝ) (w : ℕ → ℝ) :
    ∑ i : Fin N, (∑ k ∈ Finset.Ico 1 ((i : ℕ) + 1), w k) * p i
      = ∑ k ∈ Finset.Ico 1 N, w k
          * ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (s' := fun i : Fin N => Finset.Ico 1 ((i : ℕ) + 1))
      (t' := (Finset.univ : Finset (Fin N)))]
  intro k i
  have hi := i.isLt
  simp only [Finset.mem_Ico, Finset.mem_univ, Finset.mem_filter, true_and, and_true]
  omega

/-- Layer-cake identity: the mean index equals the sum of the tail masses. -/
theorem mean_eq_sum_tails {N : ℕ} (p : Fin N → ℝ) :
    ∑ i : Fin N, (i : ℝ) * p i
      = ∑ k ∈ Finset.Ico 1 N, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i := by
  have h := weighted_layer_cake p (fun _ => (1 : ℝ))
  simpa using h

/-! ## Entropy bounds from decaying tails -/

/-- Exponentially decaying tails force a bounded mean index. -/
theorem mean_le_of_tail_decay {N : ℕ} (p : Fin N → ℝ) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i ≤ C * q ^ k) :
    ∑ i : Fin N, (i : ℝ) * p i ≤ C * q / (1 - q) := by
  rw [mean_eq_sum_tails]
  calc ∑ k ∈ Finset.Ico 1 N, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      ≤ ∑ k ∈ Finset.Ico 1 N, C * q ^ k := Finset.sum_le_sum (fun k _ => htail k)
    _ ≤ C * q / (1 - q) := by
        have hrw : ∑ k ∈ Finset.Ico 1 N, C * q ^ k
            = ∑ k ∈ Finset.range (N - 1), (C * q) * q ^ k := by
          rw [Finset.sum_Ico_eq_sum_range]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [hrw]
        have hs : Summable (fun k : ℕ => (C * q) * q ^ k) :=
          (summable_geometric_of_lt_one hq0.le hq1).mul_left (C * q)
        refine (hs.sum_le_tsum _ (fun k _ => by positivity)).trans ?_
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
        ring_nf
        rfl

/-- **Entropy estimate for geometrically decaying tails.**  A probability vector whose
index-`k` tail mass is at most `C q ^ k` has Shannon entropy at most
`C q / (1 - q) * log (1/q) + log (1/(1-q))`: a bound depending only on `C` and `q`, in
particular independent of the dimension `N`. -/
theorem entropy_le_of_tail_decay {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i ≤ C * q ^ k) :
    ∑ i, Real.negMulLog (p i) ≤ (C * q / (1 - q)) * Real.log (1 / q) + Real.log (1 / (1 - q)) := by
  have hq1' : 0 < 1 - q := by linarith
  set r : Fin N → ℝ := fun i => (1 - q) * q ^ (i : ℕ) with hrdef
  have hr : ∀ i, 0 < r i := fun i => by rw [hrdef]; positivity
  have hrsum : ∑ i, r i ≤ 1 := by
    rw [hrdef, ← Finset.mul_sum]
    have h3 : ∑ i : Fin N, q ^ (i : ℕ) = ∑ i ∈ Finset.range N, q ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => q ^ i) N
    rw [h3, geom_sum_eq (by linarith)]
    have hne : q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    have h4 : (1 - q) * ((q ^ N - 1) / (q - 1)) = 1 - q ^ N := by
      field_simp
      linarith [sq_nonneg q]
    rw [h4]
    nlinarith [pow_nonneg hq0.le N]
  refine (entropy_le_of_reference p hp hsum r hr hrsum).trans ?_
  have hlogr : ∀ i : Fin N,
      -Real.log (r i) = (i : ℕ) * Real.log (1 / q) + Real.log (1 / (1 - q)) := by
    intro i
    rw [hrdef]
    simp only
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_div one_ne_zero (by positivity)]
    simp
  have hsplit : ∑ i : Fin N, p i * (-Real.log (r i))
      = (∑ i : Fin N, (i : ℝ) * p i) * Real.log (1 / q)
        + (∑ i : Fin N, p i) * Real.log (1 / (1 - q)) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hlogr i]; ring)
  rw [hsplit, hsum, one_mul]
  have hlogq : 0 ≤ Real.log (1 / q) := Real.log_nonneg (by rw [le_div_iff₀ hq0]; linarith)
  have hmean := mean_le_of_tail_decay p hq0 hq1 hC htail
  nlinarith [hmean]

/-- `log (i+1)` is bounded by the `i`-th harmonic number. -/
theorem log_le_harmonic (i : ℕ) : Real.log ((i : ℝ) + 1) ≤ ∑ k ∈ Finset.Ico 1 (i + 1), (1 / (k : ℝ)) := by
  induction i with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have h1 : Real.log ((j : ℝ) + 1 + 1) - Real.log ((j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
        have h0 := Real.log_le_sub_one_of_pos (x := ((j : ℝ) + 1 + 1) / ((j : ℝ) + 1))
          (by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h0
        have h2 : ((j : ℝ) + 1 + 1) / ((j : ℝ) + 1) - 1 = 1 / ((j : ℝ) + 1) := by
          field_simp; ring
        linarith [h0, h2.le, h2.ge]
      push_cast
      push_cast at ih
      linarith

/-- Telescoping bound `∑_{k=1}^{N-1} 1/(k(k+1)) ≤ 1`. -/
theorem harmonic_tail_sum_le (N : ℕ) :
    ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ)) * (1 / ((k : ℝ) + 1)) ≤ 1 := by
  have key : ∀ M : ℕ, ∑ k ∈ Finset.Ico 1 M, (1 / (k : ℝ)) * (1 / ((k : ℝ) + 1))
      ≤ 1 - 1 / (max M 1 : ℕ) := by
    intro M
    induction M with
    | zero => simp
    | succ j ih =>
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj; simp
        · rw [Finset.sum_Ico_succ_top (by omega)]
          have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
          have hm : ((max j 1 : ℕ) : ℝ) = (j : ℝ) := by rw [Nat.max_eq_left hj]
          rw [hm] at ih
          have hm2 : ((max (j + 1) 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
            rw [Nat.max_eq_left (by omega)]; push_cast; ring
          rw [hm2]
          have hsplit : (1 / (j : ℝ)) * (1 / ((j : ℝ) + 1)) = 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) := by
            field_simp; ring
          rw [hsplit]
          linarith
  refine (key N).trans ?_
  have h1 : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
  have h2 : 0 < 1 / ((max N 1 : ℕ) : ℝ) := by positivity
  linarith

/-- Partial sums of `∑ 1/(i+1)^2` are bounded by `2`. -/
theorem sum_inv_sq_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1) ^ 2) ≤ 2 - 1 / ((max N 1 : ℕ) : ℝ) := by
  induction N with
  | zero => norm_num
  | succ j ih =>
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; norm_num
      · rw [Finset.sum_range_succ]
        have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        have hm : ((max j 1 : ℕ) : ℝ) = (j : ℝ) := by rw [Nat.max_eq_left hj]
        rw [hm] at ih
        have hm2 : ((max (j + 1) 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
          rw [Nat.max_eq_left (by omega)]; push_cast; ring
        rw [hm2]
        have hkey : 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) := by
          have h1 : 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) = 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
            field_simp; ring
          rw [h1]
          apply one_div_le_one_div_of_le
          · positivity
          · nlinarith
        linarith

/-- The logarithmic mean is bounded when the tails decay like `C/(k+1)`. -/
theorem log_mean_le_of_harmonic_tail_decay {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) {C : ℝ}
    (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      ≤ C / ((k : ℝ) + 1)) :
    ∑ i : Fin N, p i * Real.log (((i : ℕ) : ℝ) + 1) ≤ C := by
  calc ∑ i : Fin N, p i * Real.log (((i : ℕ) : ℝ) + 1)
      ≤ ∑ i : Fin N, (∑ k ∈ Finset.Ico 1 ((i : ℕ) + 1), (1 / (k : ℝ))) * p i := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (log_le_harmonic (i : ℕ)) (hp i)
    _ = ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ))
          * ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i :=
        weighted_layer_cake p (fun k => 1 / (k : ℝ))
    _ ≤ ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ)) * (C / ((k : ℝ) + 1)) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hk : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (htail k) hk
    _ = C * ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ)) * (1 / ((k : ℝ) + 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ C := by nlinarith [harmonic_tail_sum_le N]

/-- **Entropy estimate for inverse-linearly decaying tails.**  If the index-`k` tail mass of a
probability vector is at most `C/(k+1)`, its Shannon entropy is at most `log 2 + 2 C`, a bound
independent of the dimension `N`.  (This hypothesis is much weaker than geometric decay.) -/
theorem entropy_le_of_harmonic_tail_decay {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      ≤ C / ((k : ℝ) + 1)) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log 2 + 2 * C := by
  set r : Fin N → ℝ := fun i => (1 / 2) * (1 / (((i : ℕ) : ℝ) + 1) ^ 2) with hrdef
  have hr : ∀ i, 0 < r i := fun i => by rw [hrdef]; positivity
  have hrsum : ∑ i, r i ≤ 1 := by
    rw [hrdef, ← Finset.mul_sum]
    have h : ∑ i : Fin N, (1 / (((i : ℕ) : ℝ) + 1) ^ 2)
        = ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1) ^ 2) :=
      Fin.sum_univ_eq_sum_range (fun i => 1 / ((i : ℝ) + 1) ^ 2) N
    rw [h]
    have h2 := sum_inv_sq_le N
    have h3 : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
    have h4 : 0 < 1 / ((max N 1 : ℕ) : ℝ) := by positivity
    linarith
  refine (entropy_le_of_reference p hp hsum r hr hrsum).trans ?_
  have hlogr : ∀ i : Fin N,
      -Real.log (r i) = Real.log 2 + 2 * Real.log (((i : ℕ) : ℝ) + 1) := by
    intro i
    rw [hrdef]
    simp only
    rw [Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_div one_ne_zero (by positivity)]
    rw [Real.log_pow]
    simp
    ring
  have hsplit : ∑ i : Fin N, p i * (-Real.log (r i))
      = (∑ i : Fin N, p i) * Real.log 2
        + 2 * ∑ i : Fin N, p i * Real.log (((i : ℕ) : ℝ) + 1) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hlogr i]; ring)
  rw [hsplit, hsum, one_mul]
  have := log_mean_le_of_harmonic_tail_decay p hp hC htail
  linarith

/-! ## Bipartite entanglement entropy -/

section Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

/-- The **Schmidt spectrum** of a bipartite pure state `psi : Matrix A B ℂ` (the state
`∑ a b, psi a b • |a⟩ ⊗ |b⟩`): the eigenvalues of the reduced density matrix `psi * psiᴴ` on
the left factor, i.e. the squared Schmidt coefficients. -/
noncomputable def schmidtSpectrum (psi : Matrix A B ℂ) : A → ℝ :=
  (Matrix.isHermitian_mul_conjTranspose_self psi).eigenvalues

/-- The **entanglement entropy** of a bipartite pure state: the von Neumann entropy
`-∑ λ log λ` of its reduced density matrix. -/
noncomputable def entanglementEntropy (psi : Matrix A B ℂ) : ℝ :=
  ∑ i, Real.negMulLog (schmidtSpectrum psi i)

theorem schmidtSpectrum_nonneg (psi : Matrix A B ℂ) (i : A) : 0 ≤ schmidtSpectrum psi i :=
  (Matrix.posSemidef_self_mul_conjTranspose psi).eigenvalues_nonneg i

theorem sum_schmidtSpectrum (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1) :
    ∑ i, schmidtSpectrum psi i = 1 := by
  have h := (Matrix.isHermitian_mul_conjTranspose_self psi).trace_eq_sum_eigenvalues
  rw [hnorm] at h
  have h2 : ((∑ i, schmidtSpectrum psi i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    simp only [schmidtSpectrum]
    push_cast
    exact h.symm
  exact_mod_cast h2

/-- Sorting a spectrum: truncation bounds by arbitrary index sets are equivalent to tail bounds
for the nonincreasing rearrangement. -/
theorem exists_sorted_tails (lam : A → ℝ) (hnn : ∀ i, 0 ≤ lam i) (hs1 : ∑ i, lam i = 1)
    (f : ℕ → ℝ)
    (hdecay : ∀ k : ℕ, ∃ s : Finset A, s.card ≤ k ∧ ∑ i ∈ sᶜ, lam i ≤ f k) :
    ∃ e : Fin (Fintype.card A) ≃ A, ∀ k : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card A) => k ≤ (i : ℕ)), lam (e i) ≤ f k := by
  classical
  set N := Fintype.card A with hN
  obtain ⟨e, hanti⟩ : ∃ e : Fin N ≃ A, Antitone (fun i => lam (e i)) := by
    let g : Fin N ≃ A := (Fintype.equivFin A).symm
    let f0 : Fin N → ℝ := fun i => -lam (g i)
    refine ⟨(Tuple.sort f0).trans g, ?_⟩
    have hm : Monotone (f0 ∘ (Tuple.sort f0)) := Tuple.monotone_sort f0
    intro a b hab
    have h := hm hab
    simp only [Function.comp_apply, f0, neg_le_neg_iff] at h
    simpa [Equiv.trans] using h
  refine ⟨e, ?_⟩
  set p : Fin N → ℝ := fun i => lam (e i) with hp
  have hpnn : ∀ i, 0 ≤ p i := fun i => hnn _
  have hpsum : ∑ i, p i = 1 := by rw [← hs1]; exact Equiv.sum_comp e lam
  intro k
  obtain ⟨s, hs, hsum⟩ := hdecay k
  set t : Finset (Fin N) := s.map e.symm.toEmbedding with ht
  have hcard : t.card ≤ k := by simpa [ht] using hs
  have hts : ∑ i ∈ t, p i = ∑ a ∈ s, lam a := by
    rw [ht, Finset.sum_map]
    exact Finset.sum_congr rfl (fun a _ => by simp [hp])
  have hsplit : ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      = 1 - ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), p i := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N))
      (fun i : Fin N => (i : ℕ) < k) p
    rw [hpsum] at h
    have hcongr : (Finset.univ.filter (fun i : Fin N => ¬ ((i : ℕ) < k)))
        = Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)) := by
      ext i; simp
    rw [hcongr] at h
    linarith
  have hdom := sum_le_sum_first hanti hpnn t k hcard
  have hcompl : ∑ i ∈ sᶜ, lam i = 1 - ∑ a ∈ s, lam a := by
    have h := Finset.sum_add_sum_compl s lam
    rw [hs1] at h
    linarith
  rw [hsplit]
  rw [hts] at hdom
  rw [hcompl] at hsum
  linarith

theorem entanglementEntropy_eq_reindex (psi : Matrix A B ℂ) (e : Fin (Fintype.card A) ≃ A) :
    entanglementEntropy psi = ∑ i, Real.negMulLog (schmidtSpectrum psi (e i)) :=
  (Equiv.sum_comp e (fun a => Real.negMulLog (schmidtSpectrum psi a))).symm

/-- If the state can be truncated to `k` Schmidt vectors with discarded weight at most `C q ^ k`,
its entanglement entropy is bounded by an explicit constant depending only on `C` and `q`. -/
theorem entropy_le_of_schmidt_decay (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1)
    {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hdecay : ∀ k : ℕ, ∃ s : Finset A, s.card ≤ k ∧
      ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C * q ^ k) :
    entanglementEntropy psi ≤ (C * q / (1 - q)) * Real.log (1 / q) + Real.log (1 / (1 - q)) := by
  classical
  have hnn := schmidtSpectrum_nonneg psi
  have hs1 := sum_schmidtSpectrum psi hnorm
  have hC : 0 ≤ C := by
    obtain ⟨s, hs, hsum⟩ := hdecay 0
    have hse : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    rw [hse] at hsum
    simp only [Finset.compl_empty, pow_zero, mul_one] at hsum
    rw [hs1] at hsum
    linarith
  obtain ⟨e, htail⟩ := exists_sorted_tails (schmidtSpectrum psi) hnn hs1 (fun k => C * q ^ k) hdecay
  rw [entanglementEntropy_eq_reindex psi e]
  refine entropy_le_of_tail_decay (fun i => schmidtSpectrum psi (e i)) (fun i => hnn _) ?_
    hq0 hq1 hC htail
  rw [← hs1]
  exact Equiv.sum_comp e (schmidtSpectrum psi)

/-- **Entropy bound from inverse-linear Schmidt truncation error.**  If for every `k` the state
can be truncated to `k` Schmidt vectors with discarded weight at most `C/(k+1)`, then its
entanglement entropy is at most `log 2 + 2 C`: a constant depending only on `C`, independent of
the dimensions of the two factors. -/
theorem entropy_le_of_schmidt_truncation (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1)
    {C : ℝ}
    (hdecay : ∀ k : ℕ, ∃ s : Finset A, s.card ≤ k ∧
      ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C / ((k : ℝ) + 1)) :
    entanglementEntropy psi ≤ Real.log 2 + 2 * C := by
  classical
  have hnn := schmidtSpectrum_nonneg psi
  have hs1 := sum_schmidtSpectrum psi hnorm
  have hC : 0 ≤ C := by
    obtain ⟨s, hs, hsum⟩ := hdecay 0
    have hse : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    rw [hse] at hsum
    simp only [Finset.compl_empty, Nat.cast_zero, zero_add, div_one] at hsum
    rw [hs1] at hsum
    linarith
  obtain ⟨e, htail⟩ :=
    exists_sorted_tails (schmidtSpectrum psi) hnn hs1 (fun k => C / ((k : ℝ) + 1)) hdecay
  rw [entanglementEntropy_eq_reindex psi e]
  refine entropy_le_of_harmonic_tail_decay (fun i => schmidtSpectrum psi (e i)) (fun i => hnn _) ?_
    hC htail
  rw [← hs1]
  exact Equiv.sum_comp e (schmidtSpectrum psi)

/-- **Consistency of the truncation hypothesis.**  Every normalized bipartite pure state admits
a truncation bound with *some* constant; the content of the area law is that for gapped
one-dimensional chains the constant can be chosen independently of the system size.  In
particular the hypothesis of `Phys.area_law_1d` is satisfiable. -/
theorem schmidt_truncation_of_finite_dim (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1)
    (k : ℕ) :
    ∃ s : Finset A, s.card ≤ k ∧
      ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ ((Fintype.card A : ℝ) + 1) / ((k : ℝ) + 1) := by
  classical
  by_cases h : Fintype.card A ≤ k
  · refine ⟨Finset.univ, by simpa using h, ?_⟩
    simp only [Finset.compl_univ, Finset.sum_empty]
    positivity
  · refine ⟨∅, by simp, ?_⟩
    rw [Finset.compl_empty, sum_schmidtSpectrum psi hnorm]
    push_neg at h
    have hk : ((k : ℝ) + 1) ≤ (Fintype.card A : ℝ) + 1 := by
      have : (k : ℝ) ≤ (Fintype.card A : ℝ) := by exact_mod_cast h.le
      linarith
    rw [le_div_iff₀ (by positivity)]
    linarith

end Bipartite

/-! ## The one-dimensional area law -/

/--
**Area law for gapped one-dimensional systems (Hastings).**

Setting: a spin chain of `n` sites with local Hilbert space dimension `d`, cut into the left
block (sites `0, …, m-1`) and the right block (the remaining `n - m` sites).  A pure state of
the chain is a matrix `psi` indexed by the configurations of the two blocks, normalized by
`tr (psi psiᴴ) = 1`; its entanglement entropy across the cut is the von Neumann entropy of the
reduced density matrix `psi psiᴴ`.

Hypothesis (the gap input): for the ground state of a gapped local one-dimensional Hamiltonian,
truncating the Schmidt decomposition across any cut to `k` terms leaves a discarded weight that
tends to `0` at a rate `C/(k+1)` with a constant `C` fixed by the gap and the local dimension,
uniformly in the system size.  This is the analytic content supplied by Hastings' theorem and by
the approximate-ground-state-projector construction of Arad–Kitaev–Landau–Vazirani (which in
fact yields a faster, polynomially decaying truncation error); it is hypothesis `hdecay` below.

Conclusion (the area law): there is a single constant `K`, depending only on `C` and **not** on
the chain length `n`, the position `m` of the cut, or the total Hilbert space dimension, that
bounds the entanglement entropy across every cut of every such chain.  In one dimension the
boundary of a cut is a single point, so a size-independent constant bound is exactly the
statement of the area law.
-/
theorem area_law_1d (d : ℕ) (C : ℝ) :
    ∃ K : ℝ, ∀ (n m : ℕ) (psi : Matrix (Fin m → Fin d) (Fin (n - m) → Fin d) ℂ),
      (psi * psiᴴ).trace = 1 →
      (∀ k : ℕ, ∃ s : Finset (Fin m → Fin d), s.card ≤ k ∧
          ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C / ((k : ℝ) + 1)) →
      entanglementEntropy psi ≤ K := by
  refine ⟨Real.log 2 + 2 * C, ?_⟩
  intro n m psi hnorm hdecay
  exact entropy_le_of_schmidt_truncation psi hnorm hdecay

/-- Variant of the area law under the stronger hypothesis of geometrically decaying Schmidt
truncation error. -/
theorem area_law_1d_geometric (d : ℕ) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, ∀ (n m : ℕ) (psi : Matrix (Fin m → Fin d) (Fin (n - m) → Fin d) ℂ),
      (psi * psiᴴ).trace = 1 →
      (∀ k : ℕ, ∃ s : Finset (Fin m → Fin d), s.card ≤ k ∧
          ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C * q ^ k) →
      entanglementEntropy psi ≤ K := by
  refine ⟨(C * q / (1 - q)) * Real.log (1 / q) + Real.log (1 / (1 - q)), ?_⟩
  intro n m psi hnorm hdecay
  exact entropy_le_of_schmidt_decay psi hnorm hq0 hq1 hdecay

end Phys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

