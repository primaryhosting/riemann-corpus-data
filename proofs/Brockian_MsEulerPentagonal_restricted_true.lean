import Mathlib

/-!
# Euler's pentagonal number theorem (recurrence form)

The main result `euler_pentagonal` states that for `n > 0`,
`∑ k (-1)^k p(n - g k) = 0` where `g k = k (3k-1)/2` runs over the generalized pentagonal
numbers and `p` is the partition function.

The proof has three parts.

* Part A (generating functions): using Mathlib's machinery for partition generating functions,
  `(∑ p(n) Xⁿ) * (∑ E(n) Xⁿ) = 1`, where `E(n)` is the signed count of partitions of `n` into
  distinct parts, the sign being the parity of the number of parts.
* Part B (Franklin's involution): `E(n) = (-1)^k` if `2n = k(3k-1)` for some integer `k`, and
  `E(n) = 0` otherwise.
* Part C: assembling the two.
-/

namespace Brockian.MsEulerPentagonal

open Finset

noncomputable section PartA

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The partition function. -/
def pf (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The signed count of partitions of `n` into distinct parts. -/
def Edist (n : ℕ) : ℤ := ∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ (Multiset.card p.parts)

-- Specialize `Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ ↦ True)`; the
-- restricted partitions with a trivial condition are all partitions.
/-- With the trivial condition, `restricted` is all of `univ`. -/
theorem restricted_true (n : ℕ) :
    Nat.Partition.restricted n (fun _ ↦ True) = Finset.univ := by
  simp [Nat.Partition.restricted]

theorem hasProd_pf :
    HasProd (fun i ↦ ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j))
      (PowerSeries.mk fun n ↦ (pf n : ℤ)) := by
  have := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ ↦ True)
  simp [pf, restricted_true] at this ⊢
  convert this using 2

-- Specialize `Nat.Partition.hasProd_genFun (fun _ c ↦ if c = 1 then (-1 : ℤ) else 0)`:
-- the `i`-th factor is `1 + ∑' j, (if j + 1 = 1 then -1 else 0) • X ^ ((i+1)*(j+1)) = 1 - X^(i+1)`
-- (use `tsum_eq_single 0`), and `Nat.Partition.genFun f = PowerSeries.mk Edist` because
-- `p.parts.toFinsupp.prod f` is `(-1) ^ (Multiset.card p.parts)` when `p.parts.Nodup` and `0`
-- otherwise.
theorem hasProd_Edist :
    HasProd (fun i ↦ (1 : ℤ⟦X⟧) - X ^ (i + 1)) (PowerSeries.mk fun n ↦ Edist n) := by
  have h := Nat.Partition.hasProd_genFun (fun _ c ↦ if c = 1 then (-1 : ℤ) else 0)
  have factor_eq : (fun i ↦ (1 : ℤ⟦X⟧) - X ^ (i + 1)) = (fun i ↦ 1 + ∑' (j : ℕ), (if j + 1 = 1 then (-1 : ℤ) else 0) • X ^ ((i + 1) * (j + 1))) := by
    ext i
    rw [tsum_eq_single 0]
    · simp [sub_eq_add_neg]
    · simp
  rw [factor_eq]
  have serie_eq : PowerSeries.mk (fun n ↦ Edist n) = Nat.Partition.genFun (fun x c => if c = 1 then (-1 : ℤ) else 0) := by
    ext n
    simp [Edist]
    have key : ∀ p : Nat.Partition n,
      (Multiset.toFinsupp p.parts).prod (fun x c => if c = 1 then (-1 : ℤ) else 0) =
      if p.parts.Nodup then (-1 : ℤ) ^ p.parts.card else 0 := by
      intro p
      by_cases h : p.parts.Nodup
      · simp [h]
        have support_eq : (Multiset.toFinsupp p.parts).support = p.parts.toFinset := by
          ext x
          simp [Multiset.mem_toFinset]
        have card_eq : (Multiset.toFinsupp p.parts).support.card = p.parts.card := by
          rw [support_eq]
          exact Multiset.toFinset_card_of_nodup h
        have prod_eq : ((Multiset.toFinsupp p.parts).prod fun x c => if c = 1 then (-1 : ℤ) else 0) =
                       ∏ x ∈ p.parts.toFinset, (-1 : ℤ) := by
          rw [← support_eq]
          apply Finset.prod_congr rfl
          intro x hx
          simp [Multiset.count_eq_one_of_mem h (Multiset.mem_toFinset.mp hx)]
        rw [prod_eq, Finset.prod_const, Multiset.toFinset_card_of_nodup h]
      · simp [h]
        rw [Multiset.nodup_iff_count_le_one] at h
        push_neg at h
        obtain ⟨a, ha⟩ := h
        exact ⟨a, Multiset.count_pos.mp (by linarith), ne_of_gt ha⟩
    simp_rw [key]
    rw [← Finset.sum_filter]
    congr
  rw [serie_eq]
  exact h

-- `hasProd_pf.mul hasProd_Edist` has all factors equal to `1`, by
-- `PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero` applied to
-- `f = X ^ (i + 1)` (after `pow_mul`); conclude with `HasProd.unique` against `hasProd_one`.
theorem pf_mul_Edist :
    (PowerSeries.mk fun n ↦ (pf n : ℤ)) * (PowerSeries.mk fun n ↦ Edist n) = 1 := by
  have h := hasProd_pf.mul hasProd_Edist
  have hone : ∀ i : ℕ, (∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) * (1 - X ^ (i + 1)) = 1 := by
    intro i
    have hp : ∀ j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) = (X ^ (i + 1)) ^ j := fun j ↦ by
      rw [← pow_mul]
    simp only [hp]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  simp only [hone] at h
  exact (HasProd.unique h hasProd_one)

/-- Euler's recurrence: the convolution of the partition function with the signed count of
distinct partitions vanishes in positive degrees. -/
theorem conv_zero (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ range (n + 1), Edist j * (pf (n - j) : ℤ) = 0 := by
  have h := congrArg (PowerSeries.coeff n) pf_mul_Edist
  rw [PowerSeries.coeff_mul] at h
  simp only [PowerSeries.coeff_mk] at h
  rw [PowerSeries.coeff_one, if_neg (by omega : ¬ n = 0)] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ (pf i : ℤ) * Edist j)] at h
  have hr := Finset.sum_range_reflect (fun i ↦ (pf i : ℤ) * Edist (n - i)) (n + 1)
  rw [← hr] at h
  rw [← h]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hnj : n + 1 - 1 - j = n - j := by omega
  have h2 : n - (n - j) = j := by omega
  rw [hnj, h2]
  ring

end PartA

section PartB

/-- Partitions of `n` into distinct parts, encoded as finsets of positive naturals. -/
def DP (n : ℕ) : Finset (Finset ℕ) :=
  ((range (n + 1)).powerset).filter (fun s ↦ 0 ∉ s ∧ ∑ i ∈ s, i = n)

theorem mem_DP {n : ℕ} {s : Finset ℕ} : s ∈ DP n ↔ 0 ∉ s ∧ ∑ i ∈ s, i = n := by
  simp only [DP]
  constructor
  · intro h
    exact Finset.mem_filter.mp h |>.2
  · intro ⟨h0, hsum⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, h0, hsum⟩
    rw [Finset.mem_powerset]
    intro x hx
    apply Finset.mem_range.mpr
    have hx_pos : 1 ≤ x := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hx))
    have hx_le : x ≤ n := hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le i) hx
    omega

/-- The signed count of partitions of `n` into distinct parts, in the finset encoding. -/
def Efin (n : ℕ) : ℤ := ∑ s ∈ DP n, (-1 : ℤ) ^ s.card

theorem Edist_eq_Efin (n : ℕ) : Edist n = Efin n := by
  simp only [Edist, Efin]
  refine Finset.sum_bij (fun p hp => p.parts.toFinset) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_DP]
    have hp' := List.mem_filter.mp hp
    have hnodup := hp'.2
    constructor
    · intro h0
      have := Multiset.mem_toFinset.mp h0
      have h0' : (0 : ℕ) ∈ p.parts := Multiset.mem_toFinset.mp h0
      have := p.2 h0'
      contradiction
    · have hnodup' : p.parts.Nodup := by simpa using hp'.2
      simp [Multiset.toFinset]
      have : p.parts.sum = n := Nat.Partition.parts_sum p
      rw [Multiset.dedup_eq_self.mpr hnodup', this]
  · -- Injectivity
    intro a₁ ha₁ a₂ ha₂ h
    have ha₁' := List.mem_filter.mp ha₁
    have ha₂' := List.mem_filter.mp ha₂
    have hnodup₁ : a₁.parts.Nodup := by simpa using ha₁'.2
    have hnodup₂ : a₂.parts.Nodup := by simpa using ha₂'.2
    have h' : a₁.parts.dedup = a₂.parts.dedup := by simpa [Multiset.toFinset] using h
    have heq : a₁.parts = a₂.parts := by
      rwa [Multiset.dedup_eq_self.mpr hnodup₁, Multiset.dedup_eq_self.mpr hnodup₂] at h'
    exact Nat.Partition.ext heq

  · -- Surjectivity
    intro b hb
    rw [mem_DP] at hb
    have hpos : ∀ x ∈ b, 0 < x := fun x hx => Nat.pos_of_ne_zero (fun h0 => hb.1 (h0 ▸ hx))
    have sum_eq := hb.2
    -- Construct a partition from the finset b
    have sum_eq' : b.val.sum = n := by simp [sum_eq]
    let p : Nat.Partition n := ⟨b.val, (@fun x hx => hpos x (by simpa using hx)), sum_eq'⟩
    use p
    refine ⟨?_, ?_⟩
    · -- p ∈ Nat.Partition.distincts n
      apply Finset.mem_filter.mpr
      refine ⟨by simp, ?_⟩
      exact b.nodup
    · -- p.parts.toFinset = b
      simp [Multiset.toFinset]
      congr 1
      exact Multiset.dedup_eq_self.mpr b.nodup

  · -- Cardinality
    intro a ha
    have ha' := List.mem_filter.mp ha
    have hnodup : a.parts.Nodup := by simpa using ha'.2
    simp only [Multiset.toFinset]
    have : a.parts.dedup = a.parts := Multiset.dedup_eq_self.mpr hnodup
    simp [this]

/-- The largest part (`0` for the empty partition). -/
def mx (s : Finset ℕ) : ℕ := s.sup id

/-- The smallest part (`0` for the empty partition). -/
noncomputable def mn (s : Finset ℕ) : ℕ := sInf {x | x ∈ s}

/-- The length of the maximal "staircase" `mx s, mx s - 1, …` contained in `s`. -/
noncomputable def run (s : Finset ℕ) : ℕ := sInf {r | 1 ≤ r ∧ (mx s - r) ∉ s}

theorem mx_mem {s : Finset ℕ} (hs : s.Nonempty) : mx s ∈ s := by
  rw [mx]
  obtain ⟨a, ha⟩ := Finset.exists_mem_eq_sup' hs id
  rw [← Finset.sup'_eq_sup hs id, ha.2]
  exact ha.1

theorem le_mx {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) : x ≤ mx s := by
  simp only [mx]
  have : x ≤ (s.sup id : ℕ) := Finset.le_sup (f := id) hx
  exact this

theorem mn_mem {s : Finset ℕ} (hs : s.Nonempty) : mn s ∈ s := by
  obtain ⟨x, hx⟩ := hs
  exact Nat.sInf_mem ⟨x, hx⟩

theorem mn_le {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) : mn s ≤ x := by
  exact Nat.sInf_le hx

theorem one_le_run {s : Finset ℕ} (h0 : 0 ∉ s) : 1 ≤ run s := by
  unfold run
  have hne : {r | 1 ≤ r ∧ (mx s - r) ∉ s}.Nonempty := by
    use mx s + 1
    simp only [Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    have : mx s - (mx s + 1) = 0 := by omega
    simp [this, h0]
  exact Nat.sInf_mem hne |>.1

theorem run_notMem {s : Finset ℕ} (h0 : 0 ∉ s) : (mx s - run s) ∉ s := by
  have hne : {r : ℕ | 1 ≤ r ∧ (mx s - r) ∉ s}.Nonempty := ⟨mx s + 1, by simp [h0]⟩
  have := Nat.sInf_mem hne
  exact this.2

theorem run_le {s : Finset ℕ} (h0 : 0 ∉ s) (hs : s.Nonempty) : run s ≤ mx s := by
  unfold run
  apply Nat.sInf_le
  constructor
  · obtain ⟨x, hx⟩ := hs
    have := le_mx hx
    have : 1 ≤ x := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hx))
    omega
  · simp [h0]

theorem Icc_run_subset {s : Finset ℕ} (hs : s.Nonempty) :
    Icc (mx s + 1 - run s) (mx s) ⊆ s := by
  intro k hk
  by_cases hkmx : k = mx s
  · rw [hkmx]
    exact mx_mem hs
  · simp only [Finset.mem_Icc] at hk
    have hklt : k < mx s := lt_of_le_of_ne hk.2 hkmx
    have hr' : mx s - k < run s := by omega
    have hr'_ge : 1 ≤ mx s - k := by omega
    have hnotin : mx s - (mx s - k) ∈ s := by
      by_contra hc
      have hle : run s ≤ mx s - k := Nat.sInf_le ⟨hr'_ge, hc⟩
      omega
    rwa [Nat.sub_sub_self (le_of_lt hklt)] at hnotin

/-- Characterisation of `run`. -/
theorem run_eq {s : Finset ℕ} {r : ℕ} (h1 : 1 ≤ r) (h2 : Icc (mx s + 1 - r) (mx s) ⊆ s)
    (h3 : (mx s - r) ∉ s) : run s = r := by
  have hne : {q : ℕ | 1 ≤ q ∧ (mx s - q) ∉ s}.Nonempty := ⟨r, h1, h3⟩
  have hmem : 1 ≤ run s ∧ (mx s - run s) ∉ s := Nat.sInf_mem hne
  refine le_antisymm (Nat.sInf_le ⟨h1, h3⟩) ?_
  by_contra hc
  push_neg at hc
  exact hmem.2 (h2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

/-- Shifting an interval by one. -/
theorem sum_Icc_shift (c d : ℕ) :
    ∑ i ∈ Icc (c + 1) (d + 1), i = (∑ i ∈ Icc c d, i) + (d + 1 - c) := by
  have h : Icc (c + 1) (d + 1) = Finset.image (fun j => j + 1) (Icc c d) := by
    ext x
    simp [Finset.mem_Icc]
  rw [h, Finset.sum_image (by simp)]
  simp [Finset.sum_add_distrib]

/-- Gauss' formula for a sum over an interval. -/
theorem sum_Icc_two (c d : ℕ) (h : c ≤ d + 1) : 2 * ∑ i ∈ Icc c d, i = (c + d) * (d + 1 - c) := by
  induction d with
  | zero => interval_cases c <;> simp
  | succ m ih =>
      rcases Nat.lt_or_ge (m + 1) c with hc | hc
      · have : c = m + 2 := by omega
        subst this; simp
      · rw [Finset.sum_Icc_succ_top (by omega)]
        have := ih (by omega)
        rw [Nat.mul_add, this]
        have h1 : m + 1 + 1 - c = (m + 1 - c) + 1 := by omega
        rw [h1]
        ring_nf
        omega

theorem sum_Icc_stair1 {k : ℕ} (hk : 1 ≤ k) :
    2 * ∑ i ∈ Icc k (2 * k - 1), i = k * (3 * k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
  rw [e1, e2, sum_Icc_two _ _ (by omega)]
  have e3 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  rw [e3]; ring

theorem sum_Icc_stair2 (k : ℕ) :
    2 * ∑ i ∈ Icc (k + 1) (2 * k), i = k * (3 * k + 1) := by
  rw [sum_Icc_two _ _ (by omega)]
  have e3 : 2 * k + 1 - (k + 1) = k := by omega
  rw [e3]; ring

theorem le_run {s : Finset ℕ} {r : ℕ} (h0 : 0 ∉ s)
    (h : Icc (mx s + 1 - r) (mx s) ⊆ s) : r ≤ run s := by
  unfold run
  by_contra hc
  push_neg at hc
  -- The set is nonempty (mx s is in it, since mx s >= 1 when 0 ∉ s and s nonempty, and mx s - mx s = 0 ∉ s)
  have hne : {r | 1 ≤ r ∧ mx s - r ∉ s}.Nonempty := by
    use mx s + 1
    simp
    exact h0
  -- sInf is in the set
  have hsmem := Nat.sInf_mem hne
  -- Let k = sInf {...}
  set k := sInf {r | 1 ≤ r ∧ mx s - r ∉ s} with hk_def
  -- From hsmem, k satisfies the predicate
  rw [hk_def] at hsmem
  obtain ⟨hk1, hkn⟩ := hsmem
  -- k < r from hc
  -- So mx s - k ≥ mx s + 1 - r (since k ≤ r - 1)
  -- And mx s - k ≤ mx s (since k ≥ 1)
  -- Therefore mx s - k ∈ Icc (mx s + 1 - r) (mx s), so by h, mx s - k ∈ s
  -- But hkn says mx s - k ∉ s - contradiction!
  have hklt : k < r := hc
  have hIcc : mx s - k ∈ Icc (mx s + 1 - r) (mx s) := by
    simp [Finset.mem_Icc]
    omega
  exact hkn (h hIcc)

theorem mx_Icc {c d : ℕ} (h : c ≤ d) : mx (Icc c d) = d := by
  refine le_antisymm ?_ (le_mx (Finset.mem_Icc.mpr ⟨h, le_rfl⟩))
  refine Finset.sup_le ?_
  intro x hx
  exact (Finset.mem_Icc.mp hx).2

theorem mn_Icc {c d : ℕ} (h : c ≤ d) : mn (Icc c d) = c := by
  have hne : (Icc c d).Nonempty := ⟨c, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  have h1 := mn_le (Finset.mem_Icc.mpr ⟨le_rfl, h⟩ : c ∈ Icc c d)
  have h2 := Finset.mem_Icc.mp (mn_mem hne)
  omega

theorem run_Icc {c d : ℕ} (h : c ≤ d) (hc : 1 ≤ c) : run (Icc c d) = d + 1 - c := by
  have hmx : mx (Icc c d) = d := mx_Icc h
  refine run_eq (by omega) ?_ ?_
  · rw [hmx]
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · rw [hmx]
    simp only [Finset.mem_Icc]
    omega

/-- Franklin's map in the case "smallest part ≤ staircase length": delete the smallest part `b`
and add one to each of the `b` largest parts. -/
noncomputable def frankDown (s : Finset ℕ) : Finset ℕ :=
  ((s.erase (mn s)) \ Icc (mx s + 1 - mn s) (mx s)) ∪ Icc (mx s + 2 - mn s) (mx s + 1)

/-- Franklin's map in the case "smallest part > staircase length": subtract one from each of the
`r` largest parts and adjoin a new part `r`. -/
noncomputable def frankUp (s : Finset ℕ) : Finset ℕ :=
  insert (run s) ((s \ Icc (mx s + 1 - run s) (mx s)) ∪ Icc (mx s - run s) (mx s - 1))

/-- Franklin's involution. -/
noncomputable def frank (s : Finset ℕ) : Finset ℕ :=
  if mn s ≤ run s then frankDown s else frankUp s

/-- The partitions on which Franklin's involution is well behaved. -/
noncomputable def Good (s : Finset ℕ) : Prop :=
  s.Nonempty ∧ (mn s ≤ run s → 2 * mn s ≤ mx s) ∧ (run s < mn s → 2 * run s < mx s)

noncomputable instance (s : Finset ℕ) : Decidable (Good s) := by unfold Good; infer_instance

theorem mem_frankDown {s : Finset ℕ} {x : ℕ} :
    x ∈ frankDown s ↔
      ((x ∈ s ∧ x ≠ mn s ∧ ¬ (mx s + 1 - mn s ≤ x ∧ x ≤ mx s)) ∨
        (mx s + 2 - mn s ≤ x ∧ x ≤ mx s + 1)) := by
  simp [frankDown, Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_Icc]
  tauto

theorem mem_frankUp {s : Finset ℕ} {x : ℕ} :
    x ∈ frankUp s ↔
      (x = run s ∨ (x ∈ s ∧ ¬ (mx s + 1 - run s ≤ x ∧ x ≤ mx s)) ∨
        (mx s - run s ≤ x ∧ x ≤ mx s - 1)) := by
  simp [frankUp, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]

/-
In the "Down" case write `a := mx s`, `b := mn s`, `r := run s` and `I := Icc (a + 1 - b) a`.
The hypotheses give `1 ≤ b`, `b ≤ r ≤ a`, `2 * b ≤ a`, `I ⊆ s` (`Icc_mn_subset`), `b ∉ I`,
`#I = b`, `b ∈ s`, `a ∈ s` and `∀ x ∈ s, b ≤ x ∧ x ≤ a`.  By definition
`frankDown s = ((s.erase b) \ I) ∪ Icc (a + 2 - b) (a + 1)`, a union of two disjoint sets, and
`Icc (a + 2 - b) (a + 1) = Icc ((a + 1 - b) + 1) (a + 1)` has the same cardinality `b` as `I`
while `sum_Icc_shift` gives that its sum is `(∑ i ∈ I, i) + b`.  Combined with
`Finset.sum_sdiff`, `Finset.card_sdiff` and `Finset.add_sum_erase` this yields
`frankDown_sum` and `frankDown_card`.  Membership in `frankDown s` is `mem_frankDown`.
-/

section Down

variable {s : Finset ℕ}

theorem Icc_mn_subset (hne : s.Nonempty) (hbr : mn s ≤ run s) :
    Icc (mx s + 1 - mn s) (mx s) ⊆ s := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  exact Icc_run_subset hne (Finset.mem_Icc.mpr ⟨by omega, hx.2⟩)

theorem mn_notMem_Icc (h0 : 0 ∉ s) (hne : s.Nonempty) (hab : 2 * mn s ≤ mx s) :
    mn s ∉ Icc (mx s + 1 - mn s) (mx s) := by
  have h1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h => h0 (h ▸ mn_mem hne))
  simp only [Finset.mem_Icc]
  omega

theorem frankDown_nonempty (h0 : 0 ∉ s) (hne : s.Nonempty)
    (hab : 2 * mn s ≤ mx s) : (frankDown s).Nonempty := by
  have hmn_pos : 1 ≤ mn s := by
    have hmem := mn_mem hne
    have hne0 : mn s ≠ 0 := fun h => h0 (h ▸ hmem)
    omega
  have himp : mx s + 2 - mn s ≤ mx s + 1 := by
    have : mx s + 2 ≤ mx s + 1 + mn s := by omega
    omega
  exact ⟨mx s + 1, by
    unfold frankDown
    simp [himp]⟩

theorem frankDown_zero (h0 : 0 ∉ s) (hne : s.Nonempty) : 0 ∉ frankDown s := by
  rw [mem_frankDown]
  intro h
  rcases h with ⟨h1, h2, _⟩ | ⟨h3, _⟩
  · exact h0 h1
  · have hms := mn_mem hne
    have hmn : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hms))
    have hmx : mn s ≤ mx s := mn_le (mx_mem hne)
    omega

theorem frankDown_sum (h0 : 0 ∉ s) (hne : s.Nonempty) (hbr : mn s ≤ run s)
    (hab : 2 * mn s ≤ mx s) : ∑ i ∈ frankDown s, i = ∑ i ∈ s, i := by
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hbs : mn s ∈ s := mn_mem hne
  have hI := Icc_mn_subset hne hbr
  have hbI := mn_notMem_Icc h0 hne hab
  have hIe : Icc (mx s + 1 - mn s) (mx s) ⊆ s.erase (mn s) := fun x hx ↦
    Finset.mem_erase.mpr ⟨fun h ↦ hbI (h ▸ hx), hI hx⟩
  have hdisj : Disjoint (s.erase (mn s) \ Icc (mx s + 1 - mn s) (mx s))
      (Icc (mx s + 2 - mn s) (mx s + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_Icc] at hx hx2
    exact hx.2 ⟨by omega, le_mx hx.1.2⟩
  rw [frankDown, Finset.sum_union hdisj]
  have hJ : Icc (mx s + 2 - mn s) (mx s + 1) = Icc ((mx s + 1 - mn s) + 1) (mx s + 1) := by
    congr 1
    omega
  rw [hJ, sum_Icc_shift (mx s + 1 - mn s) (mx s)]
  have h1 : ∑ i ∈ s.erase (mn s) \ Icc (mx s + 1 - mn s) (mx s), i
      + ∑ i ∈ Icc (mx s + 1 - mn s) (mx s), i = ∑ i ∈ s.erase (mn s), i :=
    Finset.sum_sdiff hIe
  have h2 : ∑ i ∈ s.erase (mn s), i + mn s = ∑ i ∈ s, i :=
    Finset.sum_erase_add s (fun i ↦ i) hbs
  omega

theorem frankDown_card (h0 : 0 ∉ s) (hne : s.Nonempty) (hbr : mn s ≤ run s)
    (hab : 2 * mn s ≤ mx s) : (frankDown s).card + 1 = s.card := by
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hbs : mn s ∈ s := mn_mem hne
  have hI := Icc_mn_subset hne hbr
  have hbI := mn_notMem_Icc h0 hne hab
  have hIe : Icc (mx s + 1 - mn s) (mx s) ⊆ s.erase (mn s) := fun x hx ↦
    Finset.mem_erase.mpr ⟨fun h ↦ hbI (h ▸ hx), hI hx⟩
  have hdisj : Disjoint (s.erase (mn s) \ Icc (mx s + 1 - mn s) (mx s))
      (Icc (mx s + 2 - mn s) (mx s + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_Icc] at hx hx2
    exact hx.2 ⟨by omega, le_mx hx.1.2⟩
  rw [frankDown, Finset.card_union_of_disjoint hdisj]
  have hc1 : (Icc (mx s + 1 - mn s) (mx s)).card = mn s := by
    rw [Nat.card_Icc]; omega
  have hc2 : (Icc (mx s + 2 - mn s) (mx s + 1)).card = mn s := by
    rw [Nat.card_Icc]; omega
  have h1 := Finset.card_sdiff_add_card_eq_card hIe
  have h2 : (s.erase (mn s)).card + 1 = s.card := by
    rw [Finset.card_erase_of_mem hbs]
    have := Finset.card_pos.mpr hne
    omega
  omega

theorem frankDown_mx (h0 : 0 ∉ s) (hne : s.Nonempty)
    (hab : 2 * mn s ≤ mx s) : mx (frankDown s) = mx s + 1 := by
  apply le_antisymm
  · -- All elements of frankDown s are ≤ mx s + 1
    apply Finset.sup_le
    intro x hx
    rw [mem_frankDown] at hx
    rcases hx with ⟨hx_s, _, _⟩ | ⟨hx_lb, hx_ub⟩
    · exact le_trans (le_mx hx_s) (Nat.le_succ _)
    · exact hx_ub
  · -- mx s + 1 ∈ frankDown s
    have hmn : 1 ≤ mn s := Nat.one_le_iff_ne_zero.mpr (fun h => h0 (by simpa [h] using mn_mem hne))
    have hmem : mx s + 1 ∈ frankDown s := by
      rw [mem_frankDown]
      right
      constructor
      · omega
      · rfl
    unfold mx
    exact Finset.le_sup hmem (f := id)

theorem frankDown_run (h0 : 0 ∉ s) (hne : s.Nonempty)
    (hab : 2 * mn s ≤ mx s) : run (frankDown s) = mn s := by
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hmx := frankDown_mx h0 hne hab
  refine run_eq hb1 ?_ ?_
  · rw [hmx]
    intro x hx
    simp only [Finset.mem_Icc] at hx
    rw [mem_frankDown]
    exact Or.inr ⟨by omega, by omega⟩
  · rw [hmx, mem_frankDown]
    rintro (⟨hxs, hxne, hxn⟩ | ⟨hl, hr⟩)
    · exact hxn ⟨by omega, by omega⟩
    · omega

theorem frankDown_mn (h0 : 0 ∉ s) (hne : s.Nonempty)
    (hab : 2 * mn s ≤ mx s) : mn s < mn (frankDown s) := by
  have htne := frankDown_nonempty h0 hne hab
  have hmem := mn_mem htne
  rw [mem_frankDown] at hmem
  rcases hmem with ⟨hx, hne', -⟩ | ⟨hl, hr⟩
  · have := mn_le hx
    omega
  · omega

theorem frankDown_good (h0 : 0 ∉ s) (hne : s.Nonempty)
    (hab : 2 * mn s ≤ mx s) : Good (frankDown s) := by
  have hrun := frankDown_run h0 hne hab
  have hmn := frankDown_mn h0 hne hab
  have hmx := frankDown_mx h0 hne hab
  exact ⟨frankDown_nonempty h0 hne hab, fun hc ↦ by omega, fun _ ↦ by omega⟩

theorem frankUp_frankDown (h0 : 0 ∉ s) (hne : s.Nonempty) (hbr : mn s ≤ run s)
    (hab : 2 * mn s ≤ mx s) : frankUp (frankDown s) = s := by
  ext x
  rw [mem_frankUp, mem_frankDown]
  have hmx : mx (frankDown s) = mx s + 1 := frankDown_mx h0 hne hab
  have hrun : run (frankDown s) = mn s := frankDown_run h0 hne hab
  rw [hmx, hrun]
  ring_nf
  have h1 : 1 + mx s - 1 = mx s := by omega
  simp only [h1]
  have hmn_mem : mn s ∈ s := mn_mem hne
  have Himn : Icc (mx s + 1 - mn s) (mx s) ⊆ s := Icc_mn_subset hne hbr
  -- Key facts about elements of s
  have hle_mx : ∀ x ∈ s, x ≤ mx s := fun x hx => le_mx hx
  -- Simplify: mx s + 1 - mn s = 1 + mx s - mn s
  have heq1 : mx s + 1 - mn s = 1 + mx s - mn s := by omega
  constructor
  · intro hx
    rcases hx with rfl | ⟨hmid, hnotB⟩ | ⟨hx_lb, hx_ub⟩
    · exact hmn_mem
    · rcases hmid with hA | ⟨hB_lb, hB_ub⟩
      · exact hA.1
      · exact absurd ⟨hB_lb, hB_ub⟩ hnotB
    · exact Himn (Finset.mem_Icc.mpr ⟨by omega, hx_ub⟩)
  · intro hx
    by_cases hxeq : x = mn s
    · left; exact hxeq
    · by_cases hxIcc : 1 + mx s - mn s ≤ x ∧ x ≤ mx s
      · right; right; exact hxIcc
      · right; left
        have hlt : x < 1 + mx s - mn s := by
          by_contra hge
          push_neg at hge
          apply hxIcc
          exact ⟨hge, hle_mx x hx⟩
        constructor
        · left
          exact ⟨hx, hxeq, hxIcc⟩
        · simp only [not_and_or]
          left
          omega

end Down

/-
In the "Up" case write `a := mx s`, `b := mn s`, `r := run s`, `I := Icc (a + 1 - r) a` and
`J := Icc (a - r) (a - 1)`.  The hypotheses give `1 ≤ r < b ≤ a`, `2 * r < a`, `I ⊆ s`
(`Icc_run_subset`), `a - r ∉ s` (`run_notMem`), `#I = #J = r`, `r ∉ s`, `r < a - r`, and
`frankUp s = insert r ((s \ I) ∪ J)` where the three pieces are pairwise disjoint.
Since `I = Icc ((a - r) + 1) ((a - 1) + 1)`, `sum_Icc_shift` gives
`∑ i ∈ I, i = (∑ i ∈ J, i) + r`.  Membership in `frankUp s` is `mem_frankUp`.
-/

section Up

variable {s : Finset ℕ}

theorem frankUp_nonempty : (frankUp s).Nonempty :=
  ⟨run s, by rw [mem_frankUp]; exact Or.inl rfl⟩

theorem frankUp_zero (h0 : 0 ∉ s) (hab : 2 * run s < mx s) : 0 ∉ frankUp s := by
  have h1 : 1 ≤ run s := one_le_run h0
  rw [mem_frankUp]
  rintro (h | ⟨hx, -⟩ | ⟨hl, hr⟩)
  · omega
  · exact h0 hx
  · omega

theorem frankUp_sum (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : ∑ i ∈ frankUp s, i = ∑ i ∈ s, i := by
  have h1r : 1 ≤ run s := one_le_run h0
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hrmx : run s ≤ mx s := run_le h0 hne
  have hI := Icc_run_subset hne
  have hnot := run_notMem h0
  have hrs : run s ∉ s := fun h ↦ absurd (mn_le h) (by omega)
  have hdisj : Disjoint (s \ Icc (mx s + 1 - run s) (mx s)) (Icc (mx s - run s) (mx s - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hx hx2
    have hxne : x ≠ mx s - run s := fun h ↦ hnot (h ▸ hx.1)
    exact hx.2 ⟨by omega, by omega⟩
  have hrnot : run s ∉ (s \ Icc (mx s + 1 - run s) (mx s)) ∪ Icc (mx s - run s) (mx s - 1) := by
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]
    rintro (⟨hx, -⟩ | ⟨hl, hr⟩)
    · exact hrs hx
    · omega
  rw [frankUp, Finset.sum_insert hrnot, Finset.sum_union hdisj]
  have hIeq : Icc (mx s + 1 - run s) (mx s) = Icc ((mx s - run s) + 1) ((mx s - 1) + 1) := by
    congr 1 <;> omega
  have hsh := sum_Icc_shift (mx s - run s) (mx s - 1)
  rw [← hIeq] at hsh
  have h1 : ∑ i ∈ s \ Icc (mx s + 1 - run s) (mx s), i
      + ∑ i ∈ Icc (mx s + 1 - run s) (mx s), i = ∑ i ∈ s, i :=
    Finset.sum_sdiff hI
  omega

theorem frankUp_card (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : (frankUp s).card = s.card + 1 := by
  have h1r : 1 ≤ run s := one_le_run h0
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hrmx : run s ≤ mx s := run_le h0 hne
  have hI := Icc_run_subset hne
  have hnot := run_notMem h0
  have hrs : run s ∉ s := fun h ↦ absurd (mn_le h) (by omega)
  have hdisj : Disjoint (s \ Icc (mx s + 1 - run s) (mx s)) (Icc (mx s - run s) (mx s - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hx hx2
    have hxne : x ≠ mx s - run s := fun h ↦ hnot (h ▸ hx.1)
    exact hx.2 ⟨by omega, by omega⟩
  have hrnot : run s ∉ (s \ Icc (mx s + 1 - run s) (mx s)) ∪ Icc (mx s - run s) (mx s - 1) := by
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]
    rintro (⟨hx, -⟩ | ⟨hl, hr⟩)
    · exact hrs hx
    · omega
  rw [frankUp, Finset.card_insert_of_notMem hrnot, Finset.card_union_of_disjoint hdisj]
  have hcI : (Icc (mx s + 1 - run s) (mx s)).card = run s := by
    rw [Nat.card_Icc]; omega
  have hcJ : (Icc (mx s - run s) (mx s - 1)).card = run s := by
    rw [Nat.card_Icc]; omega
  have h1 := Finset.card_sdiff_add_card_eq_card hI
  omega

theorem frankUp_mx (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : mx (frankUp s) = mx s - 1 := by
  have h1 : 1 ≤ run s := one_le_run h0
  have hb : mn s ≤ mx s := mn_le (mx_mem hne)
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro x hx
    rw [mem_frankUp] at hx
    simp only [id_eq]
    rcases hx with rfl | ⟨hxs, hxn⟩ | ⟨hl, hr⟩
    · omega
    · have hle := le_mx hxs
      rcases not_and_or.mp hxn with h' | h' <;> omega
    · omega
  · refine le_mx ?_
    rw [mem_frankUp]
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem frankUp_mn (h0 : 0 ∉ s) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : mn (frankUp s) = run s := by
  have h1 : 1 ≤ run s := one_le_run h0
  refine le_antisymm ?_ ?_
  · refine mn_le ?_
    rw [mem_frankUp]
    exact Or.inl rfl
  · have hmem := mn_mem (frankUp_nonempty (s := s))
    rw [mem_frankUp] at hmem
    rcases hmem with h | ⟨hxs, -⟩ | ⟨hl, hr⟩
    · omega
    · have := mn_le hxs
      omega
    · omega

theorem frankUp_run (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : run s ≤ run (frankUp s) := by
  have h1 : 1 ≤ run s := one_le_run h0
  have hmx := frankUp_mx h0 hne hrb hab
  refine le_run (frankUp_zero h0 hab) ?_
  intro x hx
  simp only [Finset.mem_Icc] at hx
  rw [hmx] at hx
  rw [mem_frankUp]
  exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem frankUp_good (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : Good (frankUp s) := by
  have hmn := frankUp_mn h0 hrb hab
  have hrun := frankUp_run h0 hne hrb hab
  have hmx := frankUp_mx h0 hne hrb hab
  exact ⟨frankUp_nonempty (s := s), fun _ ↦ by omega, fun hc ↦ by omega⟩

theorem frankDown_frankUp (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : frankDown (frankUp s) = s := by
  have h1r : 1 ≤ run s := one_le_run h0
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hrmx : run s ≤ mx s := run_le h0 hne
  have hI := Icc_run_subset hne
  have hnot := run_notMem h0
  have hmx := frankUp_mx h0 hne hrb hab
  have hmn := frankUp_mn h0 hrb hab
  ext x
  rw [mem_frankDown, hmx, hmn, mem_frankUp]
  constructor
  · rintro (⟨hxt, hxne, hxn⟩ | ⟨hl, hr⟩)
    · rcases hxt with rfl | ⟨hxs, -⟩ | ⟨hl, hr⟩
      · exact absurd rfl hxne
      · exact hxs
      · exact absurd ⟨by omega, by omega⟩ hxn
    · exact hI (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro hx
    have hxb := mn_le hx
    have hxa := le_mx hx
    by_cases hcase : mx s + 1 - run s ≤ x
    · right
      exact ⟨by omega, by omega⟩
    · left
      have hxne : x ≠ mx s - run s := fun h ↦ hnot (h ▸ hx)
      refine ⟨Or.inr (Or.inl ⟨hx, ?_⟩), by omega, ?_⟩
      · rintro ⟨hl, -⟩
        omega
      · rintro ⟨hl, -⟩
        omega

end Up

theorem frank_mem {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : Good s) : frank s ∈ DP n := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  obtain ⟨hne, hd, hu⟩ := hg
  rw [mem_DP]
  by_cases h : mn s ≤ run s
  · simp only [frank, if_pos h]
    exact ⟨frankDown_zero h0 hne, by rw [frankDown_sum h0 hne h (hd h), hsum]⟩
  · simp only [frank, if_neg h]
    rw [not_le] at h
    exact ⟨frankUp_zero h0 (hu h), by rw [frankUp_sum h0 hne h (hu h), hsum]⟩

theorem frank_good {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : Good s) : Good (frank s) := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  obtain ⟨hne, hd, hu⟩ := hg
  by_cases h : mn s ≤ run s
  · simp only [frank, if_pos h]
    exact frankDown_good h0 hne (hd h)
  · simp only [frank, if_neg h]
    rw [not_le] at h
    exact frankUp_good h0 hne h (hu h)

theorem frank_frank {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : Good s) :
    frank (frank s) = s := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  obtain ⟨hne, hd, hu⟩ := hg
  by_cases h : mn s ≤ run s
  · have hrun := frankDown_run h0 hne (hd h)
    have hmn := frankDown_mn h0 hne (hd h)
    simp only [frank, if_pos h, if_neg (by omega : ¬ mn (frankDown s) ≤ run (frankDown s))]
    exact frankUp_frankDown h0 hne h (hd h)
  · simp only [frank, if_neg h]
    rw [not_le] at h
    have hrun := frankUp_run h0 hne h (hu h)
    have hmn := frankUp_mn h0 h (hu h)
    rw [if_pos (by omega : mn (frankUp s) ≤ run (frankUp s))]
    exact frankDown_frankUp h0 hne h (hu h)

theorem frank_sign {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : Good s) :
    (-1 : ℤ) ^ (frank s).card = -(-1 : ℤ) ^ s.card := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  obtain ⟨hne, hd, hu⟩ := hg
  by_cases h : mn s ≤ run s
  · have hc := frankDown_card h0 hne h (hd h)
    simp only [frank, if_pos h]
    rw [← hc, pow_succ]
    ring
  · simp only [frank, if_neg h]
    rw [not_le] at h
    have hc := frankUp_card h0 hne h (hu h)
    rw [hc, pow_succ]
    ring

theorem Efin_eq_sum_notGood (n : ℕ) :
    Efin n = ∑ s ∈ (DP n).filter (fun s ↦ ¬ Good s), (-1 : ℤ) ^ s.card := by
  have hzero : ∑ s ∈ (DP n).filter (fun s ↦ Good s), (-1 : ℤ) ^ s.card = 0 := by
    refine Finset.sum_involution (fun s _ ↦ frank s) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      rw [frank_sign ha1 ha2]
      ring
    · intro a ha _ heq
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      have heq' : frank a = a := heq
      have hsg := frank_sign ha1 ha2
      rw [heq'] at hsg
      have hne0 : ((-1 : ℤ)) ^ a.card ≠ 0 := pow_ne_zero _ (by norm_num)
      exact hne0 (by linarith)
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨frank_mem ha1 ha2, frank_good ha1 ha2⟩
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact frank_frank ha1 ha2
  have hsplit := Finset.sum_filter_add_sum_filter_not (DP n) (fun s ↦ Good s)
    (fun s ↦ (-1 : ℤ) ^ s.card)
  rw [hzero, zero_add] at hsplit
  rw [Efin, ← hsplit]

/-- Any exceptional partition is one of the two "pentagonal staircases". -/
theorem notGood_classify' {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : ¬ Good s) :
    s = ∅ ∨ (∃ k : ℕ, 1 ≤ k ∧ s = Icc k (2 * k - 1)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ s = Icc (k + 1) (2 * k)) := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · exact Or.inl rfl
  right
  have key : (mn s ≤ run s ∧ mx s < 2 * mn s) ∨ (run s < mn s ∧ mx s ≤ 2 * run s) := by
    by_contra hc
    push_neg at hc
    exact hg ⟨hne, fun h ↦ by have := hc.1 h; omega, fun h ↦ by have := hc.2 h; omega⟩
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  rcases key with ⟨hbr, hab⟩ | ⟨hrb, hab⟩
  · left
    have hI := Icc_mn_subset hne hbr
    have hmem : mx s + 1 - mn s ∈ s := hI (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have h2 := mn_le hmem
    refine ⟨mn s, hb1, Finset.Subset.antisymm ?_ ?_⟩
    · intro x hx
      have h3 := mn_le hx
      have h4 := le_mx hx
      simp only [Finset.mem_Icc]
      omega
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hI (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · right
    have hr1 : 1 ≤ run s := one_le_run h0
    have hI := Icc_run_subset hne
    have hmem : mx s + 1 - run s ∈ s := hI (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have h2 := mn_le hmem
    refine ⟨run s, hr1, Finset.Subset.antisymm ?_ ?_⟩
    · intro x hx
      have h3 := mn_le hx
      have h4 := le_mx hx
      simp only [Finset.mem_Icc]
      omega
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hI (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem empty_not_good : ¬ Good (∅ : Finset ℕ) := by
  simp [Good]

theorem stair1_not_good {k : ℕ} (hk : 1 ≤ k) : ¬ Good (Icc k (2 * k - 1)) := by
  intro hg
  obtain ⟨-, h1, -⟩ := hg
  have hle : k ≤ 2 * k - 1 := by omega
  rw [mn_Icc hle, mx_Icc hle, run_Icc hle hk] at h1
  have := h1 (by omega)
  omega

theorem stair2_not_good {k : ℕ} (hk : 1 ≤ k) : ¬ Good (Icc (k + 1) (2 * k)) := by
  intro hg
  obtain ⟨-, -, h2⟩ := hg
  have hle : k + 1 ≤ 2 * k := by omega
  rw [mn_Icc hle, mx_Icc hle, run_Icc hle (by omega)] at h2
  have := h2 (by omega)
  omega

theorem stair1_mem_DP {n k : ℕ} (hk : 1 ≤ k) (h : 2 * n = k * (3 * k - 1)) :
    Icc k (2 * k - 1) ∈ DP n := by
  rw [mem_DP]
  refine ⟨?_, ?_⟩
  · simp only [Finset.mem_Icc]
    omega
  · have := sum_Icc_stair1 hk
    omega

theorem stair2_mem_DP {n k : ℕ} (hk : 1 ≤ k) (h : 2 * n = k * (3 * k + 1)) :
    Icc (k + 1) (2 * k) ∈ DP n := by
  rw [mem_DP]
  refine ⟨?_, ?_⟩
  · simp only [Finset.mem_Icc]
    omega
  · have := sum_Icc_stair2 k
    omega

theorem pent_inj {k l : ℤ} (h : k * (3 * k - 1) = l * (3 * l - 1)) : k = l := by
  have h2 : (k - l) * (3 * (k + l) - 1) = 0 := by linarith [h]
  rcases mul_eq_zero.mp h2 with hkl | hsum
  · linarith
  · omega

/-- The exceptional partition attached to a generalized pentagonal number. -/
def pentSet (k : ℤ) : Finset ℕ :=
  if 0 < k then Icc k.toNat (2 * k.toNat - 1) else Icc (k.natAbs + 1) (2 * k.natAbs)

theorem pentSet_card (k : ℤ) : (pentSet k).card = k.natAbs := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have : ¬ (0 < k) := by omega
    rw [pentSet, if_neg this, Nat.card_Icc]
    have : 1 ≤ k.natAbs := by omega
    omega
  · simp [pentSet]
  · rw [pentSet, if_pos hk, Nat.card_Icc]
    have h1 : 1 ≤ k.toNat := by omega
    have h2 : k.toNat = k.natAbs := by omega
    omega

theorem pentSet_not_good (k : ℤ) : ¬ Good (pentSet k) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have h0 : ¬ (0 < k) := by omega
    rw [pentSet, if_neg h0]
    exact stair2_not_good (by omega)
  · have : pentSet 0 = (∅ : Finset ℕ) := by
      simp [pentSet]
    rw [this]
    exact empty_not_good
  · rw [pentSet, if_pos hk]
    exact stair1_not_good (by omega)

theorem pentSet_mem_DP {n : ℕ} {k : ℤ} (h : 2 * (n : ℤ) = k * (3 * k - 1)) :
    pentSet k ∈ DP n := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have h0 : ¬ (0 < k) := by omega
    rw [pentSet, if_neg h0]
    refine stair2_mem_DP (by omega) ?_
    have hk' : (k.natAbs : ℤ) = -k := by omega
    have : 2 * (n : ℤ) = (k.natAbs : ℤ) * (3 * (k.natAbs : ℤ) + 1) := by
      rw [hk']; linarith [h]
    exact_mod_cast this
  · have hn : n = 0 := by simpa using h
    have : pentSet 0 = (∅ : Finset ℕ) := by simp [pentSet]
    rw [this, hn, mem_DP]
    simp
  · rw [pentSet, if_pos hk]
    refine stair1_mem_DP (by omega) ?_
    have hk' : (k.toNat : ℤ) = k := by omega
    have h1 : 1 ≤ k.toNat := by omega
    have : 2 * (n : ℤ) = (k.toNat : ℤ) * (3 * (k.toNat : ℤ) - 1) := by rw [hk']; exact h
    have hcast : ((3 * k.toNat - 1 : ℕ) : ℤ) = 3 * (k.toNat : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * k.toNat)]
      ring
    have := this
    zify [Nat.cast_sub (by omega : 1 ≤ 3 * k.toNat)]
    linarith

/-- Every exceptional partition of `n` is `pentSet k` for a generalized pentagonal index `k`. -/
theorem notGood_param {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : ¬ Good s) :
    ∃ k : ℤ, 2 * (n : ℤ) = k * (3 * k - 1) ∧ s = pentSet k := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  rcases notGood_classify' hs hg with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · refine ⟨0, ?_, ?_⟩
    · simp at hsum
      simp [← hsum]
    · simp [pentSet]
  · refine ⟨(k : ℤ), ?_, ?_⟩
    · have h1 := sum_Icc_stair1 hk
      rw [hsum] at h1
      have : ((2 * n : ℕ) : ℤ) = ((k * (3 * k - 1) : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * k)] at this
      linarith
    · rw [pentSet, if_pos (by exact_mod_cast hk : (0 : ℤ) < (k : ℤ))]
      simp
  · refine ⟨-(k : ℤ), ?_, ?_⟩
    · have h1 := sum_Icc_stair2 k
      rw [hsum] at h1
      have : ((2 * n : ℕ) : ℤ) = ((k * (3 * k + 1) : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at this
      linarith
    · have h0' : ¬ (0 < -(k : ℤ)) := by omega
      rw [pentSet, if_neg h0']
      have : (-(k : ℤ)).natAbs = k := by omega
      rw [this]

/-- Any exceptional partition of `n` witnesses that `n` is a generalized pentagonal number. -/
theorem notGood_classify {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : ¬ Good s) :
    ∃ k : ℤ, 2 * (n : ℤ) = k * (3 * k - 1) ∧ s.card = k.natAbs := by
  obtain ⟨k, hk, rfl⟩ := notGood_param hs hg
  exact ⟨k, hk, pentSet_card k⟩

/-- There is at most one exceptional partition of `n`. -/
theorem notGood_unique {n : ℕ} {s t : Finset ℕ} (hs : s ∈ DP n) (hgs : ¬ Good s)
    (ht : t ∈ DP n) (hgt : ¬ Good t) : s = t := by
  obtain ⟨k, hk, rfl⟩ := notGood_param hs hgs
  obtain ⟨l, hl, rfl⟩ := notGood_param ht hgt
  rw [pent_inj (by omega : k * (3 * k - 1) = l * (3 * l - 1))]

/-- If `n` is a generalized pentagonal number there is an exceptional partition of `n`. -/
theorem notGood_exists {n : ℕ} {k : ℤ} (hk : 2 * (n : ℤ) = k * (3 * k - 1)) :
    ∃ s ∈ DP n, ¬ Good s ∧ s.card = k.natAbs :=
  ⟨pentSet k, pentSet_mem_DP hk, pentSet_not_good k, pentSet_card k⟩

theorem Efin_of_pent {n : ℕ} {k : ℤ} (hk : 2 * (n : ℤ) = k * (3 * k - 1)) :
    Efin n = (-1 : ℤ) ^ k.natAbs := by
  rw [Efin_eq_sum_notGood]
  have h1 : (DP n).filter (fun s ↦ ¬ Good s) = {pentSet k} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨pentSet_mem_DP hk, pentSet_not_good k⟩
    · intro t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
      obtain ⟨l, hl, rfl⟩ := notGood_param ht1 ht2
      rw [pent_inj (by omega : l * (3 * l - 1) = k * (3 * k - 1))]
  rw [h1, Finset.sum_singleton, pentSet_card]

theorem Efin_of_not_pent {n : ℕ} (h : ∀ k : ℤ, 2 * (n : ℤ) ≠ k * (3 * k - 1)) : Efin n = 0 := by
  rw [Efin_eq_sum_notGood]
  have h1 : (DP n).filter (fun s ↦ ¬ Good s) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t ht hnot
    obtain ⟨k, hk, -⟩ := notGood_param ht hnot
    exact h k hk
  rw [h1, Finset.sum_empty]

end PartB

section PartC

/-- The generalized pentagonal number `g k = k (3k - 1) / 2`. -/
def pent (k : ℤ) : ℤ := k * (3 * k - 1) / 2

theorem two_mul_pent (k : ℤ) : 2 * pent k = k * (3 * k - 1) := by
  have h : (2 : ℤ) ∣ k * (3 * k - 1) := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩ <;> subst hm
    · exact ⟨m * (3 * (m + m) - 1), by ring⟩
    · exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
  rw [pent, Int.mul_ediv_cancel' h]

theorem pent_nonneg (k : ℤ) : 0 ≤ pent k := by
  have h := two_mul_pent k
  by_cases hk : k ≤ 0
  · nlinarith
  · push_neg at hk
    nlinarith

theorem pent_injective : Function.Injective pent := by
  intro a b hab
  refine pent_inj ?_
  have ha := two_mul_pent a
  have hb := two_mul_pent b
  rw [hab] at ha
  omega

theorem abs_le_of_pent_le {k : ℤ} {n : ℕ} (h : pent k ≤ n) : |k| ≤ (n : ℤ) := by
  have h2 := two_mul_pent k
  by_cases hk : 0 ≤ k
  · rw [abs_of_nonneg hk]
    nlinarith
  · push_neg at hk
    rw [abs_of_neg hk]
    nlinarith

/-- Euler's pentagonal number theorem (recurrence form): the partition function satisfies
    ∑_{k} (−1)^k · p(n − g_k) = 0 for n > 0, where g_k = k(3k−1)/2 ranges over generalized
    pentagonal numbers. Stated here as the alternating sum over pentagonal offsets.

    (The only change to the original statement is the explicit `ℤ`-valued type ascriptions,
    which are needed for the expression to elaborate.) -/
theorem euler_pentagonal (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc (-(n:ℤ)) n,
      (if (k * (3 * k - 1) / 2) ≤ (n:ℤ) then
        (-1 : ℤ) ^ (k.natAbs) *
          (Fintype.card (Nat.Partition (n - (k * (3 * k - 1) / 2).toNat)) : ℤ)
       else 0) = 0 := by
  have hpent : ∀ k : ℤ, k * (3 * k - 1) / 2 = pent k := fun _ ↦ rfl
  have hpf : ∀ m : ℕ, (Fintype.card (Nat.Partition m) : ℤ) = (pf m : ℤ) := fun _ ↦ rfl
  simp only [hpent, hpf]
  rw [← Finset.sum_filter]
  have main : ∑ k ∈ (Finset.Icc (-(n:ℤ)) n).filter (fun k ↦ pent k ≤ (n:ℤ)),
      ((-1 : ℤ) ^ k.natAbs * (pf (n - (pent k).toNat) : ℤ))
      = ∑ j ∈ Finset.range (n + 1), Efin j * (pf (n - j) : ℤ) := by
    refine Finset.sum_of_injOn (fun k ↦ (pent k).toNat) ?_ ?_ ?_ ?_
    · intro a _ b _ hab
      have hab' : (pent a).toNat = (pent b).toNat := hab
      have ha := pent_nonneg a
      have hb := pent_nonneg b
      exact pent_injective (by omega)
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hk
      have h1 := pent_nonneg k
      show (pent k).toNat ∈ (↑(Finset.range (n + 1)) : Set ℕ)
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro j hj hnot
      have hjn : j ≤ n := by
        simp only [Finset.mem_range] at hj
        omega
      refine mul_eq_zero_of_left (Efin_of_not_pent ?_) _
      intro k hk
      apply hnot
      have h1 := two_mul_pent k
      have hpk : pent k = (j : ℤ) := by omega
      have habs := abs_le_of_pent_le (k := k) (n := n) (by omega)
      have habs' := abs_le.mp habs
      refine ⟨k, ?_, ?_⟩
      · simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc]
        exact ⟨⟨habs'.1, habs'.2⟩, by omega⟩
      · show (pent k).toNat = j
        omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      have h1 := pent_nonneg k
      have h2 : 2 * (((pent k).toNat : ℕ) : ℤ) = k * (3 * k - 1) := by
        have := two_mul_pent k
        omega
      rw [Efin_of_pent h2]
  rw [main]
  have hc := conv_zero n hn
  simp only [Edist_eq_Efin] at hc
  exact hc

end PartC

end Brockian.MsEulerPentagonal

