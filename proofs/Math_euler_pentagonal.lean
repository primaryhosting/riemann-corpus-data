import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/
noncomputable def fmin (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.min' h else 0

/-- The largest element of a finite set of naturals (junk value `0` if empty). -/
noncomputable def fmax (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.max' h else 0

/-- The length of the run of consecutive integers at the top of `s`: the least `t ≥ 1`
such that `fmax s - t ∉ s`. -/
noncomputable def run (s : Finset ℕ) : ℕ := sInf {t | 1 ≤ t ∧ (fmax s - t) ∉ s}

/-- The set of partitions of `n` into distinct positive parts, encoded as finite sets of
positive naturals summing to `n`. -/
noncomputable def D (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun s => ∑ i ∈ s, i = n)

/-- The "exceptional" (fixed) configurations of Franklin's involution. -/
def isExc (s : Finset ℕ) : Prop :=
  (fmin s ≤ run s ∧ fmax s + 1 = 2 * fmin s) ∨ (run s < fmin s ∧ fmax s = 2 * run s)

/-- Franklin's involution on partitions into distinct parts. -/
noncomputable def franklin (s : Finset ℕ) : Finset ℕ :=
  if fmin s ≤ run s then
    insert (fmax s + 1) ((s.erase (fmin s)).erase (fmax s - fmin s + 1))
  else
    insert (fmax s - run s) (insert (run s) (s.erase (fmax s)))

/-! ### Basic facts about `fmin`, `fmax`, `run` -/

lemma fmin_mem {s : Finset ℕ} (hne : s.Nonempty) : fmin s ∈ s := by
  simp only [fmin, dif_pos hne]; exact s.min'_mem hne

lemma fmax_mem {s : Finset ℕ} (hne : s.Nonempty) : fmax s ∈ s := by
  simp only [fmax, dif_pos hne]; exact s.max'_mem hne

lemma fmin_le {s : Finset ℕ} {a : ℕ} (ha : a ∈ s) : fmin s ≤ a := by
  have hne : s.Nonempty := ⟨a, ha⟩
  simp only [fmin, dif_pos hne]; exact s.min'_le a ha

lemma le_fmax {s : Finset ℕ} {a : ℕ} (ha : a ∈ s) : a ≤ fmax s := by
  have hne : s.Nonempty := ⟨a, ha⟩
  simp only [fmax, dif_pos hne]; exact s.le_max' a ha

lemma fmin_pos {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) : 0 < fmin s :=
  Nat.pos_of_ne_zero (fun h => h0 (h ▸ fmin_mem hne))

lemma fmax_pos {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) : 0 < fmax s :=
  lt_of_lt_of_le (fmin_pos h0 hne) (le_fmax (fmin_mem hne))

lemma run_spec {s : Finset ℕ} (h0 : 0 ∉ s) : 1 ≤ run s ∧ (fmax s - run s) ∉ s := by
  have hex : ∃ t, t ∈ {t : ℕ | 1 ≤ t ∧ (fmax s - t) ∉ s} := by
    rcases Nat.eq_zero_or_pos (fmax s) with h | h
    · exact ⟨1, by simp [h, h0]⟩
    · exact ⟨fmax s, ⟨h, by simpa using h0⟩⟩
  exact Nat.sInf_mem hex

lemma run_pos {s : Finset ℕ} (h0 : 0 ∉ s) : 0 < run s := (run_spec h0).1

lemma run_notMem {s : Finset ℕ} (h0 : 0 ∉ s) : (fmax s - run s) ∉ s := (run_spec h0).2

lemma run_mem {s : Finset ℕ} (hne : s.Nonempty) {i : ℕ} (hi : i < run s) :
    (fmax s - i) ∈ s := by
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simpa using fmax_mem hne
  · by_contra hmem
    have : run s ≤ i := Nat.sInf_le ⟨hipos, hmem⟩
    omega

lemma run_le_fmax {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) : run s ≤ fmax s := by
  by_contra h
  push_neg at h
  have := run_mem hne (i := fmax s) h
  simp at this
  exact h0 this

/-! ### Membership in `D n` -/

lemma mem_D_iff {n : ℕ} {s : Finset ℕ} : s ∈ D n ↔ (0 ∉ s ∧ ∑ i ∈ s, i = n) := by
  simp only [D, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum⟩
    have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (fun h => h0 (h ▸ ha))
    have h2 : a ≤ n := hsum ▸ Finset.single_le_sum (f := fun i : ℕ => i)
      (fun i _ => Nat.zero_le i) ha
    simp [Finset.mem_Icc, h1, h2]

/-! ### Case A of Franklin's involution -/

lemma caseA {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (hA : fmin s ≤ run s)
    (hnexc : fmax s + 1 ≠ 2 * fmin s) :
    0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = (∑ i ∈ s, i) ∧ (franklin s).card + 1 = s.card ∧
      ¬ isExc (franklin s) ∧ franklin (franklin s) = s := by
  have hσmem : fmin s ∈ s := fmin_mem hne
  have hMmem : fmax s ∈ s := fmax_mem hne
  have hσpos : 0 < fmin s := fmin_pos h0 hne
  have hσM : fmin s ≤ fmax s := le_fmax hσmem
  have htop : fmax s - fmin s + 1 ∈ s := by
    have h1 : fmin s - 1 < run s := by omega
    have h2 := run_mem hne h1
    have h3 : fmax s - (fmin s - 1) = fmax s - fmin s + 1 := by omega
    rwa [h3] at h2
  have h2σ : 2 * fmin s ≤ fmax s := by
    have := fmin_le htop
    omega
  set u : Finset ℕ := (s.erase (fmin s)).erase (fmax s - fmin s + 1) with hu
  have husub : u ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hfr : franklin s = insert (fmax s + 1) u := by rw [franklin, if_pos hA]
  have hnotu1 : fmin s ∉ u := fun h => (Finset.mem_erase.1 (Finset.mem_of_mem_erase h)).1 rfl
  have hnotu2 : (fmax s - fmin s + 1) ∉ u := Finset.notMem_erase _ _
  have hM1notu : fmax s + 1 ∉ u := by
    intro h
    have := le_fmax (husub h)
    omega
  have hsu : s = insert (fmin s) (insert (fmax s - fmin s + 1) u) := by
    rw [hu, Finset.insert_erase (Finset.mem_erase.2 ⟨by omega, htop⟩),
      Finset.insert_erase hσmem]
  have hnotins : fmin s ∉ insert (fmax s - fmin s + 1) u := by
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨by omega, hnotu1⟩
  have hcards : s.card = u.card + 2 := by
    rw [hsu, Finset.card_insert_of_notMem hnotins, Finset.card_insert_of_notMem hnotu2]
  have hsums : (∑ i ∈ s, i) = fmin s + ((fmax s - fmin s + 1) + ∑ i ∈ u, i) := by
    conv_lhs => rw [hsu]
    rw [Finset.sum_insert hnotins, Finset.sum_insert hnotu2]
  -- properties of the image
  set t : Finset ℕ := insert (fmax s + 1) u with ht
  have h0t : 0 ∉ t := by
    simp only [ht, Finset.mem_insert]
    push_neg
    exact ⟨by omega, fun h => h0 (husub h)⟩
  have htne : t.Nonempty := ⟨fmax s + 1, by simp [ht]⟩
  have hmaxt : fmax t = fmax s + 1 := by
    refine le_antisymm ?_ (le_fmax (by simp [ht]))
    have := fmax_mem htne
    rcases Finset.mem_insert.1 this with h | h
    · omega
    · have := le_fmax (husub h); omega
  have hlt : ∀ a ∈ t, fmin s < a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with h | h
    · omega
    · have h1 : a ∈ s := husub h
      have h2 : a ≠ fmin s := fun hh => hnotu1 (hh ▸ h)
      have := fmin_le h1
      omega
  have hmint : fmin s < fmin t := hlt _ (fmin_mem htne)
  have hrunt : run t = fmin s := by
    have hmem : (fmax t - fmin s) ∉ t := by
      rw [hmaxt]
      have : fmax s + 1 - fmin s = fmax s - fmin s + 1 := by omega
      rw [this]
      simp only [ht, Finset.mem_insert]
      push_neg
      exact ⟨by omega, hnotu2⟩
    have hle : run t ≤ fmin s := Nat.sInf_le ⟨hσpos, hmem⟩
    by_contra hne'
    have hlt' : run t < fmin s := lt_of_le_of_ne hle hne'
    have h1 : 0 < run t := run_pos h0t
    have h2 : (fmax t - run t) ∉ t := run_notMem h0t
    apply h2
    have h3 : fmax t - run t = fmax s - (run t - 1) := by rw [hmaxt]; omega
    have h4 : run t - 1 < run s := by omega
    have h5 : fmax s - (run t - 1) ∈ s := run_mem hne h4
    have h6 : fmax s - (run t - 1) ≠ fmin s := by
      have : fmax s - (run t - 1) ≥ fmax s - fmin s + 1 := by omega
      omega
    have h7 : fmax s - (run t - 1) ≠ fmax s - fmin s + 1 := by omega
    rw [h3]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h7, Finset.mem_erase.2 ⟨h6, h5⟩⟩)
  refine ⟨by rwa [hfr], ?_, ?_, ?_, ?_⟩
  · rw [hfr, ht, Finset.sum_insert hM1notu, hsums]
    omega
  · rw [hfr, ht, Finset.card_insert_of_notMem hM1notu, hcards]
  · rw [hfr]
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · omega
    · rw [hmaxt, hrunt] at h; omega
  · rw [hfr, franklin, if_neg (by omega), hmaxt, hrunt, ht,
      Finset.erase_insert hM1notu]
    have : fmax s + 1 - fmin s = fmax s - fmin s + 1 := by omega
    rw [this, Finset.insert_comm, ← hsu]

/-! ### Case B of Franklin's involution -/

lemma caseB {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (hB : ¬ (fmin s ≤ run s))
    (hnexc : fmax s ≠ 2 * run s) :
    0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = (∑ i ∈ s, i) ∧ s.card + 1 = (franklin s).card ∧
      ¬ isExc (franklin s) ∧ franklin (franklin s) = s := by
  push_neg at hB
  have hMmem : fmax s ∈ s := fmax_mem hne
  have hτpos : 0 < run s := run_pos h0
  have hτM : run s ≤ fmax s := run_le_fmax h0 hne
  have hτnotmem : run s ∉ s := fun h => absurd (fmin_le h) (by omega)
  have hMtτ : (fmax s - run s) ∉ s := run_notMem h0
  have htop : fmax s - run s + 1 ∈ s := by
    have h1 : run s - 1 < run s := by omega
    have h2 := run_mem hne h1
    have h3 : fmax s - (run s - 1) = fmax s - run s + 1 := by omega
    rwa [h3] at h2
  have h2τ : 2 * run s < fmax s := by
    have := fmin_le htop
    omega
  set u : Finset ℕ := s.erase (fmax s) with hu
  have husub : u ⊆ s := Finset.erase_subset _ _
  have hsu : s = insert (fmax s) u := (Finset.insert_erase hMmem).symm
  have hMnotu : fmax s ∉ u := Finset.notMem_erase _ _
  have hτnotu : run s ∉ u := fun h => hτnotmem (husub h)
  have hMtτnotu : (fmax s - run s) ∉ u := fun h => hMtτ (husub h)
  have hne' : (fmax s - run s) ≠ run s := by omega
  have hcards : s.card = u.card + 1 := by
    rw [hsu, Finset.card_insert_of_notMem hMnotu]
  have hsums : (∑ i ∈ s, i) = fmax s + ∑ i ∈ u, i := by
    conv_lhs => rw [hsu]
    rw [Finset.sum_insert hMnotu]
  have hfr : franklin s = insert (fmax s - run s) (insert (run s) u) := by
    rw [franklin, if_neg (by omega)]
  set t : Finset ℕ := insert (fmax s - run s) (insert (run s) u) with ht
  have hnotins : (fmax s - run s) ∉ insert (run s) u := by
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨hne', hMtτnotu⟩
  have hnotins2 : run s ∉ insert (fmax s - run s) u := by
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨fun h => hne' h.symm, hτnotu⟩
  have h0t : 0 ∉ t := by
    rw [ht]
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨by omega, by omega, fun h => h0 (husub h)⟩
  have htne : t.Nonempty := ⟨run s, by rw [ht]; simp⟩
  have hmem_le : ∀ a ∈ t, a ≤ fmax s - 1 := by
    intro a ha
    rw [ht] at ha
    rcases Finset.mem_insert.1 ha with h | h
    · omega
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have h1 : a ∈ s := husub h
      have h2 : a ≠ fmax s := fun hh => hMnotu (hh ▸ h)
      have := le_fmax h1
      omega
  have hM1mem : (fmax s - 1) ∈ t := by
    rcases Nat.lt_or_ge 1 (run s) with h | h
    · have h1 : fmax s - 1 ∈ s := run_mem hne h
      have h2 : fmax s - 1 ≠ fmax s := by omega
      rw [ht]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨h2, h1⟩))
    · have h3 : fmax s - run s = fmax s - 1 := by omega
      rw [ht, ← h3]
      exact Finset.mem_insert_self _ _
  have hmaxt : fmax t = fmax s - 1 := le_antisymm (hmem_le _ (fmax_mem htne)) (le_fmax hM1mem)
  have hmem_ge : ∀ a ∈ t, run s ≤ a := by
    intro a ha
    rw [ht] at ha
    rcases Finset.mem_insert.1 ha with h | h
    · omega
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have := fmin_le (husub h); omega
  have hmint : fmin t = run s :=
    le_antisymm (fmin_le (by rw [ht]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      (hmem_ge _ (fmin_mem htne))
  have hrunt : run s ≤ run t := by
    by_contra hcon
    push_neg at hcon
    have h1 : 0 < run t := run_pos h0t
    refine run_notMem h0t ?_
    rw [hmaxt]
    have h2 : fmax s - 1 - run t = fmax s - (run t + 1) := by omega
    rw [h2]
    rcases Nat.lt_or_ge (run t + 1) (run s) with h | h
    · have h3 : fmax s - (run t + 1) ∈ s := run_mem hne h
      have h4 : fmax s - (run t + 1) ≠ fmax s := by omega
      rw [ht]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h4, h3⟩))
    · have h5 : run t + 1 = run s := by omega
      rw [ht, h5]
      exact Finset.mem_insert_self _ _
  refine ⟨by rwa [hfr], ?_, ?_, ?_, ?_⟩
  · rw [hfr, ht, Finset.sum_insert hnotins, Finset.sum_insert hτnotu, hsums]
    omega
  · rw [hfr, ht, Finset.card_insert_of_notMem hnotins,
      Finset.card_insert_of_notMem hτnotu, hcards]
  · rw [hfr]
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · rw [hmaxt, hmint] at h; omega
    · rw [hmint] at h; omega
  · rw [hfr, franklin, if_pos (by omega), hmaxt, hmint]
    have h1 : fmax s - 1 - run s + 1 = fmax s - run s := by omega
    have h2 : fmax s - 1 + 1 = fmax s := by omega
    rw [h1, h2, ht, Finset.insert_comm, Finset.erase_insert hnotins2,
      Finset.erase_insert hMtτnotu, ← hsu]

/-! ### Facts about intervals -/

lemma sum_Icc_id (a b : ℕ) (h : a ≤ b + 1) :
    (∑ i ∈ Finset.Icc a b, i) * 2 + a * (a - 1) = (b + 1) * b := by
  have h1 : (∑ i ∈ Finset.Ico 0 a, i) + (∑ i ∈ Finset.Ico a (b + 1), i)
      = ∑ i ∈ Finset.Ico 0 (b + 1), i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le a) h
  rw [← Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc] at h1
  have h2 := Finset.sum_range_id_mul_two a
  have h3 := Finset.sum_range_id_mul_two (b + 1)
  simp only [Nat.add_sub_cancel] at h3
  generalize a * (a - 1) = X at h2 ⊢
  generalize (b + 1) * b = Y at h3 ⊢
  omega

lemma fmin_Icc {a b : ℕ} (h : a ≤ b) : fmin (Finset.Icc a b) = a := by
  have hne : (Finset.Icc a b).Nonempty := ⟨a, by simp [h]⟩
  refine le_antisymm (fmin_le (by simp [h])) ?_
  exact (Finset.mem_Icc.1 (fmin_mem hne)).1

lemma fmax_Icc {a b : ℕ} (h : a ≤ b) : fmax (Finset.Icc a b) = b := by
  have hne : (Finset.Icc a b).Nonempty := ⟨a, by simp [h]⟩
  refine le_antisymm ?_ (le_fmax (by simp [h]))
  exact (Finset.mem_Icc.1 (fmax_mem hne)).2

lemma zero_notMem_Icc {a b : ℕ} (h : 1 ≤ a) : (0 : ℕ) ∉ Finset.Icc a b := by
  simp only [Finset.mem_Icc]
  omega

lemma run_Icc {a b : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ b) : run (Finset.Icc a b) = b - a + 1 := by
  have h0 : (0 : ℕ) ∉ Finset.Icc a b := zero_notMem_Icc h1
  have hne : (Finset.Icc a b).Nonempty := ⟨a, by simp [h2]⟩
  have hmax : fmax (Finset.Icc a b) = b := fmax_Icc h2
  have hle : run (Finset.Icc a b) ≤ b - a + 1 := by
    refine Nat.sInf_le ⟨by omega, ?_⟩
    rw [hmax]
    simp only [Finset.mem_Icc]
    omega
  by_contra hcon
  have hlt : run (Finset.Icc a b) < b - a + 1 := lt_of_le_of_ne hle hcon
  have hpos : 0 < run (Finset.Icc a b) := run_pos h0
  refine run_notMem h0 ?_
  rw [hmax]
  simp only [Finset.mem_Icc]
  omega

/-! ### The involution kills the non-exceptional part -/

lemma franklin_props {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (hexc : ¬ isExc s) :
    0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = (∑ i ∈ s, i) ∧
      ((franklin s).card + 1 = s.card ∨ s.card + 1 = (franklin s).card) ∧
      ¬ isExc (franklin s) ∧ franklin (franklin s) = s := by
  by_cases hA : fmin s ≤ run s
  · have hnexc : fmax s + 1 ≠ 2 * fmin s := fun h => hexc (Or.inl ⟨hA, h⟩)
    obtain ⟨a, b, c, d, e⟩ := caseA h0 hne hA hnexc
    exact ⟨a, b, Or.inl c, d, e⟩
  · have hA' : run s < fmin s := by omega
    have hnexc : fmax s ≠ 2 * run s := fun h => hexc (Or.inr ⟨hA', h⟩)
    obtain ⟨a, b, c, d, e⟩ := caseB h0 hne hA hnexc
    exact ⟨a, b, Or.inr c, d, e⟩

lemma neg_one_pow_add {b c : ℕ} (h : b + 1 = c ∨ c + 1 = b) :
    (-1 : ℤ) ^ b + (-1 : ℤ) ^ c = 0 := by
  rcases h with h | h <;> subst h <;> rw [pow_succ] <;> ring

lemma mem_filter_props {n : ℕ} {s : Finset ℕ} (hn : 1 ≤ n)
    (hs : s ∈ (D n).filter (fun s => ¬ isExc s)) :
    0 ∉ s ∧ s.Nonempty ∧ (∑ i ∈ s, i) = n ∧ ¬ isExc s := by
  rw [Finset.mem_filter, mem_D_iff] at hs
  obtain ⟨⟨h0, hsum⟩, hexc⟩ := hs
  refine ⟨h0, ?_, hsum, hexc⟩
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  simp at hsum
  omega

lemma sum_nonExc_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∑ s ∈ (D n).filter (fun s => ¬ isExc s), (-1 : ℤ) ^ s.card = 0 := by
  have key : ∀ s ∈ (D n).filter (fun s => ¬ isExc s),
      0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = n ∧
        ((franklin s).card + 1 = s.card ∨ s.card + 1 = (franklin s).card) ∧
        ¬ isExc (franklin s) ∧ franklin (franklin s) = s := by
    intro s hs
    obtain ⟨h0, hne, hsum, hexc⟩ := mem_filter_props hn hs
    obtain ⟨a, b, c, d, e⟩ := franklin_props h0 hne hexc
    exact ⟨a, by rw [b, hsum], c, d, e⟩
  have g_mem : ∀ s (hs : s ∈ (D n).filter (fun s => ¬ isExc s)),
      franklin s ∈ (D n).filter (fun s => ¬ isExc s) := by
    intro s hs
    obtain ⟨a, b, _, d, _⟩ := key s hs
    rw [Finset.mem_filter, mem_D_iff]
    exact ⟨⟨a, b⟩, d⟩
  refine Finset.sum_involution (fun s _ => franklin s) (fun s hs => ?_) (fun s hs _ => ?_)
    g_mem (fun s hs => ?_)
  · show (-1 : ℤ) ^ s.card + (-1 : ℤ) ^ (franklin s).card = 0
    exact neg_one_pow_add (Or.symm (key s hs).2.2.1)
  · show franklin s ≠ s
    intro hcon
    have := (key s hs).2.2.1
    rw [hcon] at this
    omega
  · exact (key s hs).2.2.2.2

/-! ### The exceptional partitions -/

lemma exc_eq {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (h : isExc s) :
    s = Finset.Icc (fmin s) (fmax s) ∧
      (fmax s + 1 = 2 * fmin s ∨ fmax s + 2 = 2 * fmin s) := by
  have hσM : fmin s ≤ fmax s := le_fmax (fmin_mem hne)
  have hσpos : 0 < fmin s := fmin_pos h0 hne
  have hτpos : 0 < run s := run_pos h0
  have hd : fmax s - fmin s < run s ∧ (fmax s + 1 = 2 * fmin s ∨ fmax s + 2 = 2 * fmin s) := by
    rcases h with ⟨hA, hE⟩ | ⟨hB, hE⟩
    · exact ⟨by omega, Or.inl hE⟩
    · have h1 : run s - 1 < run s := by omega
      have h3 := fmin_le (run_mem hne h1)
      exact ⟨by omega, Or.inr (by omega)⟩
  refine ⟨Finset.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_), hd.2⟩
  · simp only [Finset.mem_Icc]
    exact ⟨fmin_le ha, le_fmax ha⟩
  · rw [Finset.mem_Icc] at ha
    have h1 : fmax s - a < run s := by omega
    have h2 := run_mem hne h1
    have h3 : fmax s - (fmax s - a) = a := by omega
    rwa [h3] at h2

lemma exc_classify {n : ℕ} (hn : 1 ≤ n) {s : Finset ℕ} (hs : s ∈ (D n).filter isExc) :
    ∃ m : ℕ, 1 ≤ m ∧
      ((s = Finset.Icc m (2 * m - 1) ∧ s.card = m ∧ fmax s + 1 = 2 * fmin s ∧
          2 * n = m * (3 * m - 1)) ∨
       (s = Finset.Icc (m + 1) (2 * m) ∧ s.card = m ∧ fmax s + 1 ≠ 2 * fmin s ∧
          2 * n = m * (3 * m + 1))) := by
  rw [Finset.mem_filter, mem_D_iff] at hs
  obtain ⟨⟨h0, hsum⟩, hexc⟩ := hs
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hsum
    omega
  obtain ⟨hIcc, hcase⟩ := exc_eq h0 hne hexc
  have hσM : fmin s ≤ fmax s := le_fmax (fmin_mem hne)
  have hσpos : 0 < fmin s := fmin_pos h0 hne
  have hcard : s.card = fmax s + 1 - fmin s := by
    conv_lhs => rw [hIcc]
    rw [Nat.card_Icc]
  have hsum2 : n * 2 + fmin s * (fmin s - 1) = (fmax s + 1) * fmax s := by
    have h := sum_Icc_id (fmin s) (fmax s) (by omega)
    rw [← hIcc, hsum] at h
    exact h
  rcases hcase with hE | hE
  · refine ⟨fmin s, hσpos, Or.inl ⟨?_, ?_, hE, ?_⟩⟩
    · have e1 : 2 * fmin s - 1 = fmax s := by omega
      rw [e1]; exact hIcc
    · omega
    · obtain ⟨m, hm⟩ : ∃ m, fmin s = m + 1 := ⟨fmin s - 1, by omega⟩
      have hM : fmax s = 2 * m + 1 := by omega
      rw [hm, hM] at hsum2
      simp only [Nat.add_sub_cancel] at hsum2
      rw [hm]
      have h1 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
      rw [h1]
      nlinarith [hsum2]
  · have hτ : 2 ≤ fmin s := by omega
    refine ⟨fmin s - 1, by omega, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · have e1 : fmin s - 1 + 1 = fmin s := by omega
      have e2 : 2 * (fmin s - 1) = fmax s := by omega
      rw [e1, e2]; exact hIcc
    · omega
    · omega
    · obtain ⟨m, hm⟩ : ∃ m, fmin s = m + 1 := ⟨fmin s - 1, by omega⟩
      have hM : fmax s = 2 * m := by omega
      rw [hm, hM] at hsum2
      simp only [Nat.add_sub_cancel] at hsum2
      have h2 : fmin s - 1 = m := by omega
      rw [h2]
      nlinarith [hsum2]

lemma Icc1_mem_exc {n m : ℕ} (hm : 1 ≤ m) (h : 2 * n = m * (3 * m - 1)) :
    Finset.Icc m (2 * m - 1) ∈ (D n).filter isExc := by
  have hle : m ≤ 2 * m - 1 := by omega
  have h0 : (0 : ℕ) ∉ Finset.Icc m (2 * m - 1) := zero_notMem_Icc hm
  have hmin : fmin (Finset.Icc m (2 * m - 1)) = m := fmin_Icc hle
  have hmax : fmax (Finset.Icc m (2 * m - 1)) = 2 * m - 1 := fmax_Icc hle
  have hrun : run (Finset.Icc m (2 * m - 1)) = m := by
    rw [run_Icc hm hle]; omega
  have hsum : (∑ i ∈ Finset.Icc m (2 * m - 1), i) = n := by
    have h1 := sum_Icc_id m (2 * m - 1) (by omega)
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    subst hm'
    have h2 : 2 * (m' + 1) - 1 + 1 = 2 * m' + 2 := by omega
    have h3 : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
    have h4 : 3 * (m' + 1) - 1 = 3 * m' + 2 := by omega
    rw [h3] at h1 ⊢
    rw [h4] at h
    simp only [Nat.add_sub_cancel] at h1
    nlinarith [h1, h]
  rw [Finset.mem_filter, mem_D_iff]
  refine ⟨⟨h0, hsum⟩, Or.inl ⟨by omega, by omega⟩⟩

lemma Icc2_mem_exc {n m : ℕ} (hm : 1 ≤ m) (h : 2 * n = m * (3 * m + 1)) :
    Finset.Icc (m + 1) (2 * m) ∈ (D n).filter isExc := by
  have hle : m + 1 ≤ 2 * m := by omega
  have h0 : (0 : ℕ) ∉ Finset.Icc (m + 1) (2 * m) := zero_notMem_Icc (by omega)
  have hmin : fmin (Finset.Icc (m + 1) (2 * m)) = m + 1 := fmin_Icc hle
  have hmax : fmax (Finset.Icc (m + 1) (2 * m)) = 2 * m := fmax_Icc hle
  have hrun : run (Finset.Icc (m + 1) (2 * m)) = m := by
    rw [run_Icc (by omega) hle]; omega
  have hsum : (∑ i ∈ Finset.Icc (m + 1) (2 * m), i) = n := by
    have h1 := sum_Icc_id (m + 1) (2 * m) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    nlinarith [h1, h]
  rw [Finset.mem_filter, mem_D_iff]
  refine ⟨⟨h0, hsum⟩, Or.inr ⟨by omega, by omega⟩⟩

/-! ### Matching the exceptional partitions with pentagonal indices -/

/-- The (generalized) pentagonal index attached to an exceptional partition. -/
noncomputable def excIdx (s : Finset ℕ) : ℤ :=
  if fmax s + 1 = 2 * fmin s then (s.card : ℤ) else -(s.card : ℤ)

/-- The exceptional partition attached to a pentagonal index. -/
noncomputable def idxSet (k : ℤ) : Finset ℕ :=
  if 0 < k then Finset.Icc k.toNat (2 * k.toNat - 1)
  else Finset.Icc ((-k).toNat + 1) (2 * (-k).toNat)

lemma excIdx_Icc1 {m : ℕ} (hm : 1 ≤ m) : excIdx (Finset.Icc m (2 * m - 1)) = (m : ℤ) := by
  have hle : m ≤ 2 * m - 1 := by omega
  have hmin : fmin (Finset.Icc m (2 * m - 1)) = m := fmin_Icc hle
  have hmax : fmax (Finset.Icc m (2 * m - 1)) = 2 * m - 1 := fmax_Icc hle
  have hcard : (Finset.Icc m (2 * m - 1)).card = m := by rw [Nat.card_Icc]; omega
  rw [excIdx, if_pos (by omega), hcard]

lemma excIdx_Icc2 {m : ℕ} (hm : 1 ≤ m) : excIdx (Finset.Icc (m + 1) (2 * m)) = -(m : ℤ) := by
  have hle : m + 1 ≤ 2 * m := by omega
  have hmin : fmin (Finset.Icc (m + 1) (2 * m)) = m + 1 := fmin_Icc hle
  have hmax : fmax (Finset.Icc (m + 1) (2 * m)) = 2 * m := fmax_Icc hle
  have hcard : (Finset.Icc (m + 1) (2 * m)).card = m := by rw [Nat.card_Icc]; omega
  rw [excIdx, if_neg (by omega), hcard]

lemma idxSet_pos {k : ℤ} (hk : 0 < k) : idxSet k = Finset.Icc k.toNat (2 * k.toNat - 1) := by
  rw [idxSet, if_pos hk]

lemma idxSet_neg {k : ℤ} (hk : k < 0) :
    idxSet k = Finset.Icc ((-k).toNat + 1) (2 * (-k).toNat) := by
  rw [idxSet, if_neg (by omega)]

lemma pent_le1 {n m : ℕ} (hm : 1 ≤ m) (h : 2 * n = m * (3 * m - 1)) : m ≤ n := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h4 : 3 * (m' + 1) - 1 = 3 * m' + 2 := by omega
  rw [h4] at h
  nlinarith

lemma pent_le2 {n m : ℕ} (hm : 1 ≤ m) (h : 2 * n = m * (3 * m + 1)) : m ≤ n := by
  nlinarith

lemma sum_exc (n : ℕ) (hn : 1 ≤ n) :
    ∑ s ∈ (D n).filter isExc, (-1 : ℤ) ^ s.card
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun k => (2 * n : ℤ) = k * (3 * k - 1)),
          (-1 : ℤ) ^ k.natAbs := by
  refine Finset.sum_nbij' excIdx idxSet ?_ ?_ ?_ ?_ ?_
  · -- excIdx maps into the index set
    intro s hs
    obtain ⟨m, hm, hcase⟩ := exc_classify hn hs
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hcase with ⟨hIcc, hcard, hcond, hsum⟩ | ⟨hIcc, hcard, hcond, hsum⟩
    · have hidx : excIdx s = (m : ℤ) := by rw [excIdx, if_pos hcond, hcard]
      have hmn : m ≤ n := pent_le1 hm hsum
      have hz : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) - 1) := by
        have h1 : (1 : ℕ) ≤ 3 * m := by omega
        zify [h1] at hsum
        linarith
      have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
      rw [hidx]
      exact ⟨⟨by omega, hmn'⟩, by linear_combination hz⟩
    · have hidx : excIdx s = -(m : ℤ) := by rw [excIdx, if_neg hcond, hcard]
      have hmn : m ≤ n := pent_le2 hm hsum
      have hz : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) + 1) := by exact_mod_cast hsum
      have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
      rw [hidx]
      exact ⟨⟨by omega, by omega⟩, by linear_combination hz⟩
  · -- idxSet maps back
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨-, hkeq⟩ := hk
    rcases lt_trichotomy k 0 with hneg | hzero | hpos
    · rw [idxSet_neg hneg]
      set m := (-k).toNat with hm
      have hk' : k = -(m : ℤ) := by omega
      have hm1 : 1 ≤ m := by omega
      refine Icc2_mem_exc hm1 ?_
      have : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) + 1) := by rw [hk'] at hkeq; linarith [hkeq]
      exact_mod_cast this
    · exfalso; rw [hzero] at hkeq; simp at hkeq; omega
    · rw [idxSet_pos hpos]
      set m := k.toNat with hm
      have hk' : k = (m : ℤ) := by omega
      have hm1 : 1 ≤ m := by omega
      refine Icc1_mem_exc hm1 ?_
      have h1 : (1 : ℕ) ≤ 3 * m := by omega
      have : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) - 1) := by rw [hk'] at hkeq; linarith [hkeq]
      zify [h1]
      linarith
  · -- left inverse
    intro s hs
    obtain ⟨m, hm, hcase⟩ := exc_classify hn hs
    rcases hcase with ⟨hIcc, hcard, hcond, -⟩ | ⟨hIcc, hcard, hcond, -⟩
    · have hidx : excIdx s = (m : ℤ) := by rw [excIdx, if_pos hcond, hcard]
      rw [hidx, idxSet_pos (by exact_mod_cast hm), Int.toNat_natCast, hIcc]
    · have hidx : excIdx s = -(m : ℤ) := by rw [excIdx, if_neg hcond, hcard]
      rw [hidx, idxSet_neg (by simp; omega), neg_neg, Int.toNat_natCast, hIcc]
  · -- right inverse
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨-, hkeq⟩ := hk
    rcases lt_trichotomy k 0 with hneg | hzero | hpos
    · rw [idxSet_neg hneg]
      set m := (-k).toNat with hm
      have hm1 : 1 ≤ m := by omega
      rw [excIdx_Icc2 hm1]
      omega
    · exfalso; rw [hzero] at hkeq; simp at hkeq; omega
    · rw [idxSet_pos hpos]
      set m := k.toNat with hm
      have hm1 : 1 ≤ m := by omega
      rw [excIdx_Icc1 hm1]
      omega
  · -- the summands match
    intro s hs
    obtain ⟨m, hm, hcase⟩ := exc_classify hn hs
    rcases hcase with ⟨-, hcard, hcond, -⟩ | ⟨-, hcard, hcond, -⟩
    · have hidx : excIdx s = (m : ℤ) := by rw [excIdx, if_pos hcond, hcard]
      rw [hidx, hcard]
      simp
    · have hidx : excIdx s = -(m : ℤ) := by rw [excIdx, if_neg hcond, hcard]
      rw [hidx, hcard]
      simp

/-! ### Euler's pentagonal number theorem -/

lemma D_zero : D 0 = {∅} := by
  ext s
  rw [mem_D_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨h0, hsum⟩
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
    have h1 : a ≤ 0 :=
      hsum ▸ Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) ha
    exact h0 (by simpa [Nat.le_zero.1 h1] using ha)
  · rintro rfl
    simp

/-- **Euler's pentagonal number theorem.**

`D n` is the set of partitions of `n` into distinct positive parts (encoded as finite sets of
positive naturals with sum `n`), so the left-hand side is the coefficient of `X ^ n` in the
infinite product `∏_{i ≥ 1} (1 - X ^ i)`, the reciprocal of the partition generating function.
The right-hand side is `(-1) ^ k` if `n` is the generalized pentagonal number `k (3k - 1) / 2`
for some `k : ℤ`, and `0` otherwise. -/
theorem euler_pentagonal (n : ℕ) :
    ∑ s ∈ D n, (-1 : ℤ) ^ s.card
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          if (2 * n : ℤ) = k * (3 * k - 1) then (-1 : ℤ) ^ k.natAbs else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [D_zero]
    norm_num
  · rw [← Finset.sum_filter_add_sum_filter_not (D n) isExc (fun s => (-1 : ℤ) ^ s.card),
      sum_nonExc_eq_zero n hn, add_zero, sum_exc n hn, Finset.sum_filter]

/-! ### The generating function form -/

lemma D_eq_powerset_filter {n N : ℕ} (h : n ≤ N) :
    D n = (Finset.Icc 1 N).powerset.filter (fun s => ∑ i ∈ s, i = n) := by
  ext s
  rw [mem_D_iff, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum⟩
    have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (fun hh => h0 (hh ▸ ha))
    have h2 : a ≤ n :=
      hsum ▸ Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) ha
    rw [Finset.mem_Icc]
    omega
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this

lemma prod_one_sub_X_pow_eq (N : ℕ) :
    (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ t ∈ (Finset.Icc 1 N).powerset,
          PowerSeries.C ((-1 : ℤ) ^ t.card) * PowerSeries.X ^ (∑ i ∈ t, i) := by
  have h0 : (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∏ i ∈ Finset.Icc 1 N, ((-((PowerSeries.X : PowerSeries ℤ) ^ i)) + 1) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  rw [h0, Finset.prod_add]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_pow_eq_pow_sum,
    map_pow, map_neg, map_one]

/-- **Euler's pentagonal number theorem, generating function form.**

For `n ≤ N`, the coefficient of `X ^ n` in the finite product `∏_{i = 1}^{N} (1 - X ^ i)`
(which agrees with the coefficient in the infinite product `∏_{i ≥ 1} (1 - X ^ i)`, the
reciprocal of the partition generating function) is `(-1) ^ k` if `n` is the generalized
pentagonal number `k (3k - 1) / 2` for some `k : ℤ`, and `0` otherwise. -/
theorem euler_pentagonal_generatingFunction {n N : ℕ} (h : n ≤ N) :
    PowerSeries.coeff n (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          if (2 * n : ℤ) = k * (3 * k - 1) then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [prod_one_sub_X_pow_eq, map_sum]
  have hterm : ∀ t ∈ (Finset.Icc 1 N).powerset,
      PowerSeries.coeff n (PowerSeries.C ((-1 : ℤ) ^ t.card) * PowerSeries.X ^ (∑ i ∈ t, i))
        = if (∑ i ∈ t, i) = n then (-1 : ℤ) ^ t.card else 0 := by
    intro t _
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    by_cases hc : (∑ i ∈ t, i) = n
    · rw [if_pos hc.symm, if_pos hc, mul_one]
    · rw [if_neg (fun hh => hc hh.symm), if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← D_eq_powerset_filter h,
    euler_pentagonal]

end Math

