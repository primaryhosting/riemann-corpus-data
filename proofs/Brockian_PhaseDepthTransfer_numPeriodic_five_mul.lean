import Mathlib

namespace Brockian.PhaseDepthTransfer

variable {A : Type*} [AddCommGroup A]

def transfer (c : ZMod 5 → A) : ZMod 5 × A → ZMod 5 × A := fun x => (x.1 + 1, x.2 + c x.1)

def totalDepth (c : ZMod 5 → A) : A := ∑ j, c j

/-- first-coordinate law: after n steps the residue is shifted by n. -/
theorem transfer_fst_iterate (c : ZMod 5 → A) (n : ℕ) (x : ZMod 5 × A) :
    ((transfer c)^[n] x).1 = x.1 + (n : ZMod 5) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show ((transfer c)^[k] x).1 + 1 = x.1 + ((k + 1 : ℕ) : ZMod 5)
    rw [ih]
    push_cast
    abel

/-- one circuit returns the residue and translates the fiber by the total holonomy, from EVERY start. -/
theorem transfer_iterate_five (c : ZMod 5 → A) (x : ZMod 5 × A) :
    (transfer c)^[5] x = (x.1, x.2 + totalDepth c) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, transfer]
  apply Prod.ext
  · show x.1 + 1 + 1 + 1 + 1 + 1 = x.1
    have h5 : (5 : ZMod 5) = 0 := by decide
    have : x.1 + 1 + 1 + 1 + 1 + 1 = x.1 + (5 : ZMod 5) := by push_cast; abel
    rw [this, h5, add_zero]
  · show x.2 + c x.1 + c (x.1 + 1) + c (x.1 + 1 + 1) + c (x.1 + 1 + 1 + 1) + c (x.1 + 1 + 1 + 1 + 1)
        = x.2 + totalDepth c
    -- reindex totalDepth by adding x.1
    have hreindex : totalDepth c = ∑ k : ZMod 5, c (x.1 + k) := by
      unfold totalDepth
      rw [← Equiv.sum_comp (Equiv.addLeft x.1) c]
      rfl
    have huniv : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
    rw [hreindex, huniv]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    have e0 : x.1 + (0 : ZMod 5) = x.1 := by abel
    have e1 : x.1 + (1 : ZMod 5) = x.1 + 1 := by rfl
    have e2 : x.1 + (2 : ZMod 5) = x.1 + 1 + 1 := by
      have : (2 : ZMod 5) = 1 + 1 := by decide
      rw [this, ← add_assoc]
    have e3 : x.1 + (3 : ZMod 5) = x.1 + 1 + 1 + 1 := by
      have : (3 : ZMod 5) = 1 + 1 + 1 := by decide
      rw [this, ← add_assoc, ← add_assoc]
    have e4 : x.1 + (4 : ZMod 5) = x.1 + 1 + 1 + 1 + 1 := by
      have : (4 : ZMod 5) = 1 + 1 + 1 + 1 := by decide
      rw [this, ← add_assoc, ← add_assoc, ← add_assoc]
    rw [e0, e1, e2, e3, e4]
    abel

/-- 5r circuits translate the fiber by r copies of the holonomy. -/
theorem transfer_iterate_five_mul (c : ZMod 5 → A) (r : ℕ) (x : ZMod 5 × A) :
    (transfer c)^[5*r] x = (x.1, x.2 + r • totalDepth c) := by
  induction r with
  | zero => simp
  | succ k ih =>
    have hmul : 5 * (k + 1) = 5 + 5 * k := by ring
    rw [hmul, Function.iterate_add_apply, ih, transfer_iterate_five]
    apply Prod.ext
    · rfl
    · show x.2 + k • totalDepth c + totalDepth c = x.2 + (k + 1) • totalDepth c
      rw [succ_nsmul]
      abel

/-- off-resonance: 5 ∤ m ⇒ no period-m point ⇒ Tr(T^m)=0. -/
theorem transfer_no_fixed_of_not_dvd (c : ZMod 5 → A) {m : ℕ} (hm : ¬ (5 ∣ m))
    (x : ZMod 5 × A) : (transfer c)^[m] x ≠ x := by
  intro hfix
  apply hm
  have hfst : ((transfer c)^[m] x).1 = x.1 := by rw [hfix]
  rw [transfer_fst_iterate] at hfst
  have hzero : (m : ZMod 5) = 0 := by
    have := hfst
    -- x.1 + (m : ZMod 5) = x.1
    have h2 : x.1 + (m : ZMod 5) = x.1 + 0 := by rw [add_zero]; exact this
    exact add_left_cancel h2
  exact (CharP.cast_eq_zero_iff (ZMod 5) 5 m).mp hzero

variable [Fintype A] [DecidableEq A]

def numPeriodic (c : ZMod 5 → A) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : ZMod 5 × A => (transfer c)^[n] x = x)).card

/-- **Transfer trace identity.** Tr(T_c^{5r}) = 5 · Tr(ρ(Hol)^r): the 5r-th trace equals 5×
    the number of fiber points fixed by r copies of the holonomy translation. -/
theorem numPeriodic_five_mul (c : ZMod 5 → A) (r : ℕ) :
    numPeriodic c (5 * r) = 5 * (Finset.univ.filter (fun a : A => a + r • totalDepth c = a)).card := by
  unfold numPeriodic
  have hpred : ∀ x : ZMod 5 × A, ((transfer c)^[5 * r] x = x) ↔ (x.2 + r • totalDepth c = x.2) := by
    intro x
    rw [transfer_iterate_five_mul, Prod.ext_iff]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h2; exact ⟨rfl, h2⟩
  have hset : (Finset.univ.filter (fun x : ZMod 5 × A => (transfer c)^[5 * r] x = x))
      = (Finset.univ : Finset (ZMod 5)) ×ˢ (Finset.univ.filter (fun a : A => a + r • totalDepth c = a)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [hpred x]
  rw [hset, Finset.card_product, Finset.card_univ, ZMod.card]

/-- off-resonance trace vanishing: Tr(T_c^m) = 0 for 5 ∤ m. -/
theorem numPeriodic_eq_zero_of_not_dvd (c : ZMod 5 → A) {m : ℕ} (hm : ¬ (5 ∣ m)) :
    numPeriodic c m = 0 := by
  unfold numPeriodic
  have hempty : (Finset.univ.filter (fun x : ZMod 5 × A => (transfer c)^[m] x = x)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _
    exact transfer_no_fixed_of_not_dvd c hm x
  rw [hempty, Finset.card_empty]

end Brockian.PhaseDepthTransfer
