import Mathlib

/-!
# Phase-2 transfer operator as a LITERAL matrix trace

The Brockian phase-depth "transfer" map on `S := ZMod 5 × A` is a permutation of the
finite set `S`.  Its permutation matrix `transferMatrix c : Matrix S S ℤ` has the property
that the trace of its `n`-th power *literally* counts the period-`n` points:

    Matrix.trace ((transferMatrix c) ^ n) = numPeriodic c n.

This makes the Phase-2 identities honest matrix traces `Tr(T^n)`:
  * `Tr(T^m) = 0` whenever `5 ∤ m` (off-resonance vanishing), and
  * `Tr(T^{5r}) = 5 · #{ a : a + r•Hol = a }` (resonance = 5 × holonomy fixed points).
-/

namespace Brockian.PhaseDepthTraceMatrix

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The transfer map on `ZMod 5 × A`: advance the residue, add the roof value. -/
def transfer (c : ZMod 5 → A) : ZMod 5 × A → ZMod 5 × A := fun x => (x.1 + 1, x.2 + c x.1)

/-- Total holonomy of the roof (sum of all fiber shifts around one circuit). -/
def totalDepth (c : ZMod 5 → A) : A := ∑ j, c j

/-- first-coordinate law: after `n` steps the residue is shifted by `n`. -/
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

/-- one circuit returns the residue and translates the fiber by the total holonomy. -/
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

/-- `5r` circuits translate the fiber by `r` copies of the holonomy. -/
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

/-- off-resonance: `5 ∤ m ⇒` no period-`m` point. -/
theorem transfer_no_fixed_of_not_dvd (c : ZMod 5 → A) {m : ℕ} (hm : ¬ (5 ∣ m))
    (x : ZMod 5 × A) : (transfer c)^[m] x ≠ x := by
  intro hfix
  apply hm
  have hfst : ((transfer c)^[m] x).1 = x.1 := by rw [hfix]
  rw [transfer_fst_iterate] at hfst
  have hzero : (m : ZMod 5) = 0 := by
    have h2 : x.1 + (m : ZMod 5) = x.1 + 0 := by rw [add_zero]; exact hfst
    exact add_left_cancel h2
  exact (CharP.cast_eq_zero_iff (ZMod 5) 5 m).mp hzero

/-- **The transfer map as an honest permutation** `σ` of the finite set `ZMod 5 × A`.
Inverse: retreat the residue and undo the fiber shift. -/
def transferPerm (c : ZMod 5 → A) : (ZMod 5 × A) ≃ (ZMod 5 × A) where
  toFun := transfer c
  invFun := fun x => (x.1 - 1, x.2 - c (x.1 - 1))
  left_inv := by
    rintro ⟨j, a⟩
    have h : j + 1 - 1 = j := by abel
    simp only [transfer, h]
    congr 1 <;> abel
  right_inv := by
    rintro ⟨j, a⟩
    have h : j - 1 + 1 = j := by abel
    simp only [transfer, h]
    congr 1 <;> abel

@[simp] lemma transferPerm_coe (c : ZMod 5 → A) : ⇑(transferPerm c) = transfer c := rfl

/-- **The permutation matrix of the transfer map**, over `ℤ`. -/
def transferMatrix (c : ZMod 5 → A) : Matrix (ZMod 5 × A) (ZMod 5 × A) ℤ :=
  (transferPerm c).toPEquiv.toMatrix

/-- Number of period-`n` points of the transfer map (fixed points of `(transfer c)^[n]`). -/
def numPeriodic (c : ZMod 5 → A) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : ZMod 5 × A => (transfer c)^[n] x = x)).card

/-- `Tr` count at resonance: the number of period-`5r` points is `5 ×` the number of
fiber points fixed by `r` copies of the holonomy translation. -/
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
      = (Finset.univ : Finset (ZMod 5)) ×ˢ
          (Finset.univ.filter (fun a : A => a + r • totalDepth c = a)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [hpred x]
  rw [hset, Finset.card_product, Finset.card_univ, ZMod.card]

/-- off-resonance: the number of period-`m` points vanishes for `5 ∤ m`. -/
theorem numPeriodic_eq_zero_of_not_dvd (c : ZMod 5 → A) {m : ℕ} (hm : ¬ (5 ∣ m)) :
    numPeriodic c m = 0 := by
  unfold numPeriodic
  have hempty : (Finset.univ.filter (fun x : ZMod 5 × A => (transfer c)^[m] x = x)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _
    exact transfer_no_fixed_of_not_dvd c hm x
  rw [hempty, Finset.card_empty]

/-- **Powers of the transfer matrix are the permutation matrices of the powers of `σ`.**
The map `σ ↦ σ.toPEquiv.toMatrix` sends composition to matrix multiplication
(`PEquiv.toMatrix_trans`), so it sends `σ^n` to `(transferMatrix c)^n`. -/
lemma transferMatrix_pow (c : ZMod 5 → A) (n : ℕ) :
    (transferMatrix c) ^ n = ((transferPerm c) ^ n).toPEquiv.toMatrix := by
  simp only [transferMatrix]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Equiv.Perm.one_def, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  | succ k ih =>
    rw [pow_succ, ih, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
        ← Equiv.Perm.mul_def, ← pow_succ']

/-- **Main theorem — the trace is literally the period-point count.**
`Tr((transferMatrix c)^n) = numPeriodic c n`: the trace of the `n`-th power of the
transfer matrix equals the number of period-`n` points of the transfer map. -/
theorem trace_transferMatrix_pow (c : ZMod 5 → A) (n : ℕ) :
    Matrix.trace ((transferMatrix c) ^ n) = (numPeriodic c n : ℤ) := by
  rw [transferMatrix_pow]
  delta Matrix.trace
  simp only [Matrix.diag_apply]
  have hsum : (∑ i : ZMod 5 × A, ((transferPerm c ^ n).toPEquiv.toMatrix) i i)
        = ∑ i : ZMod 5 × A, (if (transfer c)^[n] i = i then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff,
               Equiv.Perm.coe_pow, transferPerm_coe]
  rw [hsum, Finset.sum_boole]
  simp only [numPeriodic]

/-- **Off-resonance corollary — literal trace vanishing.**
`Tr((transferMatrix c)^m) = 0` for `5 ∤ m`. -/
theorem trace_transferMatrix_pow_eq_zero (c : ZMod 5 → A) {m : ℕ} (hm : ¬ (5 ∣ m)) :
    Matrix.trace ((transferMatrix c) ^ m) = 0 := by
  rw [trace_transferMatrix_pow, numPeriodic_eq_zero_of_not_dvd c hm, Nat.cast_zero]

/-- **Resonance corollary — literal trace `= 5 ×` holonomy fixed points.**
`Tr((transferMatrix c)^{5r}) = 5 · #{ a : a + r•Hol = a }`. -/
theorem trace_transferMatrix_pow_five_mul (c : ZMod 5 → A) (r : ℕ) :
    Matrix.trace ((transferMatrix c) ^ (5 * r))
      = 5 * (Finset.univ.filter (fun a : A => a + r • totalDepth c = a)).card := by
  rw [trace_transferMatrix_pow, numPeriodic_five_mul]
  norm_cast

end Brockian.PhaseDepthTraceMatrix
