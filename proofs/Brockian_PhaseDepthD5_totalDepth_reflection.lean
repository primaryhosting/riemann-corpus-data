import Mathlib

/-!
# The REAL D₅ (pentagon) symmetry of the phase-depth construction

We realise the genuine dihedral group `DihedralGroup 5` (order 10, the pentagon's full
symmetry group) as a group action on the pentagonal residue cycle `ZMod 5`, and prove the
covariance of the directed holonomy `totalDepth c = ∑ j, c j` of a roof `c : ZMod 5 → A`:

* rotations preserve the directed holonomy;
* reflections reverse orientation, hence negate the directed holonomy;
* consequently the quantity fixed by ALL of `D₅` is the unordered ±-pair
  `{totalDepth c, -totalDepth c}`.

### Honesty note on the reflection formula
Mathlib's `DihedralGroup` multiplication satisfies `sr i * sr j = r (j - i)`
(`DihedralGroup.sr_mul_sr`).  Under this convention a LEFT action with rotation
`r k : j ↦ j + k` is forced to send the reflection `sr k` to `j ↦ -k - j` (= `-(j+k)`);
the naive formula `j ↦ k - j` is NOT a left action (it fails the `sr * sr` law — verified
by `decide`).  Both are orientation-reversing (coefficient `-1` on `j`), so the reflection
still negates the *directed* holonomy exactly as intended.  We therefore use the true
`sr k : j ↦ -k - j`.  A plain reindexed sum is reflection-INVARIANT, so the negation is
supplied by the reversed directed step (`reverseRoof`), not by the reindexing.
-/

namespace Brockian.PhaseDepthD5

open DihedralGroup

variable {A : Type*} [AddCommGroup A]

/-- The `DihedralGroup 5` action on the pentagonal residue cycle `ZMod 5`:
rotation `r k` translates by `k`; reflection `sr k` is the orientation-reversing
involution `j ↦ -k - j`. -/
def act : DihedralGroup 5 → ZMod 5 → ZMod 5
  | r k, j => j + k
  | sr k, j => -k - j

@[simp] theorem act_r (k j : ZMod 5) : act (r k) j = j + k := rfl
@[simp] theorem act_sr (k j : ZMod 5) : act (sr k) j = -k - j := rfl

/-- `act 1 = id` (identity element is `r 0`). -/
theorem act_one (j : ZMod 5) : act 1 j = j := by
  rw [one_def, act_r, add_zero]

/-- `act (g * h) = act g ∘ act h`: `act` is a genuine left action of `DihedralGroup 5`.
Proved by case analysis on `g, h` using Mathlib's dihedral multiplication laws
(`r_mul_r`, `r_mul_sr`, `sr_mul_r`, `sr_mul_sr`), NOT by `decide`. -/
theorem act_mul (g h : DihedralGroup 5) (j : ZMod 5) :
    act (g * h) j = act g (act h j) := by
  cases g with
  | r a =>
    cases h with
    | r b => rw [r_mul_r, act_r, act_r, act_r]; abel
    | sr b => rw [r_mul_sr, act_sr, act_sr, act_r]; abel
  | sr a =>
    cases h with
    | r b => rw [sr_mul_r, act_sr, act_r, act_sr]; abel
    | sr b => rw [sr_mul_sr, act_r, act_sr, act_sr]; abel

/-- Package the action as a genuine `MulAction (DihedralGroup 5) (ZMod 5)`. -/
instance : MulAction (DihedralGroup 5) (ZMod 5) where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

/-- The directed holonomy (total phase depth) of a roof `c` over the pentagon. -/
def totalDepth (c : ZMod 5 → A) : A := ∑ j, c j

/-! ## 2. Rotation-invariance of the directed holonomy. -/

/-- Any rotation `r k` preserves the total directed holonomy: reindex the cyclic sum by
the bijection `j ↦ j + k`. -/
theorem totalDepth_rotation (c : ZMod 5 → A) (k : ZMod 5) :
    totalDepth (fun j => c (act (r k) j)) = totalDepth c := by
  unfold totalDepth
  simp only [act_r]
  exact Equiv.sum_comp (Equiv.addRight k) c

/-! ## 3. Reflection reverses orientation ⇒ negates the DIRECTED holonomy.

A plain reindexed sum is reflection-INVARIANT: `∑ j, c (act (sr k) j) = ∑ j, c j`, because
`j ↦ -k - j` is a bijection of `ZMod 5`.  The negation is a genuinely orientation-aware
fact: traversing the cycle in reverse accumulates the roof with a flipped directed step. -/

/-- The plain (undirected) pullback sum is reflection-INVARIANT — this is exactly why the
directed negation must come from reversing the step, not from the reindexing. -/
theorem totalDepth_reflection_invariant (c : ZMod 5 → A) (k : ZMod 5) :
    (∑ j : ZMod 5, c (act (sr k) j)) = ∑ j : ZMod 5, c j := by
  simp only [act_sr]
  exact Equiv.sum_comp (Equiv.subLeft (-k)) c

/-- The reversed roof of `c` under the reflection `sr k`: the roof pulled back along the
reflected cycle **with the directed step flipped** (an explicit sign). -/
def reverseRoof (c : ZMod 5 → A) (k : ZMod 5) : ZMod 5 → A :=
  fun j => - c (act (sr k) j)

/-- Orientation reversal negates the directed holonomy: the reversed directed holonomy of
`c` under any reflection `sr k` equals `-totalDepth c`. -/
theorem totalDepth_reflection (c : ZMod 5 → A) (k : ZMod 5) :
    totalDepth (reverseRoof c k) = - totalDepth c := by
  unfold totalDepth reverseRoof
  rw [Finset.sum_neg_distrib, totalDepth_reflection_invariant]

/-! ## 4. The reflection invariant is the ±-class. -/

/-- **Headline: `d5_covariance`.** The full `D₅` covariance of the directed holonomy:
every rotation fixes `totalDepth c`, and every reflection sends the reversed directed
holonomy to `-totalDepth c`. -/
theorem d5_covariance (c : ZMod 5 → A) (k : ZMod 5) :
    totalDepth (fun j => c (act (r k) j)) = totalDepth c
      ∧ totalDepth (reverseRoof c k) = - totalDepth c :=
  ⟨totalDepth_rotation c k, totalDepth_reflection c k⟩

/-- The quantity preserved by ALL of `D₅` is the unordered pair `{totalDepth c, -totalDepth c}`:
rotations keep `totalDepth c`, reflections send it to its negation, and the ±-class as a
whole is invariant. -/
theorem d5_pm_class_invariant [DecidableEq A] (c : ZMod 5 → A) (k : ZMod 5) :
    ({totalDepth (fun j => c (act (r k) j)), totalDepth (reverseRoof c k)} : Finset A)
      = {totalDepth c, -totalDepth c} := by
  rw [totalDepth_rotation, totalDepth_reflection]

end Brockian.PhaseDepthD5
