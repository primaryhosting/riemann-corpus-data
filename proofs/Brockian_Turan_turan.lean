import Mathlib
namespace Brockian.Turan
/-- Turán's theorem (integer form): a K_{r+1}-free graph satisfies 2r·|E| ≤ (r−1)·|V|². -/
theorem turan {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 0 < r) (h : G.CliqueFree (r + 1)) :
    2 * r * G.edgeFinset.card ≤ (r - 1) * (Fintype.card V) ^ 2 := by
  -- Arithmetic fact: if `a < b` then `b * a * (a - 1) ≤ (b - 1) * a ^ 2`.
  have harith : ∀ a b : ℕ, a < b → b * (a * (a - 1)) ≤ (b - 1) * a ^ 2 := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · simp [h0]
    · obtain ⟨t, rfl⟩ : ∃ t, a = t + 1 := ⟨a - 1, by omega⟩
      obtain ⟨u, rfl⟩ : ∃ u, b = u + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have ht : t + 1 ≤ u := by omega
      nlinarith
  set n := Fintype.card V with hn
  set s := n % r with hs
  have hsr : s < r := Nat.mod_lt _ hr
  have hsn : s ≤ n := Nat.mod_le _ _
  -- The sharp Turán bound from Mathlib.
  have key : G.edgeFinset.card ≤ (n ^ 2 - s ^ 2) * (r - 1) / (2 * r) + s.choose 2 :=
    h.card_edgeFinset_le
  have h1 : 2 * r * G.edgeFinset.card
      ≤ 2 * r * ((n ^ 2 - s ^ 2) * (r - 1) / (2 * r) + s.choose 2) :=
    Nat.mul_le_mul_left _ key
  refine h1.trans ?_
  rw [Nat.mul_add]
  have h2 : 2 * r * ((n ^ 2 - s ^ 2) * (r - 1) / (2 * r)) ≤ (n ^ 2 - s ^ 2) * (r - 1) :=
    Nat.mul_div_le _ _
  have h3 : 2 * r * s.choose 2 = r * (s * (s - 1)) := by
    rw [Nat.choose_two_right, mul_comm 2 r, mul_assoc,
      Nat.mul_div_cancel' (Nat.even_mul_pred_self s).two_dvd]
  have hs2 : s ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hsn 2
  have h4 : r * (s * (s - 1)) ≤ (r - 1) * s ^ 2 := harith s r hsr
  have h5 : (r - 1) * n ^ 2 = (n ^ 2 - s ^ 2) * (r - 1) + (r - 1) * s ^ 2 := by
    rw [mul_comm (n ^ 2 - s ^ 2) (r - 1), ← Nat.mul_add]
    congr 1
    omega
  rw [h3, h5]
  omega
end Brockian.Turan

