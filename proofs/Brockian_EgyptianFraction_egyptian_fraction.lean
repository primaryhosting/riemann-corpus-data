import Mathlib
namespace Brockian.EgyptianFraction
/-- Egyptian fraction existence: every rational a/b with 0 < a < b is a finite sum of
    distinct unit fractions (the Finset of denominators makes them automatically distinct). -/
theorem egyptian_fraction (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    ∃ S : Finset ℕ, (∀ d ∈ S, 0 < d) ∧ ∑ d ∈ S, (1 / (d : ℚ)) = (a : ℚ) / b := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    match a with
    | 0 => omega
    | 1 =>
      refine ⟨{b}, ?_, ?_⟩
      · simp; omega
      · simp
    | a + 2 =>
      -- Greedy algorithm: c = ⌈b / (a + 2)⌉
      let c := (b + (a + 1)) / (a + 2)
      have hc_pos : 0 < c := by
        simp [c]
        omega
      -- Check if a + 2 divides b exactly
      by_cases hdiv : c * (a + 2) = b
      · -- If exact, a + 2 / b = 1 / c
        refine ⟨{c}, ?_, ?_⟩
        · simp; exact hc_pos
        · simp; rw [inv_eq_one_div, div_eq_div_iff] <;> norm_cast <;> linarith
      · -- Otherwise, c*(a+2) > b since c = ⌈b/(a+2)⌉
        -- c = (b + a + 1) / (a + 2), so c * (a+2) = (b + a + 1) - remainder
        have hdiv_mod : c * (a + 2) = b + a + 1 - (b + a + 1) % (a + 2) := by
          simp only [c]
          rw [← Nat.div_add_mod (b + a + 1) (a + 2)]
          simp [add_comm, add_assoc, mul_comm]
        have hrem_lt : (b + a + 1) % (a + 2) < a + 2 := Nat.mod_lt _ (by omega)
        have hc_ge : c * (a + 2) ≥ b := by
          rw [hdiv_mod]
          have : (b + a + 1) % (a + 2) ≤ a + 1 := Nat.le_of_lt_succ hrem_lt
          omega
        have hc_gt : c * (a + 2) > b := lt_of_le_of_ne hc_ge (Ne.symm hdiv)
        -- Define a' and b'
        let a' := c * (a + 2) - b
        let b' := b * c
        have ha'_pos : 0 < a' := Nat.sub_pos_of_lt hc_gt
        have ha'_lt : a' < a + 2 := by
          simp only [a', c]
          rw [hdiv_mod]
          have : (b + a + 1) % (a + 2) ≥ 0 := Nat.zero_le _
          omega
        have hab' : a' < b' := by
          simp only [a', b']
          have : c > 0 := hc_pos
          nlinarith
        -- Apply IH
        obtain ⟨S', hS'_pos, hS'_sum⟩ := ih a' ha'_lt b' ha'_pos hab'
        -- First show c ∉ S' (otherwise the sum would be wrong)
        have hc_notin : c ∉ S' := by
          intro hc_in
          have hsum_eq : (1 : ℚ) / c ≤ ↑a' / ↑b' := by
            rw [← hS'_sum]
            have := Finset.single_le_sum (f := fun (x : ℕ) => (1 : ℚ) / x)
              (fun x hx => div_nonneg zero_le_one (Nat.cast_nonneg x)) hc_in
            exact this
          -- Cross multiply: 1/c ≤ a'/b' implies b*c ≤ c*a' = c*(c*(a+2) - b)
          -- So b ≤ c*(a+2) - b, i.e., 2*b ≤ c*(a+2)
          -- But c*(a+2) = b + a + 1 - remainder ≤ b + a + 1 < 2*b (since b > a+2)
          have hca : (c : ℚ) * (a + 2) ≤ b + a + 1 := by
            simp only [c]
            have : (b + (a + 1)) / (a + 2) * (a + 2) ≤ b + (a + 1) := Nat.div_mul_le_self _ _
            norm_cast
          -- From hsum_eq: b ≤ c*a' = c*(c*(a+2) - b)
          have hb_pos : 0 < b := by omega
          have hab'pos : (0 : ℚ) < b' := by positivity
          have hc_ne : (0 : ℚ) < c := by positivity
          field_simp at hsum_eq
          -- hsum_eq : b' ≤ a' * c
          simp only [b'] at hsum_eq
          -- hsum_eq : b * c ≤ a' * c
          have hbc : (b : ℚ) * c ≤ c * a' := by simp only [Nat.cast_mul] at hsum_eq; exact hsum_eq
          have hac : (b : ℚ) ≤ ↑a' := by nlinarith
          -- But a' < a + 2 < b, contradiction
          have ha'_lt_b : a' < b := by omega
          have hb_gt_a' : (b : ℚ) > a' := by norm_cast
          linarith
        use insert c S'
        constructor
        · intro d hd
          cases Finset.mem_insert.mp hd with
          | inl h => simp [h]; exact hc_pos
          | inr h => exact hS'_pos d h
        · rw [Finset.sum_insert hc_notin, hS'_sum]
          -- Need to show 1/c + a'/b' = (a+2)/b
          -- where a' = c*(a+2) - b and b' = b*c
          have hb_pos : 0 < b := by omega
          have hc_pos' : 0 < c := hc_pos
          simp only [b', a']
          rw [div_add_div, div_eq_div_iff]
          · norm_cast
            -- Goal: (b * c + c * (c * (a + 2) - b)) * b = (a + 2) * (c * (b * c))
            have h1 : c * (a + 2) ≥ b := hc_ge
            have h2 : c * (c * (a + 2) - b) = c * (a + 2) * c - c * b := by
              rw [mul_comm c (c * (a + 2) - b), Nat.sub_mul, mul_comm b c]
            rw [h2]
            simp only [one_mul]
            have h3 : c * (a + 2) * c ≥ c * b := by nlinarith
            have h4 : c * b + (c * (a + 2) * c - c * b) = c * (a + 2) * c := Nat.add_sub_cancel' h3
            rw [mul_comm b c, h4]
            ring
          · positivity
          · positivity
          · positivity
          · positivity
end Brockian.EgyptianFraction

