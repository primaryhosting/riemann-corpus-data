/-
# Pair 10007 10009
Category: Frontier — Prime Numbers
Target: Twin.pair_10007_10009
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Twin

/-- 10007 and 10009 form a twin prime pair. -/
theorem pair_10007_10009 :
    Nat.Prime 10007 ∧ Nat.Prime 10009 ∧ 10009 = 10007 + 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end Twin

