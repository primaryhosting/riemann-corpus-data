/-!
# Sum Three Cubes 42
Category: Frontier — Prime Numbers
Target: Frontier.sum_three_cubes_42
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The 2019 solution of `x³ + y³ + z³ = 42` in the integers:
`42 = (-80538738812075974)³ + 80435758145817515³ + 12602123297335631³`. -/
theorem sum_three_cubes_42 :
    (42 : Int) =
      (-80538738812075974) ^ 3 + 80435758145817515 ^ 3 + 12602123297335631 ^ 3 := by
  decide

end Frontier

