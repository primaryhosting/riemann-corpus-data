/-
  Brockian/PentagonTraceBridge.lean

  Identifies the fixed-point formula used by `permCharacter` with the trace of
  the concrete permutation matrix implementing `d5Pull` on the five vertices.
-/
import Brockian.D5CharacterTable
import Brockian.PentagonCharacterMultiplicity

open DihedralGroup

namespace Brockian.PentagonTraceBridge

open Brockian.D5CharacterTable
open Brockian.PentagonCharacterMultiplicity

/-- The concrete permutation-matrix trace is the packaged vertex character. -/
theorem d5Character_eq_permCharacter (g : DihedralGroup 5) :
    d5Character g = permCharacter g := by
  cases g with
  | r k => exact d5Character_rotation k
  | sr k => exact d5Character_reflection k

/-- The packaged character is literally the trace of the concrete matrix that
acts as `d5Pull` in the vertex delta basis. -/
theorem permCharacter_eq_trace_d5PermutationMatrix (g : DihedralGroup 5) :
    permCharacter g = Matrix.trace (d5PermutationMatrix g) := by
  rw [← d5Character_eq_permCharacter]
  rfl

/-- The golden multiplicity computation can be stated directly using the
trace character of the concrete permutation representation. -/
theorem concrete_permInner_golden :
    Brockian.D5CharacterComplete.charInner d5Character
      Brockian.D5CharacterComplete.chiGolden = 1 := by
  have hchar : d5Character = permCharacter :=
    funext d5Character_eq_permCharacter
  rw [hchar]
  exact permInner_golden

end Brockian.PentagonTraceBridge
