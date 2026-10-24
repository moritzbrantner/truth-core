import TruthCore.Logic.QuantifierShift
namespace TruthCore.Results.Logic.QuantifierShiftInvalid
open TruthCore.Logic

/-- The naive temporal quantifier shift is invalid. Two beings and two times:
each being is at exactly one time, the other's. Each being is at some time not,
yet at every time something is. Constructive, no premises. -/
theorem quantifierShiftInvalid : EachSometimeNotDoesNotEntailSometimeNothing := by
  intro hShift
  -- the relay model: being `b` is only at time `b`
  have hEach : ∀ x : Bool, ∃ t : Bool, ¬ (x = t) := by
    intro x
    cases x
    · exact ⟨true, Bool.noConfusion⟩
    · exact ⟨false, Bool.noConfusion⟩
  obtain ⟨t, hNothing⟩ := hShift Bool Bool (fun x t => x = t) hEach
  -- but at time `t` the being `t` is
  exact hNothing t rfl

end TruthCore.Results.Logic.QuantifierShiftInvalid
