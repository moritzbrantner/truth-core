import TruthCore.Logic.QuantifierShift
namespace TruthCore.Results.Logic.QuantifierShiftInvalid
open TruthCore.Logic

/-- The naive temporal quantifier shift is invalid. Two beings and two times:
each being is at exactly one time, the other's. Each being is at some time not,
yet at every time something is. Constructive, no premises. -/
theorem quantifierShiftInvalid : EachSometimeNotDoesNotEntailSometimeNothing := by
  sorry

end TruthCore.Results.Logic.QuantifierShiftInvalid
