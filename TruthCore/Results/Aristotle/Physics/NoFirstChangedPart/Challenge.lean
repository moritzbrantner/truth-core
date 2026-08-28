import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter5
namespace TruthCore.Results.Aristotle.Physics.NoFirstChangedPart
open TruthCore.Greek.Aristotle.Physics
theorem noFirstChangedPart (ProposedFirstChangedPart EarlierSmallerChangedPart : Prop)
    (hEarlier : ProposedFirstChangedPartHasEarlierSmallerPartReading
      ProposedFirstChangedPart EarlierSmallerChangedPart)
    (hExcludes : EarlierSmallerPartExcludesFirstChangedPartReading
      EarlierSmallerChangedPart ProposedFirstChangedPart) :
    NoFirstChangedPartReading ProposedFirstChangedPart := by
  sorry
end TruthCore.Results.Aristotle.Physics.NoFirstChangedPart
