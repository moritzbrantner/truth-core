import TruthCore.Greek.Aristotle.Physics.BookV.Chapter3

namespace TruthCore.Results.Aristotle.Physics.ContinuityImpliesSuccession

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's implication hierarchy in *Physics* V.3, 227a17-23. -/
theorem continuityImpliesSuccession
    (Continuity Contact Succession EveryContactIsContinuous
      EverySuccessionInvolvesContact : Prop)
    (hContinuityContact :
      ContinuityImpliesContactNotConverselyReading
        Continuity Contact EveryContactIsContinuous)
    (hContactSuccession :
      ContactImpliesSuccessionNotConverselyReading
        Contact Succession EverySuccessionInvolvesContact) :
    ContinuityImpliesSuccessionReading Continuity Succession := by
  sorry

end TruthCore.Results.Aristotle.Physics.ContinuityImpliesSuccession
