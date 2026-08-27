import TruthCore.Greek.Aristotle.Physics.BookI.Chapter9

namespace TruthCore.Results.Aristotle.Physics.MatterUngeneratedImperishable

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's two reductios in *Physics* I.9 exclude matter's generation and perishing. -/
theorem matterUngeneratedImperishable
    (MatterComesToBe MatterExistsBeforeComingToBe
      MatterPerishes MatterAlreadyPerishedBeforePerishing : Prop)
    (hReductios :
      MatterGenerationPerishingReductiosReading
        MatterComesToBe MatterExistsBeforeComingToBe
        MatterPerishes MatterAlreadyPerishedBeforePerishing)
    (hImpossible :
      MatterReductioOutcomesImpossibleReading
        MatterExistsBeforeComingToBe MatterAlreadyPerishedBeforePerishing) :
    MatterUngeneratedImperishableQuaPotentialityReading
      MatterComesToBe MatterPerishes := by
  constructor
  · intro hComesToBe
    exact hImpossible.1 (hReductios.1 hComesToBe)
  · intro hPerishes
    exact hImpossible.2 (hReductios.2 hPerishes)

end TruthCore.Results.Aristotle.Physics.MatterUngeneratedImperishable
