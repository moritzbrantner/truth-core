import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter1

namespace TruthCore.Results.Aristotle.Physics.ContinuumNotIndivisibles

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's reductio in *Physics* VI.1, 231a24-231b6. -/
theorem continuumNotComposedOfIndivisibles
    (ContinuumComposedOfIndivisibles
      IndivisiblesComposeContinuumThroughContinuityOrContact : Prop)
    (hRequires :
      ContinuumFromIndivisiblesRequiresContinuityOrContactReading
        ContinuumComposedOfIndivisibles
        IndivisiblesComposeContinuumThroughContinuityOrContact)
    (hImpossible :
      IndivisiblesCannotComposeContinuumByContinuityOrContactReading
        IndivisiblesComposeContinuumThroughContinuityOrContact) :
    ContinuumNotComposedOfIndivisiblesReading ContinuumComposedOfIndivisibles := by
  intro hComposition
  exact hImpossible (hRequires hComposition)

end TruthCore.Results.Aristotle.Physics.ContinuumNotIndivisibles
