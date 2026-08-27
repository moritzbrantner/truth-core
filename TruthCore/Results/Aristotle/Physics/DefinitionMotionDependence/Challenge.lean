import TruthCore.Greek.Aristotle.Physics.BookII.Chapter2

namespace TruthCore.Results.Aristotle.Physics.DefinitionMotionDependence

open TruthCore.Greek.Aristotle.Physics

/-- The definition comparison distinguishes mathematical from natural inquiry. -/
theorem definitionMotionDependenceDistinguishesInquiries
    (MathematicalDefinitionsRequireMotion
      NaturalDefinitionsRequireMotion : Prop)
    (hMathematical :
      MathematicalDefinitionsMotionIndependentReading
        MathematicalDefinitionsRequireMotion)
    (hNatural :
      NaturalDefinitionsMotionDependentReading
        NaturalDefinitionsRequireMotion) :
    DefinitionMotionDependenceDistinguishesInquiriesReading
      MathematicalDefinitionsRequireMotion
      NaturalDefinitionsRequireMotion := by
  sorry

end TruthCore.Results.Aristotle.Physics.DefinitionMotionDependence
