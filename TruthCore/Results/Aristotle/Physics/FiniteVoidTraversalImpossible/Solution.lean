import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter8

namespace TruthCore.Results.Aristotle.Physics.FiniteVoidTraversalImpossible

open TruthCore.Greek.Aristotle.Physics

/-- A finite traversal of void would equal a traversal through some full medium, contrary
to Aristotle's stated impossibility. -/
theorem finiteVoidTraversalImpossible
    (FiniteVoidTraversal EqualFullAndVoidTraversalTime : Prop)
    (hConsequence :
      FiniteVoidTraversalEntailsEqualFullVoidTraversalTimeReading
        FiniteVoidTraversal EqualFullAndVoidTraversalTime)
    (hImpossible :
      EqualFullVoidTraversalTimeImpossibleReading EqualFullAndVoidTraversalTime) :
    FiniteVoidTraversalImpossibleReading FiniteVoidTraversal := by
  intro hFinite
  exact hImpossible (hConsequence hFinite)

end TruthCore.Results.Aristotle.Physics.FiniteVoidTraversalImpossible
