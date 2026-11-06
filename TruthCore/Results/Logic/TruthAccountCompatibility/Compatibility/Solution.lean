module

public import TruthCore.Logic.TruthAccountCompatibility
public import TruthCore.Results.Comparison.ExcludedMiddle.IntuitionistTheoryConsistent.Solution

@[expose] public section
namespace TruthCore.Results.Logic.TruthAccountCompatibility.Compatibility
open TruthCore.Logic.TruthAccountCompatibility
open TruthCore.Greek.Aristotle.Metaphysics
theorem jointEncodedAccounts : JointEncodedAccounts := by
  have hComposition : ThoughtTrueOrFalseByCompositionReading object Affirms Denies
      TrueThought FalseThought := by
    intro ⟨affirmative, p⟩
    cases affirmative
    · constructor
      · intro h
        exact False.elim (Bool.noConfusion h)
      · intro h
        exact ⟨Iff.rfl, Iff.rfl⟩
    · constructor
      · intro h
        exact ⟨Iff.rfl, Iff.rfl⟩
      · intro h
        exact False.elim (Bool.noConfusion h)
  exact ⟨TruthCore.Results.Comparison.ExcludedMiddle.IntuitionistTheoryConsistent.intuitionistTheoryConsistent,
    hComposition, True.intro, (fun h => h), (fun h => h), True.intro⟩
end TruthCore.Results.Logic.TruthAccountCompatibility.Compatibility
