import TruthCore.Greek.Aristotle.MetaphysicsIV7
namespace TruthCore.Results.Aristotle.Metaphysics.ChangeDecidesContradictoryPair
open TruthCore.Greek.Aristotle.Metaphysics
/-- *Metaphysics* IV.7, 1011b29-1012a1: if every change in respect of a
contradictory pair goes from one side to the other, and every state is the start
of such a change, then every state either has `F` or lacks it. Constructive:
the decision comes from the change premise, which is itself a disjunction about
every change. So the argument refutes a state between the contradictories; it
does not refute withholding `F a ∨ ¬F a`, because the withholder withholds the
change premise for any pair not already decided. -/
theorem changeDecidesContradictoryPair {State : Type}
    (F : State → Prop) (Changes : State → State → Prop)
    (hOnly : ChangeOnlyBetweenContradictoriesReading F Changes)
    (hAlways : WhatIsAlwaysChangesReading Changes) :
    ContradictoryPairDecidedOnStates F := by
  intro a
  -- νῦν δʼ ἀεὶ φαίνεται: the state a is the start of some change.
  obtain ⟨b, hChange⟩ := hAlways a
  -- That change goes from one side of the pair to the other.
  cases hOnly a b hChange with
  | inl hFromNot =>
    -- From not-F to F: a lacks F.
    exact Or.inr hFromNot.1
  | inr hFrom =>
    -- From F to not-F: a has F.
    exact Or.inl hFrom.1
end TruthCore.Results.Aristotle.Metaphysics.ChangeDecidesContradictoryPair
