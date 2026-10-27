/-! Constructive logical floor. These propositions concern Lean's Prop, not
external existence, thought episodes, or metaphysical truth. -/
namespace TruthCore.Logic.CartesianFloor

/-- No proposition is both proved and refuted. -/
def NonContradiction : Prop := ∀ p : Prop, ¬ (p ∧ ¬ p)

/-- There is a proposition which does not hold (False). -/
def SomePropositionFails : Prop := ∃ p : Prop, ¬ p

/-- Not all propositions hold. -/
def NotEveryPropositionHolds : Prop := ¬ (∀ p : Prop, p)

end TruthCore.Logic.CartesianFloor
