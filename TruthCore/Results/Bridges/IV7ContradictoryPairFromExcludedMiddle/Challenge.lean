import TruthCore.Greek.Aristotle.MetaphysicsIV7
namespace TruthCore.Results.Bridges.IV7ContradictoryPairFromExcludedMiddle
open TruthCore.Greek.Aristotle.Metaphysics
/-- Bridge (#401), an instance of excluded middle: the conclusion of the change
argument, *Metaphysics* IV.7, 1011b29-1012a1
(`STMT-CONTRADICTORY-PAIR-DECIDED-ON-STATES`: every state has `F` or lacks it),
is an instance of excluded middle (`STMT-EXCLUDED-MIDDLE`) per state. The proof
only instantiates the premise. It connects the change argument's conclusion to
the self-evident principle; it says nothing about the change argument's own
premises, which the withholder also withholds. -/
theorem contradictoryPairDecidedOfExcludedMiddle {State : Type} (F : State → Prop)
    (hExcludedMiddle : TruthCore.Logic.ExcludedMiddle) :
    ContradictoryPairDecidedOnStates F := by
  sorry
end TruthCore.Results.Bridges.IV7ContradictoryPairFromExcludedMiddle
