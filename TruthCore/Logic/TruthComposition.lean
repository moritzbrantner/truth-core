import TruthCore.Logic.TruthPilot

namespace TruthCore.Logic.TruthComposition
open TruthCore.Logic.TruthPilot

/-- A bounded composition fixture: retain both the existential witness and the
consequence denying universal failure. This conjunction introduces no external
truth predicate, source reading, or empirical claim. The component meanings are
exactly those of the objective-truth pilot; no second interpretation is added. -/
def WitnessAndConsequence : Prop :=
  SomePropositionHolds ∧ NotEveryPropositionFails

end TruthCore.Logic.TruthComposition
