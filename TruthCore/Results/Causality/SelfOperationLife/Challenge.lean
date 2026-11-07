import TruthCore.Causality.SelfOperationLife

namespace TruthCore.Results.Causality.SelfOperationLife
open TruthCore.Causality.SelfOperationLife
open TruthCore.Latin.Aquinas.SummaTheologiae (PureActLivesReading MovedOnlyAsInPotencyReading)

/-- A pure act operates from itself; being in potency in no respect, it is moved
in no respect; so it lives. Conditional on three OPEN premises. -/
theorem pureActLives {B R T : Type} (InPotency MovedIn : B → R → Prop)
    (Operates : B → Prop) (LivesAt : B → T → Prop)
    (hOperates : PureActOperates InPotency Operates)
    (hLife : SelfOperatingUnmovedLives Operates MovedIn LivesAt)
    (hMoved : MovedOnlyAsInPotencyReading MovedIn InPotency) :
    PureActLivesReading InPotency LivesAt := by
  sorry

theorem controls : TruthCore.Causality.SelfOperationLife.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.SelfOperationLife
