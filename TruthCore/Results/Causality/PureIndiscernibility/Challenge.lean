import TruthCore.Causality.PureIndiscernibility
namespace TruthCore.Results.Causality.PureIndiscernibility
open TruthCore.Case.Catholicism
open TruthCore.Causality.PureActThisness
open TruthCore.Causality.PureIndiscernibility

/-- Unrestricted perfection and strict pure actuality make any two first movers
really indiscernible and purely determined; the narrower bridge makes them one.
Conditional on three OPEN premises. No first mover is produced. -/
theorem uniqueFromPureIndiscernibility {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hBridge : PurelyDeterminedIndiscerniblesIdentical Has Pure) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  sorry

/-- Identity of real indiscernibles entails the narrower bridge. -/
theorem pureIndiscernibilityOfReal {B D : Type} (Has : B → D → Prop) (Pure : D → Prop)
    (hReal : RealDeterminationsIndividuate Has) :
    PurelyDeterminedIndiscerniblesIdentical Has Pure := by
  sorry

theorem controls : TruthCore.Causality.PureIndiscernibility.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.PureIndiscernibility
