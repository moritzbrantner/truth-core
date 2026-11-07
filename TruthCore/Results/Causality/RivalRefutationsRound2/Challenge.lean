import TruthCore.Causality.RivalRefutationsRound2

namespace TruthCore.Results.Causality.RivalRefutationsRound2
open TruthCore.Causality.RivalRefutationsRound2
open TruthCore.Latin.Aquinas.SummaTheologiae (SecondEfficientCausesCauseOnlyAsCausedReading)
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Alternatives.ActPotencyRegress (MovedIsAbleToBeReading MovedNotYetInActReading)
open TruthCore.Alternatives.Inertia (UniformPerseveranceIsNotBeingMovedReading)

/-- Every per se mover link is a per se cause link, given the link analysis, the
mover/efficient-cause bridge and the Second Way's per se ordering premise. -/
theorem noMoverLinkWithoutCauseLink {B R : Type}
    (MovesIn EfficientlyCausesIn : B → B → R → Prop)
    (MovesAsMoved CausesAsCaused : B → B → Prop)
    (hLink : PerSeMoverLinkIsMovingByMovedMoverReading MovesIn MovesAsMoved)
    (hEfficient : MoverIsEfficientCauseReading MovesIn EfficientlyCausesIn)
    (hSecond : SecondEfficientCausesCauseOnlyAsCausedReading EfficientlyCausesIn CausesAsCaused) :
    NoMoverLinkWithoutCauseLink MovesAsMoved CausesAsCaused := by
  sorry

/-- Whatever is being moved in a respect is in potency in it, given Metaphysics
IX.3 (able to be), Physics III.2 (not yet) and Metaphysics IX.6 (potency is
unactualized capacity). -/
theorem noMovedNotPotentCountertuple {B R : Type}
    (MovedIn InAct InPotency CanBe : B → R → Prop)
    (hAble : MovedIsAbleToBeReading MovedIn CanBe)
    (hNotYet : MovedNotYetInActReading MovedIn InAct)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) :
    NoMovedNotPotentCountertuple MovedIn InPotency := by
  sorry

/-- Nothing is moved uniformly in a straight line with nothing moving it, given
the state reading of uniform motion and the perseverance bridge. -/
theorem noUniformMotionWithoutMover {B R : Type}
    (MovedIn Perseveres : B → R → Prop) (MovesIn : B → B → R → Prop)
    (UniformLocalMotion : R → Prop)
    (hState : UniformPerseveranceIsNotBeingMovedReading MovedIn UniformLocalMotion Perseveres)
    (hBridge : MoverlessUniformMotionIsPerseveranceReading MovedIn MovesIn UniformLocalMotion
      Perseveres) :
    NoUniformMotionWithoutMover MovedIn MovesIn UniformLocalMotion := by
  sorry

theorem controls : TruthCore.Causality.RivalRefutationsRound2.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.RivalRefutationsRound2
