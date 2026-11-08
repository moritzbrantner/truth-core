import TruthCore.Causality.WholePowerPerfection

namespace TruthCore.Results.Causality.WholePowerPerfection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActThisness
open TruthCore.Causality.PureIndiscernibility (PurelyDeterminedIndiscerniblesIdentical)
open TruthCore.Causality.PureActRoot (ActualRootHasEveryPureDetermination)
open TruthCore.Causality.WholePowerPerfection
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.Logic (ExcludedMiddle)

/-- Unrestricted perfection for first movers: simplicity and firstness remove
every represented limiting principle; the open bridge makes an unlimited first
mover its own being; SCG I.28 gives it every perfection of being; q.4 a.2 makes
every pure perfection such a perfection. -/
theorem firstMoverPerfectionFromWholePower {B R P D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (Body ComposedOfMatterAndForm Composite : B → Prop) (essenceOf esseOf : B → P)
    (OwnBeing : B → Prop) (Has : B → D → Prop) (Pure OfBeing : D → Prop)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hFirst : FirstUnmovedMoverIsFirstBeing Moved Moves PriorSimply)
    (hOwn : UnlimitedIsOwnBeing Composite PriorSimply essenceOf esseOf OwnBeing)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing) :
    FirstMoverHasEveryPureDetermination Moved Moves Has Pure := by
  sorry

/-- Unrestricted perfection at the actual roots, from the eight inputs that make
every actual root unlimited and the same three premises. -/
theorem rootPerfectionFromWholePower {W B P R D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (OwnBeing : B → Prop) (Has : B → D → Prop) (Pure OfBeing : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hOwn : UnlimitedIsOwnBeing Composite PriorSimply p.essenceOf p.esseOf OwnBeing)
    (hWhole : OwnBeingLacksNoPerfectionOfBeing OwnBeing Has OfBeing)
    (hPertain : PurePerfectionsPertainToBeing Pure OfBeing) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  sorry

/-- Unrestricted perfection for first movers through infinity: simplicity and
excluded middle give esse equal to essence, the existing q.7 reading
(`STMT-SUBSISTENT-BEING-IS-INFINITE`, a premise of the designated root route) makes
the first mover infinite, and the bridge gives it every pure perfection. -/
theorem firstMoverPerfectionFromInfinity {B R P D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body ComposedOfMatterAndForm Composite : B → Prop) (essenceOf esseOf : B → P)
    (Infinite : B → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hInfinite : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hBridge : InfiniteHasEveryPurePerfection Infinite Has Pure) :
    FirstMoverHasEveryPureDetermination Moved Moves Has Pure := by
  sorry

/-- Unrestricted perfection at the actual roots through infinity: the existing
per-root essence/esse identity, the q.7 reading and the bridge. -/
theorem rootPerfectionFromInfinity {W B P R D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (Infinite : B → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hInfinite : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hBridge : InfiniteHasEveryPurePerfection Infinite Has Pure) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  sorry

/-- SCG I.42 with unrestricted perfection and strict pure actuality: at most one
first mover. Conditional on three OPEN premises. -/
theorem uniqueFromPerfectBeings {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hPerfect : PerfectBeingsNotSeveral Has Pure) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  sorry

/-- The narrower bridge entails SCG I.42. -/
theorem perfectBeingsOfPureIndiscernibility {B D : Type} (Has : B → D → Prop)
    (Pure : D → Prop) (hBridge : PurelyDeterminedIndiscerniblesIdentical Has Pure) :
    PerfectBeingsNotSeveral Has Pure := by
  sorry

theorem controls : TruthCore.Causality.WholePowerPerfection.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.WholePowerPerfection
