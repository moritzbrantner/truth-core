module

public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Results.Causality.RootPurity.Solution
public import TruthCore.Results.Causality.PureActThisness.Solution

@[expose] public section

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
  intro f hf d hd
  have hs := hSimple f hf
  have hUnlimited : ¬ TruthCore.Causality.RootMultiplication.HasLimitingPrinciple
      Composite PriorSimply essenceOf esseOf f := by
    intro hLimited
    rcases hLimited with hComposite | hDistinctEsse | ⟨y, hDistinct, hPriorY⟩
    · exact hs.2.2.2 hComposite
    · exact hs.2.2.1 hDistinctEsse
    · exact hDistinct (hFirst f hf y hPriorY)
  exact hWhole f (hOwn f hUnlimited) d (hPertain d hd)

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
  intro r hr d hd
  exact hWhole r (hOwn r (TruthCore.Results.Causality.RootPurity.rootsWithoutLimitingPrinciple
    m w p PriorSimply ComponentOf Composite hEM hExisting hEsse hExhaustive hNoSelfCause
    hPrior hPosterior hOther r hr)) d (hPertain d hd)

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
  intro f hf d hd
  have hEq : esseOf f = essenceOf f := by
    rcases hEM (esseOf f = essenceOf f) with h | h
    · exact h
    · exact ((hSimple f hf).2.2.1 h).elim
  exact hBridge f (hInfinite f hEq) d hd

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
  intro r hr d hd
  exact hBridge r (hInfinite r (TruthCore.Causality.RootEssenceIdentity.identityOfActualRoot
    m w p r hr hEM hExisting hEsse hExhaustive hNoSelfCause)) d hd

/-- SCG I.42 with unrestricted perfection and strict pure actuality: at most one
first mover. Conditional on three OPEN premises. -/
theorem uniqueFromPerfectBeings {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hPerfect : PerfectBeingsNotSeveral Has Pure) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  intro f g hf hg
  exact hPerfect f g (hEvery f hf) (hPure f hf) (hEvery g hg) (hPure g hg)

/-- The narrower bridge entails SCG I.42. -/
theorem perfectBeingsOfPureIndiscernibility {B D : Type} (Has : B → D → Prop)
    (Pure : D → Prop) (hBridge : PurelyDeterminedIndiscerniblesIdentical Has Pure) :
    PerfectBeingsNotSeveral Has Pure := by
  intro x y hx hxPure hy hyPure
  exact hBridge x y hxPure (fun d => ⟨fun h => hy d (hxPure d h), fun h => hx d (hyPure d h)⟩)

section Controls
open TruthCore.Causality.WholePowerPerfection.Control
open TruthCore.Causality.RootPurity.Control (fmMoved fmMoves)
open TruthCore.Results.Causality.RootPurity (unlimited)
open TruthCore.Results.Causality.PartFreePlurality (leftFirst rightFirst perfect notUnique)

theorem fmFirst : IsFirstUnmovedMover fmMoved fmMoves true := ⟨⟨true, (), rfl⟩, fun _ h => h⟩

theorem fmSimple : FirstUnmovedMoverIsSimpleReading fmMoved fmMoves
    TruthCore.Causality.RootPurity.Control.none1 TruthCore.Causality.RootPurity.Control.none1
    TruthCore.Causality.RootPurity.Control.none1
    TruthCore.Causality.RootPurity.Control.flat.essenceOf
    TruthCore.Causality.RootPurity.Control.flat.esseOf :=
  fun _ _ => ⟨fun h => h, fun h => h, fun h => h rfl, fun h => h⟩

theorem fmFirstBeing : FirstUnmovedMoverIsFirstBeing fmMoved fmMoves
    TruthCore.Causality.RootPurity.Control.none2 := fun _ _ _ h => h.elim

theorem noPerfection : ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas
    (fun _ => True) := fun h => h true fmFirst () trivial

theorem controls : TruthCore.Causality.WholePowerPerfection.Control.Certificate :=
  ⟨⟨fun _ _ hx _ _ _ => (hx () trivial).elim,
      fun h => Bool.noConfusion (h true false (fun _ h => h.elim) (fun _ => Iff.rfl))⟩,
    ⟨fun x hx r _ => perfect x hx r, fun _ _ _ _ => trivial,
      fun h => TruthCore.Causality.PartFreePlurality.Being.noConfusion
        (h .left .right (fun r _ => perfect .left leftFirst r) (fun _ _ => trivial)
          (fun r _ => perfect .right rightFirst r) (fun _ _ => trivial)),
      notUnique⟩,
    ⟨fmSimple, fmFirstBeing, fun h => h true (unlimited true), fun _ h => h.elim,
      fun _ _ => trivial, noPerfection⟩,
    ⟨fun _ _ => trivial, fun h => h true trivial () trivial, fun _ _ => trivial, noPerfection⟩,
    ⟨fun _ _ => trivial, fun _ _ _ h => h.elim, fun h => h () trivial, noPerfection⟩,
    ⟨fun _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ => trivial, fun _ _ _ _ => trivial,
      fmFirst⟩,
    ⟨fun _ _ => trivial, fun h => h true trivial () trivial, noPerfection,
      fun _ _ _ _ => trivial⟩⟩

end Controls

end TruthCore.Results.Causality.WholePowerPerfection
