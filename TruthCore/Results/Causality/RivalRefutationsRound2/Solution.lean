module

public import TruthCore.Causality.RivalRefutationsRound2

@[expose] public section

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
    NoMoverLinkWithoutCauseLink MovesAsMoved CausesAsCaused :=
  fun ⟨y, x, hL, hNot⟩ =>
    match hLink y x hL with
    | ⟨hne, ⟨r, hm⟩, ⟨z, r', hz⟩⟩ =>
      hNot (hSecond y x r hne (hEfficient y x r hm) ⟨z, r', hEfficient z y r' hz⟩)

/-- Whatever is being moved in a respect is in potency in it, given Metaphysics
IX.3 (able to be), Physics III.2 (not yet) and Metaphysics IX.6 (potency is
unactualized capacity). -/
theorem noMovedNotPotentCountertuple {B R : Type}
    (MovedIn InAct InPotency CanBe : B → R → Prop)
    (hAble : MovedIsAbleToBeReading MovedIn CanBe)
    (hNotYet : MovedNotYetInActReading MovedIn InAct)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) :
    NoMovedNotPotentCountertuple MovedIn InPotency :=
  fun ⟨x, r, hM, hNot⟩ => hNot ((hAnalysis x r).mpr ⟨hAble x r hM, hNotYet x r hM⟩)

/-- Nothing is moved uniformly in a straight line with nothing moving it, given
the state reading of uniform motion and the perseverance bridge. -/
theorem noUniformMotionWithoutMover {B R : Type}
    (MovedIn Perseveres : B → R → Prop) (MovesIn : B → B → R → Prop)
    (UniformLocalMotion : R → Prop)
    (hState : UniformPerseveranceIsNotBeingMovedReading MovedIn UniformLocalMotion Perseveres)
    (hBridge : MoverlessUniformMotionIsPerseveranceReading MovedIn MovesIn UniformLocalMotion
      Perseveres) :
    NoUniformMotionWithoutMover MovedIn MovesIn UniformLocalMotion :=
  fun ⟨x, r, hU, hM, hNo⟩ => hState x r hU (hBridge x r hU hM hNo) hM

open TruthCore.Causality.RivalRefutationsRound2.Control in
/-- The two-being link model satisfies the per se link analysis. -/
theorem linkDiff : PerSeMoverLinkIsMovingByMovedMoverReading diff3 diff :=
  fun y x h =>
    ⟨fun e => (match y, x, e, h with
      | true, _, rfl, h => Bool.noConfusion h
      | false, _, rfl, h => Bool.noConfusion h), ⟨(), h⟩, ⟨!y, (), rfl⟩⟩

open TruthCore.Causality.RivalRefutationsRound2.Control in
theorem controls : TruthCore.Causality.RivalRefutationsRound2.Control.Certificate :=
  ⟨⟨⟨fun h => (h () () trivial).1 rfl, fun _ _ _ h => h, fun _ _ _ _ h _ => h,
        ⟨(), (), trivial, fun h => h⟩⟩,
      ⟨linkDiff, fun h => h true false () rfl, fun _ _ _ _ h _ => h,
        ⟨true, false, rfl, fun h => h⟩⟩,
      ⟨linkDiff, fun _ _ _ h => h,
        fun h => h true false () (fun e => Bool.noConfusion e) rfl ⟨false, (), rfl⟩,
        ⟨true, false, rfl, fun h => h⟩⟩,
      ⟨linkDiff, fun _ _ _ h => h, fun _ _ _ _ h _ => h, rfl⟩⟩,
    ⟨⟨fun h => h () () trivial, fun _ _ _ h => h,
        fun _ _ => ⟨fun h => h.elim, fun h => h.1.elim⟩, ⟨(), (), trivial, fun h => h⟩⟩,
      ⟨fun _ _ _ => trivial, fun h => h () () trivial trivial,
        fun _ _ => ⟨fun h => h.elim, fun h => h.2 trivial⟩, ⟨(), (), trivial, fun h => h⟩⟩,
      ⟨fun _ _ _ => trivial, fun _ _ _ h => h, fun h => (h () ()).mpr ⟨trivial, fun h => h⟩,
        ⟨(), (), trivial, fun h => h⟩⟩,
      ⟨fun _ _ _ => trivial, fun _ _ _ h => h,
        fun _ _ => ⟨fun _ => ⟨trivial, fun h => h⟩, fun _ => trivial⟩, trivial⟩⟩,
    ⟨⟨fun h => h () () trivial trivial trivial, fun _ _ _ _ _ => trivial,
        ⟨(), (), trivial, trivial, fun _ h => h⟩⟩,
      ⟨fun _ _ _ h => h.elim, fun h => h () () trivial trivial (fun _ h => h),
        ⟨(), (), trivial, trivial, fun _ h => h⟩⟩,
      ⟨fun _ _ _ h => h.elim, fun _ _ _ _ h => (h () trivial).elim, trivial, trivial⟩⟩⟩

end TruthCore.Results.Causality.RivalRefutationsRound2
