module

public import TruthCore.Causality.RootPurity
public import TruthCore.Results.Causality.PureActRoot.Solution

@[expose] public section

namespace TruthCore.Results.Causality.RootPurity
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.RootPurity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.Logic (ExcludedMiddle)

/-- Every actual root lacks all three represented limiting principles. The
witnessed-root argument of ROOT-WITHOUT-LIMITING-PRINCIPLE, run for each actual
root; no population, whole-roster, dependence or necessity premise is used. -/
theorem rootsWithoutLimitingPrinciple {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf) :
    ActualRootsWithoutLimitingPrinciple m w Composite PriorSimply p.essenceOf p.esseOf := by
  intro n hr hLimited
  have hIdentity := TruthCore.Causality.RootEssenceIdentity.identityOfActualRoot
    m w p n hr hEM hExisting hEsse hExhaustive hNoSelfCause
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  rcases hLimited with hComposite | hDistinctEsse | ⟨y, hDistinct, hPriorY⟩
  · obtain ⟨part, hComponent, hDistinct⟩ := hOther n hComposite
    exact hDistinct (hFirst part (hPosterior part n hComponent))
  · exact hDistinctEsse hIdentity
  · exact hDistinct (hFirst y hPriorY)

/-- Strict pure actuality at the actual roots from the same seven inputs, excluded
middle and the open bridge that unlimited beings have only pure determinations. -/
theorem rootPurityFromNoLimitation {W B P R D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hBridge : UnlimitedDeterminationsArePure Composite PriorSimply p.essenceOf p.esseOf Has Pure) :
    ActualRootDeterminationsArePure m w Has Pure :=
  fun r hr => hBridge r (rootsWithoutLimitingPrinciple m w p PriorSimply ComponentOf Composite
    hEM hExisting hEsse hExhaustive hNoSelfCause hPrior hPosterior hOther r hr)

theorem firstMoverPurityFromNoLimitation {B R P D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (Body ComposedOfMatterAndForm Composite : B → Prop) (essenceOf esseOf : B → P)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hFirst : TruthCore.Case.Catholicism.FirstUnmovedMoverIsFirstBeing Moved Moves PriorSimply)
    (hBridge : UnlimitedDeterminationsArePure Composite PriorSimply essenceOf esseOf Has Pure) :
    TruthCore.Causality.PureActThisness.FirstMoverDeterminationsArePure Moved Moves Has Pure := by
  intro f hf
  apply hBridge f
  have hs := hSimple f hf
  intro hLimited
  rcases hLimited with hComposite | hDistinctEsse | ⟨y, hDistinct, hPriorY⟩
  · exact hs.2.2.2 hComposite
  · exact hs.2.2.1 hDistinctEsse
  · exact hDistinct (hFirst f hf y hPriorY)

section Controls
open TruthCore.Causality.RootPurity.Control
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Results.Causality.PureActRoot (twoRootsRoot oneRootTrue)

theorem inputs (m : Profile Unit Bool) : Inputs m :=
  ⟨fun _ _ => trivial, fun _ _ _ _ h => h.elim, fun _ h => (h.2 rfl).elim,
    fun _ h => (h.2 rfl).elim, fun _ _ _ h => h.elim, fun _ _ h => h, fun _ h => h.elim⟩

theorem unlimited (x : Bool) : ¬ TruthCore.Causality.RootMultiplication.HasLimitingPrinciple
    none1 none2 flat.essenceOf flat.esseOf x :=
  fun h => h.elim (fun h => h) (fun h => h.elim (fun h => h rfl) (fun ⟨_, _, h⟩ => h))

theorem controls : Certificate :=
  ⟨⟨inputs _, fun r _ => unlimited r,
      fun h => h true (unlimited true) () trivial,
      fun h => h true (twoRootsRoot true) () trivial⟩,
    ⟨inputs _, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, twoRootsRoot true⟩,
    ⟨inputs _,
      fun r hr _ h => Bool.noConfusion
        ((TruthCore.Results.Causality.PureActRoot.oneRootOnly r hr).symm.trans h),
      fun h => h false (unlimited false) () rfl,
      oneRootTrue, fun h => h.2 true ⟨trivial, trivial, rfl, rfl⟩⟩,
    ⟨fun _ _ => ⟨fun h => h, fun h => h, fun h => h rfl, fun h => h⟩,
      fun _ _ _ h => h.elim, ⟨⟨true, (), rfl⟩, fun _ h => h⟩,
      fun h => h true (unlimited true) () trivial,
      fun h => h true ⟨⟨true, (), rfl⟩, fun _ h => h⟩ () trivial⟩⟩

end Controls

end TruthCore.Results.Causality.RootPurity
