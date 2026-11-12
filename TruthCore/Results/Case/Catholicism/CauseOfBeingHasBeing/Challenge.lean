import TruthCore.Case.Catholicism.CauseOfBeingHasBeing

namespace TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing

open TruthCore.Case.Catholicism.CauseOfBeingHasBeing
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.Round2Grounding
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.CausalMapsBatch1 (CauseHasWhatItGives CauseOfBeingHasWhatItGives)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (ActualityOnlyInsofarAsBeingReading PerfectionsOfEffectPreexistInCauseReading)

/-- Every existent at `w` is concrete: it is in act as to being by the
existence-to-act contract, and what has esse in re is concrete by the
calibration. -/
theorem everyExistentConcreteOfCalibration {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (esse : R)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hConcrete : EsseInReIsConcrete m InAct esse) :
    EveryExistentConcreteAt m.ontic m.concrete w := by
  sorry

/-- The cause of the being of an actual thing exists at `w`: the effect exists,
so is in act as to being; the giver of its being is then in act as to being;
and what is in act as to being exists at `w`. -/
theorem esseCausesExistOfCauseHasBeing {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hGives : CauseOfABeingHasBeing InAct CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hSuffices : ActOfEsseSufficesForExistenceAt m.ontic InAct esse w) :
    EsseCausesExistAt m w CausesIn esse := by
  sorry

/-- The esse-cause bridge with its concreteness clause taken from the
concreteness of every existent, in place of the unscoped concreteness of every
cause of esse. -/
theorem esseCauseGroundOfExistentConcreteness {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) (DependsForBeing : B → B → Prop)
    (hExists : EsseCausesExistAt m w CausesIn esse)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w)
    (hDep : EsseEffectDependsOnItsCause CausesIn esse DependsForBeing)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    EsseCauseIsActualConcreteGround m w CausesIn esse := by
  sorry

/-- Agency in act and the q.4 a.1 ad 3 premise: a cause of being is in act in
some respect, and whatever is in act in some respect is in act as to being. -/
theorem causeOfBeingHasBeingOfAgency {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hAgent : CauseOfBeingIsInAct InAct CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse) :
    CauseOfBeingInActAsToBeing InAct CausesIn esse := by
  sorry

/-- Strength order: the unscoped maxim entails its restriction to causes of the
being of things in act as to being. -/
theorem causeOfABeingHasBeingOfHasBeing {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : CauseOfBeingInActAsToBeing InAct CausesIn esse) :
    CauseOfABeingHasBeing InAct CausesIn esse := by
  sorry

/-- Strength order: q.4 a.2 preexistence entails its esse instance. -/
theorem causeOfABeingHasBeingOfPreexistence {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPre : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) :
    CauseOfABeingHasBeing InAct CausesIn esse := by
  sorry

/-- Strength order: a cause of being has every perfection it causes in its
effect, so it has being. -/
theorem causeOfBeingHasBeingOfGives {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : CauseOfBeingHasWhatItGives CausesIn InAct esse) :
    CauseOfBeingInActAsToBeing InAct CausesIn esse := by
  sorry

/-- Strength order: the unrestricted "nothing gives what it does not have"
entails its restriction to causes of being. -/
theorem causeOfBeingGivesOfCauseGives {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : CauseHasWhatItGives CausesIn InAct) :
    CauseOfBeingHasWhatItGives CausesIn InAct esse := by
  sorry

/-- The finite controls hold. -/
theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing
