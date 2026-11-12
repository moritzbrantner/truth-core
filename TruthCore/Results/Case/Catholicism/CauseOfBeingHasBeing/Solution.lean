module

public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing

@[expose] public section

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
    EveryExistentConcreteAt m.ontic m.concrete w :=
  fun x hx => hConcrete x (hExisting x hx)

/-- The cause of the being of an actual thing exists at `w`: the effect exists,
so is in act as to being; the giver of its being is then in act as to being;
and what is in act as to being exists at `w`. -/
theorem esseCausesExistOfCauseHasBeing {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hGives : CauseOfABeingHasBeing InAct CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hSuffices : ActOfEsseSufficesForExistenceAt m.ontic InAct esse w) :
    EsseCausesExistAt m w CausesIn esse := by
  intro c x hx hc
  have hxAct : InAct x esse := hExisting x hx.2
  have hcAct : InAct c esse := hGives c x hc hxAct
  exact hSuffices c hcAct

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
  intro c x hne hx hc
  have hcE : m.ontic.ExistsAt w c := hExists c x hx hc
  have hcC : m.concrete c := hConcrete c hcE
  exact ⟨hcC, hcE, hGround c x hx ⟨hcC, hcE⟩ (hDep c x hne hc)⟩

/-- Agency in act and the q.4 a.1 ad 3 premise: a cause of being is in act in
some respect, and whatever is in act in some respect is in act as to being. -/
theorem causeOfBeingHasBeingOfAgency {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hAgent : CauseOfBeingIsInAct InAct CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse) :
    CauseOfBeingInActAsToBeing InAct CausesIn esse := by
  intro c x hc
  obtain ⟨r, hr⟩ := hAgent c x hc
  exact hBeing c r hr

/-- Strength order: the unscoped maxim entails its restriction to causes of the
being of things in act as to being. -/
theorem causeOfABeingHasBeingOfHasBeing {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : CauseOfBeingInActAsToBeing InAct CausesIn esse) :
    CauseOfABeingHasBeing InAct CausesIn esse :=
  fun c x hc _ => h c x hc

/-- Strength order: q.4 a.2 preexistence entails its esse instance. -/
theorem causeOfABeingHasBeingOfPreexistence {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPre : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) :
    CauseOfABeingHasBeing InAct CausesIn esse :=
  fun c x hc hx => hPre c x esse hc hx

/-- Strength order: a cause of being has every perfection it causes in its
effect, so it has being. -/
theorem causeOfBeingHasBeingOfGives {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : CauseOfBeingHasWhatItGives CausesIn InAct esse) :
    CauseOfBeingInActAsToBeing InAct CausesIn esse :=
  fun c x hc => h c x esse hc hc

/-- Strength order: the unrestricted "nothing gives what it does not have"
entails its restriction to causes of being. -/
theorem causeOfBeingGivesOfCauseGives {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : CauseHasWhatItGives CausesIn InAct) :
    CauseOfBeingHasWhatItGives CausesIn InAct esse :=
  fun c x r _ hc => h c x r hc

/-- The finite controls hold. -/
theorem controls : Control.Controls := by
  unfold Control.Controls
  delta EsseInReIsConcrete ExistingInActAt EveryExistentConcreteAt ActOfEsseSufficesForExistenceAt CauseOfABeingHasBeing CauseOfBeingInActAsToBeing CauseOfBeingIsInAct EsseCausesExistAt EsseEffectDependsOnItsCause ActualDependenceIsGrounding EsseCauseIsActualConcreteGround ActualityOnlyInsofarAsBeingReading PerfectionsOfEffectPreexistInCauseReading CauseOfBeingHasWhatItGives CauseHasWhatItGives TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround TruthCore.Causality.NecessaryRootFork.ActualConcrete TruthCore.Ontology.ConcreteAbstract.HasEsseInRe Control.prof Control.causesBeing Control.causesAll Control.esse
  and_intros <;> decide

end TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing
