import TruthCore.Causality.EsseCausePriority

namespace TruthCore.Results.Causality.EsseCausePriority
open TruthCore.Causality.EsseCausePriority
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority
  ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.CreatureSenses (CausedEsseIsHad)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.ActPriorityAtFirst
open TruthCore.Causality.ComponentFirstness
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The composition of #1604: a distinct cause `c` of the esse of an actual
concretum `x` is, by the esse-cause bridge, a concrete ground of `x` existing at
`w`; both are then actual concreta related by grounding, so by the
grounding-to-priority bridge `c` is simply prior to `x`. No dependence or
separability premise. -/
theorem actualEsseCausePriority {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) (PriorSimply : B → B → Prop)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hPrior : ActualGroundingIsSimplePriority m w PriorSimply) :
    ActualEsseCausePriority m w CausesIn esse PriorSimply := by
  sorry

/-- The actuality antecedent discharged: an effect of a cause of esse has esse
(`CausedEsseIsHad`), hence exists at `w` and is concrete in the profile, so the
scoped priority applies to it. Reuses `actualEsseCausePriority`'s conclusion as
a premise. -/
theorem distinctEsseCausePriority {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (PriorSimply : B → B → Prop)
    (hScoped : ActualEsseCausePriority m w CausesIn esse PriorSimply)
    (hHad : CausedEsseIsHad CausesIn InAct esse)
    (hExist : ActOfEsseSufficesForExistenceAt m.ontic InAct esse w)
    (hConc : EsseInReIsConcrete m InAct esse) :
    DistinctEsseCausePriority CausesIn esse PriorSimply := by
  sorry

/-- The q.3 a.1 conclusion from composition, with the cause-to-efficient bridge
and efficient-cause priority replaced by distinct-esse-cause priority: a first
being in act in some respect and in potency in another would be composite, so it
would have a distinct cause of its esse, which is prior to it, against
firstness. -/
theorem firstBeingNoPotencyOfEssePriority {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (Composite : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hInAct : FirstBeingIsInSomeAct InAct PriorSimply)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply := by
  sorry

/-- The first-being version of act priority from the same four premises, by
`firstBeingNoPotencyOfEssePriority`: it holds vacuously. -/
theorem weakOfEssePriority {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (Composite : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hInAct : FirstBeingIsInSomeAct InAct PriorSimply)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  sorry

/-- "No component is the first being" with efficient-cause priority replaced by
distinct-esse-cause priority. A component supposed first is in potency in some
respect, against act priority at a first being and non-overlap, or participated,
so it has a distinct cause of its esse, which is prior to it, against
firstness. The participation premise is the cause-of-being reading
`Round2Grounding.ParticipatedEsseHasDistinctCause` (the same body as
`ComponentFirstness.ParticipatedHasOtherCause`), so one cause-of-perfection
relation at esse runs through the whole argument. -/
theorem noComponentFirstOfEssePriority {B R : Type} (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hWeak : FirstBeingActPriority InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedEsseHasDistinctCause Participated CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply := by
  sorry

/-! ## Controls -/

/-- The batch controls. -/
theorem controls : TruthCore.Causality.EsseCausePriority.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.EsseCausePriority
