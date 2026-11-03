import TruthCore.Causality.ModalNecessaryBeingActuality
import TruthCore.Causality.ExistenceActuality
import TruthCore.Causality.NecessarilyUnderived

/-! Analyst configured adapter for the existing modalPossible/modalIsAt reading.
No assertion is made for arbitrary temporal Possible or independently true
metaphysical/act dictionaries. Existing convergence remains off the root. -/
namespace TruthCore.Results.Causality.ModalNecessaryBeingActuality
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (modalPossible modalIsAt)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Causality.ModalNecessaryBeingActuality
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

/-- Reflexive accessible possibility and existing-to-act give the OLD universal
bridge for this configured dictionary. Excluded middle supplies actual existence. -/
theorem hasBeing {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (esse : R)
    (hEM : ExcludedMiddle) (hReflexive : ActualReflexive m.ontic w)
    (hExisting : ExistingInActAt m.ontic InAct esse w) :
    ConfiguredHasBeing m w InAct esse := by
  sorry

/-- Compose the OLD tertia-via convergence theorem on the SAME configured
ontology. Maximum existence, God naming and root migration are not conclusions. -/
theorem convergence {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (CausesNecessityOf : B → B → Prop)
    (hEM : ExcludedMiddle) (hReflexive : ActualReflexive m.ontic w)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity
      (modalPossible m w) (modalIsAt m) CausesIn esse CausesNecessityOf) :
    ConfiguredConvergence m w CausesNecessityOf InAct MoreIn esse := by
  sorry

end TruthCore.Results.Causality.ModalNecessaryBeingActuality
