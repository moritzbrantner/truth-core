import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Causality.ContingentAtomicity
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Causality.ScopedActualCausality.Solution
import TruthCore.Results.Causality.ContingentAtomicity.Solution

namespace TruthCore.Results.Causality.ConcreteAtomisticNecessaryBeing
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteUnderived (concreteOntic)
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.ScopedActualCausality
open TruthCore.Causality.ContingentAtomicity
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Logic (ExcludedMiddle)

/-- Assembly on the EXISTING rigid concrete candidate restriction. Ordinary
Causes stays separate from Profile.grounds, which this theorem never uses.
The SAME concrete witness and original frame/existence fields are retained. -/
theorem scopedConcrete {W B : Type} (m : Profile W B) (w : W)
    [PartialOrder (Actual (concreteOntic m) w)]
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hAtomic : AtomicParts (Actual (concreteOntic m) w))
    (hCover : ConditionalCausedSimpleCover (actualGraph (concreteOntic m) w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph (concreteOntic m) w))
    (hEM : ExcludedMiddle)
    (hCoverage : SelectedActualCausalCoverage (concreteOntic m) w) :
    NecessaryConcreteAt m w := by
  obtain ⟨b, hc, he⟩ := hPop
  have hp : ObjectPopulation (Actual (concreteOntic m) w) := ⟨⟨⟨b, hc⟩, he⟩⟩
  obtain ⟨c, hActual, hNecessary⟩ :=
    TruthCore.Results.Causality.ScopedActualCausality.necessaryBeing
      (concreteOntic m) w hp hAtomic hCover hNoOverlap hEM hCoverage
  exact ⟨c.val, c.property, hActual, hNecessary⟩

/-- Assembly with atomicity restricted to actually contingent concrete
candidates. No structural premise is imported from an unrestricted domain. -/
theorem contingent {W B : Type} (m : Profile W B) (w : W)
    [PartialOrder (Actual (concreteOntic m) w)]
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hAtomic : ContingentAtomicParts (concreteOntic m) w)
    (hCover : ConditionalCausedSimpleCover (actualGraph (concreteOntic m) w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph (concreteOntic m) w))
    (hEM : ExcludedMiddle)
    (hCoverage : SelectedActualCausalCoverage (concreteOntic m) w) :
    NecessaryConcreteAt m w := by
  obtain ⟨b, hc, he⟩ := hPop
  have hp : ObjectPopulation (Actual (concreteOntic m) w) := ⟨⟨⟨b, hc⟩, he⟩⟩
  obtain ⟨c, hActual, hNecessary⟩ :=
    TruthCore.Results.Causality.ContingentAtomicity.necessaryBeing
      (concreteOntic m) w hp hAtomic hCover hNoOverlap hEM hCoverage
  exact ⟨c.val, c.property, hActual, hNecessary⟩

end TruthCore.Results.Causality.ConcreteAtomisticNecessaryBeing
