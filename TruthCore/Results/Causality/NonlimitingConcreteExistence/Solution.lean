import TruthCore.Causality.NonlimitingConcreteExistence
import TruthCore.Results.Modal.LimitationSeparation.Solution

namespace TruthCore.Results.Causality.NonlimitingConcreteExistence
open TruthCore.Causality.NonlimitingConcreteExistence
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal.LimitationPossibility (BackwardClosedAt)
open TruthCore.Modal (Euclidean)
open TruthCore.Isabelle.AFP.GoedelGod (Property)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Logic (ExcludedMiddle)

/-- Retain the SAME separated individual at the accessible world and selected
origin. Direct separation is needed: the old possible theorem cannot supply
an exemplar outside Q merely by projecting its weaker conclusion. -/
theorem sameIndividual {W B : Type} (m : Profile W B)
    (L : Property W B → W → Prop) (w : W)
    (hKnown : KnownAbsenceLimitingAt m L w)
    (hTarget : ConcreteExistenceNonlimitingAt m L w)
    (hClosure : BackwardClosedAt m.ontic.frame L w) (hEM : ExcludedMiddle)
    (hEuclidean : Euclidean m.ontic.frame) (hReflexive : ActualReflexive m.ontic w) :
    ∃ v, m.ontic.frame.access w v ∧ ∃ c, m.concrete c ∧ m.ontic.ExistsAt v c ∧
      NecessaryAt m.ontic v c ∧ m.ontic.ExistsAt w c ∧ NecessaryAt m.ontic w c := by
  have hSeparated := TruthCore.Results.Modal.LimitationSeparation.separate
    m.ontic.frame L (PossibleAbsence m) (ConcreteExistence m) w
    hKnown hTarget hClosure hEM
  obtain ⟨v, hwv, c, ⟨hc, he⟩, hNoAbsence⟩ := hSeparated
  have hn : NecessaryAt m.ontic v c := by
    intro u hvu
    rcases hEM (m.ontic.ExistsAt u c) with hPresent | hMissing
    · exact hPresent
    · exact (hNoAbsence ⟨u, hvu, hMissing⟩).elim
  have hOrigin := necessaryAtOrigin m.ontic w v c hEuclidean hReflexive hwv hn
  exact ⟨v, hwv, c, hc, he, hn, hOrigin.1, hOrigin.2⟩

/-- Six explicit inputs derive an actual necessary concrete individual.
Necessity is not inside the target property; grounds and causal laws are unused. -/
theorem necessaryConcrete {W B : Type} (m : Profile W B)
    (L : Property W B → W → Prop) (w : W)
    (hKnown : KnownAbsenceLimitingAt m L w)
    (hTarget : ConcreteExistenceNonlimitingAt m L w)
    (hClosure : BackwardClosedAt m.ontic.frame L w) (hEM : ExcludedMiddle)
    (hEuclidean : Euclidean m.ontic.frame) (hReflexive : ActualReflexive m.ontic w) :
    NecessaryConcreteAt m w := by
  obtain ⟨_, _, c, hc, _, _, he, hn⟩ :=
    sameIndividual m L w hKnown hTarget hClosure hEM hEuclidean hReflexive
  exact ⟨c, hc, he, hn⟩

/-- The exact old mixed ontology retains actual contingent existence while
jointly satisfying the six-input configuration with a NEW analyst classifier. -/
theorem checks (hEM : ExcludedMiddle) : JointControl := by
  have hKnown : KnownAbsenceLimitingAt controlProfile controlClassifier false := by
    intro hAbsent
    obtain ⟨u, _, hMissing⟩ := hAbsent
    exact hMissing True.intro
  have hTarget : ConcreteExistenceNonlimitingAt controlProfile controlClassifier false := by
    intro hLimiting
    exact hLimiting ⟨True.intro, True.intro⟩
  have hClosure : BackwardClosedAt controlProfile.ontic.frame controlClassifier false := by
    intro Phi Psi hInclusion hLimiting hPhi
    exact hLimiting (hInclusion false True.intro none hPhi)
  have hEuclidean : Euclidean controlProfile.ontic.frame := by
    intro w v u _ _
    exact TruthCore.Causality.PossibleCauseOfContingency.mixedUniversal v u
  have hReflexive : ActualReflexive controlProfile.ontic false :=
    TruthCore.Causality.PossibleCauseOfContingency.mixedUniversal false false
  refine ⟨hKnown, hTarget, hClosure, hEM, hEuclidean, hReflexive, ?_,
    ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact necessaryConcrete controlProfile controlClassifier false
      hKnown hTarget hClosure hEM hEuclidean hReflexive
  · exact ⟨True.intro, rfl,
      TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtFalse⟩
  · exact TruthCore.Causality.PossibleCauseOfContingency.mixedContingentAtFalse.2
  · intro u _
    exact True.intro

end TruthCore.Results.Causality.NonlimitingConcreteExistence
