import TruthCore.Causality.PossibleCausalSourceNecessity
import TruthCore.Results.Causality.HeadlessCausalAncestry.Solution
import TruthCore.Results.Causality.WorldSourceRegress.Solution

namespace TruthCore.Results.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

/-- An existing source at one world cannot be contingent there under the
existing local causal principle. Explicit EM converts absence to necessity;
no frame property, concreteness or sufficiency of explanation is assumed. -/
theorem source_necessary_at {W B : Type} (m : Ontic W B) (v : W) (c : B)
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple m)
    (hExists : m.ExistsAt v c)
    (hSource : ¬ ∃ y, m.ExistsAt v y ∧ m.Causes v y c) : NecessaryAt m v c := by
  intro z hvz
  rcases hEM (m.ExistsAt z c) with hExistsZ | hAbsent
  · exact hExistsZ
  · obtain ⟨y, hyExists, hyCause, _⟩ := hCausal v c ⟨hExists, z, hvz, hAbsent⟩
    exact (hSource ⟨y, hyExists, hyCause⟩).elim

/-- Preserve the SAME accessible world and source individual. Sourcehood is
only at `v`; existence and necessity also transfer to `w`. Actual reflexivity
is used only to recover existence at `w`, not to infer universal accessibility. -/
theorem sameSource {W B : Type} (m : Ontic W B) (w : W)
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple m)
    (hEuclidean : Euclidean m.frame) (hReflexive : ActualReflexive m w)
    (hPossible : PossiblyFailedHeadlessCoverage m w) :
    ∃ v, m.frame.access w v ∧ ∃ c,
      m.ExistsAt v c ∧ (¬ ∃ y, m.ExistsAt v y ∧ m.Causes v y c) ∧
      NecessaryAt m v c ∧ m.ExistsAt w c ∧ NecessaryAt m w c := by
  obtain ⟨v, hwv, hFailure⟩ := hPossible
  obtain ⟨s, hs⟩ :=
    TruthCore.Results.Causality.HeadlessCausalAncestry.source_of_not_headless_coverage
      (TruthCore.Causality.WorldSourceRegress.actualGraph m v) hEM hFailure
  have hSource :=
    (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff m v s).mp hs
  have hNecessary := source_necessary_at m v s.val hEM hCausal s.property hSource
  exact ⟨v, hwv, s.val, s.property, hSource, hNecessary,
    hNecessary w (hEuclidean w v w hwv hReflexive),
    fun z hwz => hNecessary z (hEuclidean w v z hwv hwz)⟩

theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple m)
    (hEuclidean : Euclidean m.frame) (hReflexive : ActualReflexive m w)
    (hPossible : PossiblyFailedHeadlessCoverage m w) : NecessaryBeing m w := by
  obtain ⟨_, _, c, _, _, _, hc, hn⟩ :=
    sameSource m w hEM hCausal hEuclidean hReflexive hPossible
  exact ⟨c, hc, hn⟩

end TruthCore.Results.Causality.PossibleCausalSourceNecessity
