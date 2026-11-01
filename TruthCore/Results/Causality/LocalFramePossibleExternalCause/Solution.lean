import TruthCore.Causality.LocalFramePossibleExternalCause

namespace TruthCore.Results.Causality.LocalFramePossibleExternalCause
open TruthCore.Causality.LocalFramePossibleExternalCause
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Modal (Euclidean)

/-- Preserve the original concrete causal witness and its accessible world.
Only existence/necessity transfer to `w`; no cause at `w`, exercised power at
`w` or modal persistence of the totality-cause relation is inferred. -/
theorem sameCause {W B : Type} (s : Scenario W B) (w : W)
    (hEuclidean : Euclidean s.ontic.frame)
    (hReflexive : ActualReflexive s.ontic w)
    (hPossible : PossiblyExternallyCausedAt s w) :
    ∃ v, s.ontic.frame.access w v ∧ ContingencyBeginsAt s v ∧ ∃ c,
      s.concrete c ∧ s.ontic.ExistsAt v c ∧ s.causesContingencyTotality v c ∧
      OutsideContingentTotalityAt s v c ∧ NecessaryAt s.ontic v c ∧
      s.ontic.ExistsAt w c ∧ NecessaryAt s.ontic w c := by
  obtain ⟨v, hwv, hBegins, c, hc, he, hCause, hOutside⟩ := hPossible
  have hNecessary := necessaryOfExternalCandidate s v c hc he hOutside
  exact ⟨v, hwv, hBegins, c, hc, he, hCause, hOutside, hNecessary,
    hNecessary w (hEuclidean w v w hwv hReflexive),
    fun z hwz => hNecessary z (hEuclidean w v z hwv hwz)⟩

/-- Base possible-cause theorem with precisely the old causal premise and
weaker frame scope. The concrete predicate is the original Scenario field. -/
theorem necessaryConcreteOfPossibleCause {W B : Type} (s : Scenario W B) (w : W)
    (hEuclidean : Euclidean s.ontic.frame)
    (hReflexive : ActualReflexive s.ontic w)
    (hPossible : PossiblyExternallyCausedAt s w) : NecessaryConcreteAt s w := by
  obtain ⟨_, _, _, c, hc, _, _, _, _, he, hn⟩ :=
    sameCause s w hEuclidean hReflexive hPossible
  exact ⟨c, hc, he, hn⟩

theorem necessaryConcrete {W B : Type} (s : Scenario W B) (w : W)
    (hEuclidean : Euclidean s.ontic.frame)
    (hReflexive : ActualReflexive s.ontic w)
    (hBeginning : PossiblyBeginsAt s w)
    (hOpportunity : CausalOpportunityAt s w) : NecessaryConcreteAt s w := by
  exact necessaryConcreteOfPossibleCause s w hEuclidean hReflexive
    (hOpportunity hBeginning)

end TruthCore.Results.Causality.LocalFramePossibleExternalCause
