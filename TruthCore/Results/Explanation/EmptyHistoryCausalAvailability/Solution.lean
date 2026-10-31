import TruthCore.Explanation.EmptyHistoryCausalAvailability

namespace TruthCore.Results.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Explanation.PSRStrength (Arena Contingent)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt NecessaryBeing ContingentAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

/-- Only the caused-fact branch promises a CauseFact role. Preserve that
SAME actual concrete c, using the SAME fact's truth at u to exclude contingency. -/
theorem causeOfNegativeFactNecessary {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (CauseFact : W → B → F → Prop) (f : F) (u : W)
    (hEM : ExcludedMiddle) (hMeaning : NegativeFactMeaning A Concrete f)
    (hCaused : ActualCausedFact A Concrete CauseFact u f) :
    ∃ c, Concrete c ∧ A.ontic.ExistsAt u c ∧ CauseFact u c f ∧ NecessaryAt A.ontic u c := by
  obtain ⟨hf, c, hc, he, hCause⟩ := hCaused
  exact ⟨c, hc, he, hCause,
    necessaryOfActualNoncontingent A Concrete u c hEM ((hMeaning u).mp hf) hc he⟩

/-- Preserve the original concrete predicate and SAME chosen individual in
each branch. If the coverage world already has a concrete individual, no
causal role is inferred for it; only the second branch uses CauseFact. -/
theorem necessaryConcrete {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (CauseFact : W → B → F → Prop) (w : W) (f : F)
    (hEM : ExcludedMiddle) (hEuclidean : Euclidean A.ontic.frame)
    (hReflexive : ActualReflexive A.ontic w)
    (hMeaning : NegativeFactMeaning A Concrete f)
    (hCoverage : AccessibleEmptyCoverage A Concrete CauseFact w)
    (hPositive : PossiblyInhabitedConcreteAt A Concrete w) :
    ∃ c, Concrete c ∧ A.ontic.ExistsAt w c ∧ NecessaryAt A.ontic w c := by
  obtain ⟨v, hwv, hNoCont, hAvailable⟩ := hCoverage
  rcases hEM (∃ c, Concrete c ∧ A.ontic.ExistsAt v c) with hPresent | hEmpty
  · obtain ⟨c, hc, he⟩ := hPresent
    have hn := necessaryOfActualNoncontingent A Concrete v c hEM hNoCont hc he
    have hOrigin := necessaryAtOrigin A w v c hEuclidean hReflexive hwv hn
    exact ⟨c, hc, hOrigin.1, hOrigin.2⟩
  · obtain ⟨p, hwp, b, hb, he⟩ := hPositive
    have hContingentB : ContingentAt A.ontic p b :=
      ⟨he, v, hEuclidean w p v hwp hwv, fun hExists => hEmpty ⟨b, hb, hExists⟩⟩
    have hNotFact : ¬ A.holds p f := by
      intro hf
      exact ((hMeaning p).mp hf) b hb hContingentB
    have hContingentFact : Contingent A v f :=
      ⟨(hMeaning v).mpr hNoCont, p, hEuclidean w v p hwv hwp, hNotFact⟩
    obtain ⟨u, hvu, hCaused⟩ := hAvailable f hContingentFact
    obtain ⟨c, hc, _, _, hn⟩ :=
      causeOfNegativeFactNecessary A Concrete CauseFact f u hEM hMeaning hCaused
    have hOrigin := necessaryAtOrigin A w u c hEuclidean hReflexive
      (accessibleSecondStep A w v u hEuclidean hReflexive hwv hvu) hn
    exact ⟨c, hc, hOrigin.1, hOrigin.2⟩

theorem necessaryBeing {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (CauseFact : W → B → F → Prop) (w : W) (f : F)
    (hEM : ExcludedMiddle) (hEuclidean : Euclidean A.ontic.frame)
    (hReflexive : ActualReflexive A.ontic w)
    (hMeaning : NegativeFactMeaning A Concrete f)
    (hCoverage : AccessibleEmptyCoverage A Concrete CauseFact w)
    (hPositive : PossiblyInhabitedConcreteAt A Concrete w) : NecessaryBeing A.ontic w := by
  obtain ⟨c, _, he, hn⟩ :=
    necessaryConcrete A Concrete CauseFact w f hEM hEuclidean hReflexive hMeaning hCoverage hPositive
  exact ⟨c, he, hn⟩

end TruthCore.Results.Explanation.EmptyHistoryCausalAvailability
