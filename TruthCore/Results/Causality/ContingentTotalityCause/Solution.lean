import TruthCore.Causality.ContingentTotalityCause
import TruthCore.Results.Causality.ExternalCandidateNecessity.Solution

namespace TruthCore.Results.Causality.ContingentTotalityCause
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.ContingentTotalityCause

/-- Conditional typed connection only: coverage and an actual outside-parts
cause yield a necessary cause of the same whole. No whole-level cause is
inferred from member-level causal laws. -/
theorem necessaryCause {W B : Type} [PartialOrder B]
    (s : Scenario W B) (w : W) (whole : B)
    (hCover : ContingentsCovered s w whole)
    (hCause : ExternalWholeCause s w whole) :
    NecessaryWholeCause s w whole := by
  classical
  rcases hCause with ⟨c, hOutside, hc, he, hCausal⟩
  -- Restrict only the concrete predicate, retaining the original identity,
  -- existence, worlds and causal relation. This forces the imported
  -- existential equivalence to return this same causal witness.
  let selected : Scenario W B := { s with concrete := fun x => x = c }
  have hSelected : ExternalCandidateAt selected w := by
    refine ⟨c, rfl, he, ?_⟩
    intro x hx hCont _
    have hxC : x = c := hx
    subst x
    exact hOutside (hCover c ⟨hc, hCont⟩)
  rcases (TruthCore.Results.Causality.ExternalCandidateNecessity.checks
    W B selected w).mp hSelected with ⟨d, hd, _, hNec⟩
  have hdC : d = c := hd
  subst d
  exact ⟨c, hc, he, hNec, hCausal⟩


/-- Connect the same typed totality route to the shared actual necessary-being
interface. The stronger necessaryCause theorem additionally retains causation. -/
theorem necessaryBeing {W B : Type} [PartialOrder B]
    (s : Scenario W B) (w : W) (whole : B)
    (hCover : ContingentsCovered s w whole)
    (hCause : ExternalWholeCause s w whole) :
    NecessaryBeing s.ontic w := by
  rcases necessaryCause s w whole hCover hCause with ⟨c, _, he, hn, _⟩
  exact ⟨c, he, hn⟩

end TruthCore.Results.Causality.ContingentTotalityCause
