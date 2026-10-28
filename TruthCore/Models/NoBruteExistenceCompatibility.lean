import TruthCore.Causality.BruteFoundationBoundary
import TruthCore.Explanation.ExistencePSR

/-! A source-free compatibility expansion of the existing contingent-root
interpretation. Only explanation labels are added; the old ontology and its
separate grounding assignment are unchanged. The intrinsic tag establishes
neither explanatory adequacy nor grounding by an actual concrete individual.
-/
namespace TruthCore.Models.NoBruteExistenceCompatibility
open TruthCore.Explanation.ExistencePSR
open TruthCore.Causality.BruteFoundationBoundary

def model : Model Bool (Bool × Bool) where
  ontic := boundaryRival.ontic
  explains := fun w r f => match f with
    | .fact x => boundaryRival.ontic.ExistsAt w x ∧ r = .intrinsic x

/-- Explanation coverage and truth soundness coexist with the existing
contingent ground-root rival. This concerns one fixed joint interpretation,
not independently sufficient explanation or an absence of every kind of reason. -/
def JointWitness : Prop :=
  Sound model ∧ ExistencePSR model ∧
  ¬ NecessaryConcreteAt boundaryRival false ∧
  ¬ EveryContingentGroundedAt boundaryRival false

/-- Truth soundness is just the explicit existence conjunct. -/
theorem sound : Sound model := by
  intro w x r h
  exact h.1

/-- One stipulated token per existing fact supplies coverage, not adequacy. -/
theorem psr : ExistencePSR model := by
  intro w x hx
  exact ⟨.intrinsic x, hx, rfl⟩

/-- Compose the old contingent-root certificates in the same interpretation. -/
theorem jointWitness : JointWitness :=
  ⟨sound, psr, boundaryRivalNoNecessary, boundaryRivalHasBruteRoot⟩

end TruthCore.Models.NoBruteExistenceCompatibility
