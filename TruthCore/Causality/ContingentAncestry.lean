import TruthCore.Causality.SelectedAncestry
import TruthCore.Explanation.ExplanatoryAdequacy

/-! Reuse the established contingent-reason descent on the positive-existence
fragment of one actual concrete grounding cone. No arbitrary fact is identified
with a bearer: ExistenceFact.fact is the existing explicit constructor. -/
namespace TruthCore.Causality.ContingentAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.SelectedAncestry
open TruthCore.Explanation.ExistencePSR (ExistenceFact)
open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Explanation.ExplanatoryAdequacy (Founded)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

variable {W B : Type}

/-- A representation of the selected actual-ground relation using only tagged
positive existence facts. Truth of fact x is DEFINITIONALLY x's world-relative
existence. Each admitted reason edge has actual concrete endpoints. This does
not say that every philosophical explanation is such a ground. -/
def existenceArena (m : Profile W B) : Arena W B (ExistenceFact B) where
  ontic := m.ontic
  holds v f := match f with | .fact x => m.ontic.ExistsAt v x
  exist := ExistenceFact.fact
  explains v r f := match r, f with
    | .fact source, .fact target =>
      ActualConcrete m v target ∧ ActualConcreteGround m v source target
  conjunct := fun _ _ => False

/-- Only existence facts of actual concrete members of this COMPLETE cone. -/
def coneFacts (m : Profile W B) (w : W) (selected : B) : ExistenceFact B → Prop
  | .fact x => Cone m w selected x

/-- The existing Founded predicate, restricted to contingent existence facts
in this cone. It leaves support involving necessary ancestors unrestricted. -/
def ContingentConeFounded (m : Profile W B) (w : W) (selected : B) : Prop :=
  Founded (existenceArena m) w (coneFacts m w selected)

/-- An actual concrete ancestor exists necessarily. It need not be a grounding
root, even at the actual world; necessary ancestors may support each other. -/
def NecessaryAncestor (m : Profile W B) (w : W) (selected : B) : Prop :=
  ∃ x, Cone m w selected x ∧ NecessaryAt m.ontic w x

/-- Full cone foundation implies contingent-only foundation. The converse is
not asserted; the same-profile cycle control separates them. -/
def FoundationComparison : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W) (selected : B),
    ConeWellFounded m w selected → ContingentConeFounded m w selected

end TruthCore.Causality.ContingentAncestry
