import TruthCore.Explanation.ExistencePSR
import TruthCore.Logic.ExcludedMiddle

/-! Optional analyst commitments about actual positive individual existence
facts at one selected world. All explanatory force is relative to Model.explains:
no adequate, concrete, noncircular, causal, or grounding explanation is added.
In particular NoBruteExistenceAt does not exclude the grounding-brute roots of
Causality.BruteFoundationRoutes. Negative facts and totality facts are outside
this signature; existence of a world/candidate type does not imply population. -/
namespace TruthCore.Explanation.NoBruteExistence
open TruthCore.Explanation.ExistencePSR
variable {World Being : Type}

/-- Every actually existing individual's positive existence fact has a reason
according to the chosen explains interpretation, at this world only. -/
def NoBruteExistenceAt (m : Model World Being) (w : World) : Prop :=
  ∀ x, m.ontic.ExistsAt w x → ∃ r, m.explains w r (.fact x)

/-- Some actual individual has no reason according to explains here. This is
not a grounding-root predicate or a judgment about metaphysical sufficiency. -/
def BruteExistenceAt (m : Model World Being) (w : World) : Prop :=
  ∃ x, m.ontic.ExistsAt w x ∧ ¬ ∃ r, m.explains w r (.fact x)

/-- Local coverage and incompatibility, together with the exact scope relation
to the already existing all-world existence-PSR. EM is supplied to coverage. -/
def LocalExistenceBoundary (m : Model World Being) (w : World) : Prop :=
  (NoBruteExistenceAt m w ∨ BruteExistenceAt m w) ∧
  ¬ (NoBruteExistenceAt m w ∧ BruteExistenceAt m w) ∧
  (ExistencePSR m ↔ ∀ v, NoBruteExistenceAt m v)

/-- A single sound interpretation can have no unexplained actual positive
existence facts at its designated world but a brute existence fact elsewhere. -/
def LocalDoesNotImplyGlobal : Prop :=
  ∃ m : Model Bool Bool, Sound m ∧ NoBruteExistenceAt m false ∧
    BruteExistenceAt m true ∧ ¬ ExistencePSR m
end TruthCore.Explanation.NoBruteExistence
