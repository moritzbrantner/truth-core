import TruthCore.Modal.ExistenceDegrees
import TruthCore.Models.NecessarilyUnderived
import TruthCore.Models.PSR
import TruthCore.Modal.NecessaryContingentActivity

/-! Named refinement of the existing existential NecessarilyUnderived:
the identity of the selected necessary potential causer is retained. The
primitive R stays explicit. Results choosing R := m.Causes are restricted
causal-support profiles, not identifications of causation with grounding. -/
namespace TruthCore.Causality.NamedPotentialCauser
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees
open TruthCore.Modal.NecessaryContingentActivity

/-- The pointwise fiber of NecessarilyUnderived, before its outer existential
quantifier. Incoming sources must exist at their edge's world; that world need
not be accessible from the base. No reason token or divine attribute is given. -/
def NamedNecessarilyUnderived {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) (n : Being) : Prop :=
  m.ExistsAt w n ∧ NecessaryAt m w n ∧
    ∀ v source, m.ExistsAt v source → ¬ R v source n

/-- The unchanged registered varying interpretation gives a nonvacuous
positive profile. Its source has an actual other-directed effect at world
true, though no causal edge holds at base false. Both candidates are necessary. -/
def VaryingNamedControl : Prop :=
  let m := TruthCore.Models.NecessarilyUnderived.varying
  ActualReflexive m false ∧ NecessaryAt m false false ∧
  OtherDirectedPotentialCause m false false ∧
  NoContingentGroundOfNecessary m m.Causes false ∧
  WellFoundedUnionNecessarySupport m m.Causes false ∧
  NamedNecessarilyUnderived m m.Causes false false ∧
  m.ExistsAt true true ∧ m.Causes true false true

/-- A separate causal assignment on the old contingent-only ontology.
At false both candidates exist and cause each other; at true only false exists
and no causal edge holds. Source and target presence are not a loophole. -/
def contingentPredecessor : Ontic Bool Bool :=
  { TruthCore.Models.PSR.ContingentOnly.model.ontic with
    Causes := fun w source target => w = false ∧ source ≠ target }

/-- Omit only the no-contingent-predecessor bridge from the named theorem.
The necessary-only edge union is well-founded, but an existing contingent
individual actually causes the selected necessary potential causer. This
control does not claim worldwise well-foundedness (false has a 2-cycle).
It is outside the owner's acyclic-world setting, and tests only the weaker
background without pointwise causal WF. -/
def ContingentPredecessorControl : Prop :=
  let m := contingentPredecessor
  ActualReflexive m false ∧ NecessaryAt m false false ∧
  OtherDirectedPotentialCause m false false ∧ SoundDistinctCauses m ∧
  WellFoundedUnionNecessarySupport m m.Causes false ∧
  ContingentAt m false true ∧ m.Causes false true false ∧
  ¬ NoContingentGroundOfNecessary m m.Causes false ∧
  ¬ NamedNecessarilyUnderived m m.Causes false false
end TruthCore.Causality.NamedPotentialCauser
