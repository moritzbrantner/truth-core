import TruthCore.Causality.WorldSourceRegress
import TruthCore.Causality.NamedPotentialCauser

/-! A fresh finite control; the prior frozen Bool predecessor control stays
unchanged. Every causal edge stays inside its own world. World-specific ranks
used in the proof witness ordinary graph WF, not temporal order or duration.
Root-value sets below are Set images of the EXISTING Graph.Source predicate
on Actual nodes; no new root criterion or absent-node starter is introduced. -/
namespace TruthCore.Models.WorldIndexedSources
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.WorldSourceRegress

def model : Ontic (Fin 3) Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => x = false ∨ (x = true ∧ w ≠ 2)
  Causes := fun w source target =>
    (w = 0 ∧ source = true ∧ target = false) ∨
    (w = 1 ∧ source = false ∧ target = true)

/-- Full joint acyclic-world omission/root-variation profile. Its necessary-only
union is empty, while overlaying ALL world-labelled edges can create a cycle;
neither is an actual cross-world causal path. No metaphysical possibility or
common starter follows from the pointwise source classification. -/
def JointControl : Prop :=
  SoundDistinctCauses model ∧
  (∀ w, WellFounded (model.Causes w)) ∧ ActualAcyclic model ∧
  ActualReflexive model 0 ∧ NecessaryAt model 0 false ∧
  OtherDirectedPotentialCause model 0 false ∧
  WellFoundedUnionNecessarySupport model model.Causes 0 ∧
  ContingentAt model 0 true ∧ model.Causes 0 true false ∧
  ¬ NoContingentGroundOfNecessary model model.Causes 0 ∧
  ¬ NamedNecessarilyUnderived model model.Causes 0 false ∧
  (Subtype.val '' {x : Actual model 0 | (actualGraph model 0).Source x} = {true}) ∧
  (Subtype.val '' {x : Actual model 1 | (actualGraph model 1).Source x} = {false}) ∧
  (Subtype.val '' {x : Actual model 2 | (actualGraph model 2).Source x} = {false}) ∧
  (¬ ∃ x : Bool, ∀ w : Fin 3,
    x ∈ Subtype.val '' {s : Actual model w | (actualGraph model w).Source s}) ∧
  StarterWorlds model = Set.univ ∧ RegressWorlds model = ∅
end TruthCore.Models.WorldIndexedSources
