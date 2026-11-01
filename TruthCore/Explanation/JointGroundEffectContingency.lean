import TruthCore.Explanation.AutonomousGroundNecessity

/-!
Selected-record consumer of existing whole-ground necessitation. The record's
admission and positive-target identity are explicit inputs, not hidden in a
subtype. No aggregate fact, actual bearer, causal relation, autonomous necessity
or target-truth/existence coherence is introduced. Necessitation is not inferred
from explanatory adequacy or admission.
-/
namespace TruthCore.Explanation.JointGroundEffectContingency
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Causality.JointGroups

/-- The supplied record is admitted and its effect is this SAME positive b.
This asserts neither truth, explanatory adequacy, causal exercise nor necessity. -/
def SelectedPositiveGround {B O G : Type} (h : Groups (Fact B O) G)
    (g : G) (b : B) : Prop :=
  h.admitted g ∧ h.effect g = positive b

end TruthCore.Explanation.JointGroundEffectContingency
