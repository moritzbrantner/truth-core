import Mathlib.Order.Bounds.Basic
import TruthCore.Modal.ExistenceDegrees

/-! Attainment of the selected individual's own accessible-world degree
family. Mathlib's IsGreatest on the image of the accessible-world set expresses
an attained upper bound, rather than mere boundedness. Preorder-equivalent
labels may still differ. This is an analyst's mathematical bridge, not a new
attributed philosophical premise. -/
namespace TruthCore.Modal.ExistenceDegrees
open TruthCore.German.Kant.CosmologicalInference

/-- The selected individual's degree image over the root-accessible family
has a greatest member. Presence and necessity are separate; the theorem uses
NecessaryAt to ensure these assigned degrees belong to existing individuals.
An empty accessible family has no image member and cannot satisfy this. -/
def SelectedDegreeFamilyAttains {World Being Degree : Type} [Preorder Degree]
    (m : Ontic World Being) (intensity : World → Being → Degree)
    (w₀ : World) (n : Being) : Prop :=
  ∃ d, IsGreatest ((fun v => intensity v n) '' {v | m.frame.access w₀ v}) d

/-- Possible global attainment is equivalent to attainment in the selected
individual's own degree family. The equivalence's explicit hypotheses are in
the registered argument; this proposition does not assume invariance, actual
reflexivity, or a nonempty accessible family. -/
def GlobalAttainmentIffSelectedFamily {World Being Degree : Type} [Preorder Degree]
    (m : Ontic World Being) (intensity : World → Being → Degree)
    (w₀ : World) (n : Being) : Prop :=
  AttainedGlobalDegreeMaximum m intensity w₀ ↔
    SelectedDegreeFamilyAttains m intensity w₀ n

end TruthCore.Modal.ExistenceDegrees
