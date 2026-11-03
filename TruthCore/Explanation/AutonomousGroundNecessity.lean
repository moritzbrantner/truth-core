import TruthCore.Explanation.ExistenceIngredient
import TruthCore.Explanation.JointCondition

/-! Selected-target analyst consumer of complete autonomous fact grounds.
The strong full-ground premise is NOT inferred from the owner's scoped PSR.
Autonomous necessity and whole-ground necessitation are separate OPEN inputs.
Fact labels are not beings; no efficient cause, selected R, essential-label
realization, IngredientAt, well-foundedness or modal frame law is introduced. -/
namespace TruthCore.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCondition
open TruthCore.Causality.JointGroups

/-- Explicit actual concrete target, not hidden in a carrier/subtype parameter. -/
def ActualConcreteTargetAt {W B O : Type} (A : Arena W B (Fact B O))
    (Concrete : B → Prop) (w : W) (b : B) : Prop :=
  Concrete b ∧ A.ontic.ExistsAt w b

/-- Autonomous facts are true at every accessible world of this SAME Arena.
This is separate from autonomy, actual truth and explanatory coverage. -/
def AutonomousFactsNecessaryAt {W B F : Type} (A : Arena W B F)
    (autonomous : F → Prop) (w : W) : Prop :=
  ∀ f, autonomous f → ∀ v, Access A w v → A.holds v f

/-- All members of an admitted full ground jointly necessitate THIS target.
The full contributor/enabler union is retained; no single-member sufficiency
or ordinary efficient causation is asserted. -/
def WholeGroundNecessitatesTargetAt {W B O G : Type}
    (A : Arena W B (Fact B O)) (h : Groups (Fact B O) G) (w : W) (b : B) : Prop :=
  ∀ g, h.admitted g → h.effect g = positive b →
    ∀ v, Access A w v → JointTrue A (h.members g) v → A.holds v (positive b)

/-- Target-local version of existing Arena.Coherent, with the SAME positive
constructor explicitly aligned to A.exist. No dummy Arena or profile equality
is hidden in the parameters; nothing is assumed about other existence labels. -/
def PositiveTargetCoherent {W B O : Type} (A : Arena W B (Fact B O)) (b : B) : Prop :=
  A.exist b = positive b ∧ ∀ v, A.holds v (A.exist b) ↔ A.ontic.ExistsAt v b

/-- Reuse ordinary fact coherence when the target's label is aligned. This
helper supplies no truth, autonomy, modal necessity or actual bearer. -/
theorem targetCoherenceOfCoherent {W B O : Type} (A : Arena W B (Fact B O)) (b : B)
    (hCoherent : Coherent A) (hLabel : A.exist b = positive b) :
    PositiveTargetCoherent A b :=
  ⟨hLabel, fun v => hCoherent v b⟩

/-- The selected target is not contingent in the SAME Ontic/frame. This does
not by itself assert actual presence, a concrete root, God or universal collapse. -/
def TargetNotContingentAt {W B O : Type} (A : Arena W B (Fact B O)) (w : W) (b : B) : Prop :=
  ¬ TruthCore.German.Kant.CosmologicalInference.ContingentAt A.ontic w b

end TruthCore.Explanation.AutonomousGroundNecessity
