import TruthCore.Explanation.ExistencePSR
import TruthCore.Causality.JointGroups

/-!
Typed analyst extraction motivated by the materialized Dasgupta §9 reading.
The existing Groups record is reused for joint fact-ground records, without
Exercise, physical causation or event occurrence. Members (contributors and
enablers together) record the COMPLETE antecedent list in this application.
Positive existence reuses ExistenceFact.fact. Essential-existence labels are
not modal truths or proofs of a bearer. No truth, sufficiency, actual ground,
autonomy or causal property is inferred from record admission alone.
See docs/notes/underived-essence-identity.md for meanings and open applications.
-/
namespace TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.ExistencePSR
open TruthCore.Causality.JointGroups

/-- Positive existence, essential existence, and other fact labels. The two
existential forms remain distinct; no logical essence operator is encoded. -/
abbrev Fact (B O : Type) := Sum (ExistenceFact B) (Sum B O)

def positive {B O : Type} (b : B) : Fact B O := .inl (.fact b)
def essential {B O : Type} (b : B) : Fact B O := .inr (.inl b)
def other {B O : Type} (o : O) : Fact B O := .inr (.inr o)

/-- A syntactic classification of fact labels, not a claim of truth. -/
def ExistenceRelated {B O : Type} : Fact B O → Prop
  | .inl _ => True
  | .inr (.inl _) => True
  | .inr (.inr _) => False

/-- Some admitted full ground record of this positive existence label has
only autonomous members. This is the strong ultimate-ground input, not local
coverage, and says nothing about whether autonomous facts explain themselves. -/
def AutonomousFullGround {B O G : Type} (h : Groups (Fact B O) G)
    (autonomous : Fact B O → Prop) (b : B) : Prop :=
  ∃ g, h.admitted g ∧ h.effect g = positive b ∧
    ∀ f ∈ h.members g, autonomous f

/-- Every admitted full ground record of this target includes at least one
existence-related member. Other members may be nonexistential. This is distinct
from every member being existential, truth or sufficiency. -/
def IngredientAt {B O G : Type} (h : Groups (Fact B O) G) (b : B) : Prop :=
  ∀ g, h.admitted g → h.effect g = positive b →
    ∃ f ∈ h.members g, ExistenceRelated f

/-- Preserve the SAME full record along with one autonomous existential member.
The chosen member is not asserted sufficient, true or essential rather than
positive. Other members and conditions have not been deleted. -/
def AutonomousExistenceIngredient {B O G : Type} (h : Groups (Fact B O) G)
    (autonomous : Fact B O → Prop) (b : B) : Prop :=
  ∃ g, h.admitted g ∧ h.effect g = positive b ∧
    (∀ f ∈ h.members g, autonomous f) ∧
    ∃ f ∈ h.members g, ExistenceRelated f ∧ autonomous f

/-- A mixed complete ground record: one essential-existence label and one
other condition. The latter is kept as an enabler to ensure extraction handles
the full member union rather than forgetting conditions. No reality claim. -/
def mixed : Groups (Fact Unit Unit) Unit where
  contributors := fun _ => {essential ()}
  enablers := fun _ => {other ()}
  effect := fun _ => positive ()
  admitted := fun _ => True

def mixedAutonomous (f : Fact Unit Unit) : Prop :=
  f = essential () ∨ f = other ()

/-- The two premises and extracted conclusion coexist with a nonexistential
member of that SAME ground. A witnessed formal scope separation only. -/
def MixedCertificate : Prop :=
  AutonomousFullGround mixed mixedAutonomous () ∧ IngredientAt mixed () ∧
  AutonomousExistenceIngredient mixed mixedAutonomous () ∧
  ∃ f ∈ mixed.members (), ¬ ExistenceRelated f

end TruthCore.Explanation.ExistenceIngredient
