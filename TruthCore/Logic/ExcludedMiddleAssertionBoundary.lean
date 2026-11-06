module

public import TruthCore.Logic.ExcludedMiddle

/-!
Assertion policy is distinct from the object-level proposition ExcludedMiddle.
These analyst propositions use the existing stage-indexed assertion markers;
no bridge from logical holding to proof-known or assertion is assumed.
The controls concern exactly that encoded policy subset, not the intended
semantics of a complete intuitionist logic or its historical interpretation.
-/
@[expose] public section
namespace TruthCore.Logic.ExcludedMiddleAssertionBoundary
open TruthCore.Logic

/-- Every stage asserts every instance. This comparison policy is not adopted
as a correct assertion norm and is not a source attribution. -/
def AllInstancesAsserted {Stage : Type} (Asserts : Stage → Prop → Prop) : Prop :=
  ∀ s p, Asserts s (p ∨ ¬ p)

/-- Exact negation of the same policy, not object-level negation of EM. -/
def NotAllInstancesAsserted {Stage : Type} (Asserts : Stage → Prop → Prop) : Prop :=
  ¬ AllInstancesAsserted Asserts

/-- With explicit object-level EM, the existing withholding-policy subset may
hold. Separately, failure of the full raw withholding package need not imply
universal assertion. Marker models are not complete epistemic/intuitionist models. -/
def Controls : Prop :=
  (∃ (Proved Asserts : Unit → Prop → Prop),
    ExcludedMiddleWithheld Proved Asserts ∧ ExcludedMiddle ∧
    NotAllInstancesAsserted Asserts) ∧
  (∃ (Proved Asserts : Bool → Prop → Prop),
    ¬ ExcludedMiddleWithheld Proved Asserts ∧ NotAllInstancesAsserted Asserts)

end TruthCore.Logic.ExcludedMiddleAssertionBoundary
