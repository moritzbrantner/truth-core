import TruthCore.Causality.AtomisticCausalSource
import Mathlib.Order.WellFounded

/-! Conditional extension of the analyst minimum. Proper-part descent is
well-founded; causal descent is NOT assumed well-founded. Priority means
asymmetric existential requirement in Rutten chapter VI, fn174, rather than
Aquinas's act/potency priority. Independent applicability remains open.
The endpoint concerns the CAUSE N, not the cover M's universal priority. -/
namespace TruthCore.Causality.AtomisticUniversalCausePriority
open TruthCore.Logic.Regress (Graph)
open TruthCore.Mereology.UniversalFusionBoundary (Covers)
open TruthCore.Causality.AtomisticCausalSource

/-- Source P2's terminating proper-part descent (p127, defended pp129–131).
This is stronger than merely having a simple part. -/
def ProperPartWF (B : Type) [PartialOrder B] : Prop :=
  WellFounded (fun p x : B => p < x)

def EveryCausedObjectHasCausedSimplePart {B : Type} [PartialOrder B]
    (G : Graph B) : Prop :=
  ∀ x, (∃ c, G.edge c x) → ∃ a, a ≤ x ∧ IsMin a ∧ ∃ c, G.edge c a

/-- Source p135 explicitly asserts priority to each effect-part, not just
priority to the effect. This policy is separate from proper-part priority. -/
def CausePriorToEffectParts {B : Type} [PartialOrder B]
    (G : Graph B) (Prior : B → B → Prop) : Prop :=
  ∀ c e, G.edge c e → ∀ p, p ≤ e → Prior c p

/-- fn174's part-priority read for PROPER parts: including improper parthood
would impose self-priority, contrary to its asserted strictness. -/
def ProperPartsPrior {B : Type} [PartialOrder B] (Prior : B → B → Prop) : Prop :=
  ∀ p e, p < e → Prior p e

def TransitiveExistentialPriority {B : Type} (Prior : B → B → Prop) : Prop :=
  ∀ x y z, Prior x y → Prior y z → Prior x z

/-- M covers caused simples; no full fusion, priority of M, unique first cause,
necessity, or identification of edge with every existential ground follows. -/
def UniversalCausePriority {B : Type} [PartialOrder B]
    (G : Graph B) (Prior : B → B → Prop) : Prop :=
  ∃ N M, G.Source N ∧ G.edge N M ∧ Covers (CausedSimples G) M ∧
    ∀ x, (∃ c, G.edge c x) → Prior N x

namespace Fixture
abbrev prior := AtomisticCausalSource.Fixture.graph.edge
end Fixture

/-- Extends the old nonvacuous two-atom identity-parthood model. Strict
parthood, and hence P6 and proper-part priority, are vacuous here. The causal
edge and cause-to-part priority are nonvacuous; this is no reality claim. -/
def Consistency : Prop :=
  AtomisticCausalSource.Consistency ∧
  ProperPartWF AtomisticCausalSource.Fixture.Object ∧
  CausePriorToEffectParts AtomisticCausalSource.Fixture.graph Fixture.prior ∧
  ProperPartsPrior Fixture.prior ∧
  TransitiveExistentialPriority Fixture.prior ∧
  (∀ x, ¬ Fixture.prior x x) ∧
  UniversalCausePriority AtomisticCausalSource.Fixture.graph Fixture.prior

end TruthCore.Causality.AtomisticUniversalCausePriority
