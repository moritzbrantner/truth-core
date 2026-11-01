import TruthCore.Logic.Regress
import TruthCore.Mereology.UniversalFusionBoundary
import Mathlib.Order.Max

/-! Analyst minimum extracted from the atomistic argument's structure.
The fixed carrier denotes non-null objects in the chosen interpretation; it
has no added bottom, complete lattice, world, concreteness or modality field.
Source existence and an outgoing source are NOT Rutten's stronger first cause
whose effect is prior to or includes every other caused effect.

AtomicParts is only a weaker consequence of the primary chapter's terminating
proper-part descent, not its full P2. Conditional cover is only containment
from the nonempty caused-simple sum, not unrestricted or unguarded fusion.
The selected edge may be read as complete existence production; no automatic
identification with partial contribution or actual existential ground is made. -/
namespace TruthCore.Causality.AtomisticCausalSource
open TruthCore.Logic.Regress (Graph)
open TruthCore.Mereology.UniversalFusionBoundary (Composite Overlap Covers Fusion)

def ObjectPopulation (B : Type) : Prop := Nonempty B

/-- Standard minimality means absence of proper parts on this non-null domain.
The same object can serve as its own simple part. No descent law is assumed. -/
def AtomicParts (B : Type) [PartialOrder B] : Prop :=
  ∀ x : B, ∃ a, a ≤ x ∧ IsMin a

def CausedSimples {B : Type} [PartialOrder B] (G : Graph B) : Set B :=
  {a | IsMin a ∧ ∃ c, G.edge c a}

/-- Object-valued coverage is required only when THIS family is nonempty.
No no-extra-parts or extensionality clause is needed by the minimum proof. -/
def ConditionalCausedSimpleCover {B : Type} [PartialOrder B] (G : Graph B) : Prop :=
  (CausedSimples G).Nonempty → ∃ u, Covers (CausedSimples G) u

/-- Raw graph counterpart of the existing world-guarded nonoverlap policy.
No world/actuality dictionary is silently supplied for this different scope. -/
def CauseEffectNonoverlap {B : Type} [PartialOrder B] (G : Graph B) : Prop :=
  ∀ c e, G.edge c e → ¬ Overlap c e

def SourceExists {B : Type} (G : Graph B) : Prop := ∃ x, G.Source x

/-- Inclusive incoming-or-outgoing role; an outgoing effect is distinct.
This remains a separate premise from mere object population. -/
def CausalActivity {B : Type} (G : Graph B) : Prop :=
  ∀ x, (∃ c, G.edge c x) ∨ ∃ y, y ≠ x ∧ G.edge x y

def OutgoingSourceExists {B : Type} (G : Graph B) : Prop :=
  ∃ x, G.Source x ∧ ∃ y, y ≠ x ∧ G.edge x y

/-- Full complete-cause framework commitment, unused by the minimum proof. -/
def UniqueCausePerEffect {B : Type} (G : Graph B) : Prop :=
  ∀ e c d, G.edge c e → G.edge d e → c = d

/-- The source P6 says caused PROPER part, not caused simple part.
No termination or causal inheritance is encoded in this interface. -/
def CausedCompositeHasCausedProperPart {B : Type} [PartialOrder B] (G : Graph B) : Prop :=
  ∀ x, (∃ c, G.edge c x) → Composite x → ∃ p, p < x ∧ ∃ c, G.edge c p

namespace Fixture
inductive Object where
  | origin
  | effect
  deriving DecidableEq

/-- Identity parthood on two non-null atoms; NOT the usual linear Bool order. -/
instance : PartialOrder Object where
  le := Eq
  le_refl := Eq.refl
  le_trans := fun _ _ _ hxy hyz => hxy.trans hyz
  le_antisymm := fun _ _ hxy _ => hxy

def graph : Graph Object where
  edge c e := c = .origin ∧ e = .effect
end Fixture

/-- A finite interpretation of all nonlogical minimum inputs and activity,
with a genuine outgoing edge and a full singleton fusion. Additional source
incoming-cause uniqueness and P6 hold; all objects are simple, so P6 is vacuous here.
This is not a certified physical/metaphysical world or the full first cause. -/
def Consistency : Prop :=
  ObjectPopulation Fixture.Object ∧ AtomicParts Fixture.Object ∧
  ConditionalCausedSimpleCover Fixture.graph ∧ CauseEffectNonoverlap Fixture.graph ∧
  CausalActivity Fixture.graph ∧ UniqueCausePerEffect Fixture.graph ∧
  CausedCompositeHasCausedProperPart Fixture.graph ∧
  (∀ x : Fixture.Object, IsMin x) ∧
  CausedSimples Fixture.graph = {Fixture.Object.effect} ∧
  Fusion (CausedSimples Fixture.graph) Fixture.Object.effect ∧
  SourceExists Fixture.graph ∧ OutgoingSourceExists Fixture.graph

end TruthCore.Causality.AtomisticCausalSource
