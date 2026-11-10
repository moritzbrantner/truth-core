module

public import TruthCore.Logic.ExcludedMiddle
public import Mathlib.Order.Fin.Basic
public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Causality.WorldSourceRegress

/-! Full effect-based first cause, on an arbitrary carrier and fixed inclusion
order. `requirement x y` is primitive existential requirement: y requires x to
exist. It is not implication between truth values of existence at one world,
temporal precedence, causal production, or overlap. Applicability remains OPEN.
Graph edges are interpreted as complete existence production, with their
independent semantic burdens retained. No uniqueness, transitivity, acyclicity
or reality of either primitive is built into this definition. -/

@[expose] public section
namespace TruthCore.Causality.FullFirstCause
open TruthCore.Logic.Regress (Graph)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.CausalPowerConcreteness

/-- x is required for y, while y is not required for x. In particular this
relation is asymmetric even when the underlying requirement is reciprocal. -/
def Prior {B : Type} (requirement : B → B → Prop) (x y : B) : Prop :=
  requirement x y ∧ ¬ requirement y x

/-- The SAME effect M is selected before quantifying over every other caused
effect e. Inclusion is e ≤ M (M includes e), not overlap or M ≤ e.
No assumption says that N itself is prior to every effect. -/
def FirstCause {B : Type} [PartialOrder B] (G : Graph B)
    (requirement : B → B → Prop) (N : B) : Prop :=
  G.Source N ∧ ∃ M, G.edge N M ∧
    ∀ e, (∃ c, G.edge c e) → e ≠ M → Prior requirement M e ∨ e ≤ M

def ExistsFirstCause {B : Type} [PartialOrder B] (G : Graph B)
    (requirement : B → B → Prop) : Prop := ∃ N, FirstCause G requirement N

/-- OPEN dictionary: complete production on actual nodes agrees exactly with
this Ontic's causation at this world, in BOTH directions. The reverse direction
is needed for uncausedness; the forward direction for outgoing concreteness.
It does not follow from calling a relation causal or complete. -/
def ActualProductionDictionary {W B : Type} (m : Ontic W B) (w : W)
    (G : Graph (Actual m w)) : Prop :=
  ∀ c e, G.edge c e ↔ m.Causes w c.val e.val

namespace Fixture
inductive Object where
  | origin | effect | other
  deriving DecidableEq

/-- Identity inclusion on three atoms. No distinct effects include one another. -/
instance : PartialOrder Object where
  le := Eq
  le_refl := Eq.refl
  le_trans := fun _ _ _ hxy hyz => hxy.trans hyz
  le_antisymm := fun _ _ hxy _ => hxy

/-- One complete cause with TWO distinct effects. -/
def graph : Graph Object where
  edge c e := c = .origin ∧ (e = .effect ∨ e = .other)

/-- The selected effect is asymmetrically required for the OTHER effect. -/
def effectRequirement (x y : Object) : Prop := x = .effect ∧ y = .other

/-- Confusing priority of N with priority of M fails in this interpretation. -/
def causeRequirement (x y : Object) : Prop :=
  x = .origin ∧ (y = .effect ∨ y = .other)
/-- A separate model with genuine proper inclusion: effect 2 includes effect
1. Standard Fin order is interpreted as this stipulated inclusion, not time. -/
def inclusionGraph : Graph (Fin 3) where
  edge c e := c = 0 ∧ (e = 1 ∨ e = 2)
end Fixture

/-- Nonvacuous full instance, source/outgoing separator, and explicit rejection
of cause-priority as a substitute for effect-priority. Those comparisons use
one fixed graph, carrier and inclusion, with a DISTINCT other caused effect.
A separate proper-inclusion model tests the inclusion horn. These are formal
interpretations, not certified real production examples. -/
def Comparisons : Prop :=
  FirstCause Fixture.graph Fixture.effectRequirement .origin ∧
  Fixture.graph.edge .origin .other ∧ Fixture.Object.other ≠ .effect ∧
  (Fixture.graph.Source .origin ∧ ∃ M, Fixture.graph.edge .origin M) ∧
  (¬ ExistsFirstCause Fixture.graph (fun _ _ => False)) ∧
  (∀ e, (∃ c, Fixture.graph.edge c e) → Prior Fixture.causeRequirement .origin e) ∧
  (¬ ExistsFirstCause Fixture.graph Fixture.causeRequirement) ∧
  FirstCause Fixture.inclusionGraph (fun _ _ => False) 0 ∧
  Fixture.inclusionGraph.edge 0 1 ∧ Fixture.inclusionGraph.edge 0 2 ∧
  (1 : Fin 3) < 2

end TruthCore.Causality.FullFirstCause
