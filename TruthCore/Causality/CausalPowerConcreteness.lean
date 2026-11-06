module

public import TruthCore.German.Kant.CosmologicalInference

/-!
# Owner-proposed causal-power concreteness premise

Framework input for #545, not a theorem or a source attribution. Concreteness
and causal power are independently supplied predicates; neither is defined in
terms of the other. Power means a capacity to cause, which need not be exercised
at the selected world. Concreteness does not mean materiality or spatial location.
See `docs/notes/causal-power-concreteness.md` for scope and remaining bridges.
-/

@[expose] public section

namespace TruthCore.Causality.CausalPowerConcreteness

open TruthCore.German.Kant.CosmologicalInference

/-- At the selected world, anything with causal power is concrete. This defines
an openly proposed premise, not concreteness itself and not a proof of its truth.
No converse, actual exercise, existence implication or necessity is included. -/
def PowerRequiresConcreteAt {W B : Type}
    (concrete : B → Prop) (hasCausalPower : W → B → Prop) (w : W) : Prop :=
  ∀ x, hasCausalPower w x → concrete x

/-- Independent direct-exercise clause: every outgoing cause at w is concrete.
It does not infer capacity from exercise or prohibit incoming causation. -/
def CausersRequireConcreteAt {W B : Type}
    (o : Ontic W B) (concrete : B → Prop) (w : W) : Prop :=
  ∀ x y, o.Causes w x y → concrete x

/-- The owner's capacity and activity clauses, retained as independent inputs.
This proposition is a working commitment, not a theorem proving either clause. -/
def OwnerCommitmentAt {W B : Type}
    (o : Ontic W B) (concrete : B → Prop)
    (hasCausalPower : W → B → Prop) (w : W) : Prop :=
  PowerRequiresConcreteAt concrete hasCausalPower w ∧
    CausersRequireConcreteAt o concrete w

/-- Separate classification policy needed to exclude abstract causal powers.
Abstractness is supplied independently, not defined as nonconcreteness. This
policy alone says nothing about powers, causation or being caused. -/
def AbstractConcreteDisjoint {B : Type}
    (abstract concrete : B → Prop) : Prop :=
  ∀ x, abstract x → ¬ concrete x

end TruthCore.Causality.CausalPowerConcreteness
