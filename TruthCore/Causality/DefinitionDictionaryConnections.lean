module

public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Isabelle.AFP.GoedelGod
public import TruthCore.Logic.CogitoConcrete

/-!
# Exact dictionary connections for the definition-overlap audit (#1111)

Every comparison below holds at the same supplied carrier, world, predicates
and frame. It is not an identification of differently interpreted dictionaries.
Classification.disjoint is a required proof field; AbstractConcreteDisjoint is
the proposition needed to package independently supplied predicates in that
structure. A proof projection cannot serve as an alias for the proposition
which its constructor requires.
-/

@[expose] public section

namespace TruthCore.Causality.DefinitionDictionaryConnections

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Ontology.ConcreteAbstract (Classification)

/-- Exact inhabited-world, modal existence and classification-package
connections. No population, frame law, classification policy for arbitrary
predicates, exhaustiveness or intended interpretation is established. -/
def Connections : Prop :=
  (∀ (W B : Type) (m : Profile W B) (w : W),
    InhabitedConcreteAt m.ontic m.concrete w ↔ InhabitedAt m w) ∧
  (∀ (W B : Type) (o : Ontic W B) (w : W) (x : B),
    NecessaryAt o w x ↔
      TruthCore.Isabelle.AFP.GoedelGod.Box o.frame (fun v => o.ExistsAt v x) w) ∧
  (∀ (B : Type) (abstract concrete : B → Prop),
    AbstractConcreteDisjoint abstract concrete ↔
      ∃ c : Classification B, c.abstract = abstract ∧ c.concrete = concrete)

end TruthCore.Causality.DefinitionDictionaryConnections
