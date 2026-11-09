module

public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Causality.WorldSourceRegress

@[expose] public section
namespace TruthCore.Causality.OwnerEndpointCalibration
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Causality.WorldSourceRegress

/-- The actualGraph dictionary is literal: its outgoing endpoint is the SAME
Ontic causer. Neither sourcehood, necessity nor exercise-to-power is needed. -/
def DirectLaw : Prop :=
  ∀ (W B : Type) (m : Ontic W B) (concrete : B → Prop)
    (power : W → B → Prop) (w : W),
    OwnerCommitmentAt m concrete power w →
    ∀ x y : Actual m w, (actualGraph m w).edge x y → concrete x.val

/-- The weaker profile has its own power route, independently of the owner's
activity conjunct. This does not identify its concrete predicate with esse. -/
def ProfileLaw : Prop :=
  ∀ (W B : Type) (p : IntendedProfile W B) (w : W) (x y : B),
    p.underlying.ontic.Causes w x y → p.underlying.concrete x

/-- The adopted esse calibration transports the SAME bearer, with no change
of world, concrete predicate or ontic interpretation. Anchors remain required
by the profile, though this pointwise inference only uses concreteIsEsse. -/
def EsseLaw : Prop :=
  ∀ (W B R : Type) (p : EsseIntendedProfile W B R) (w : W) (x y : B),
    p.underlying.ontic.Causes w x y →
    TruthCore.Ontology.ConcreteAbstract.HasEsseInRe p.InAct p.esse x

def toy (edge : Prop) : Ontic Unit Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => edge

/-- Isolated sources may be nonconcrete despite the owner floor; an unrelated
outgoing graph edge cannot replace an Ontic cause; arbitrary concrete labels
need not entail esse. The joint case has genuine outgoing production. These
are finite logical interpretations, not intended anchored ontologies. -/
def Controls : Prop :=
  (OwnerCommitmentAt (toy False) (fun _ => False) (fun _ _ => False) () ∧
    (actualGraph (toy False) ()).Source ⟨(), True.intro⟩ ∧
    ¬ (fun (_ : Unit) => False) ()) ∧
  (OwnerCommitmentAt (toy False) (fun _ => False) (fun _ _ => False) () ∧
    (fun (_ _ : Unit) => True) () () ∧ ¬ (fun (_ : Unit) => False) ()) ∧
  ((fun (_ : Unit) => True) () ∧
    ¬ TruthCore.Ontology.ConcreteAbstract.HasEsseInRe
      (fun (_ _ : Unit) => False) () ()) ∧
  (OwnerCommitmentAt (toy True) (fun _ => True) (fun _ _ => False) () ∧
    (actualGraph (toy True) ()).edge ⟨(), True.intro⟩ ⟨(), True.intro⟩)

/-- Interface and omission certificate serving the necessary-concrete endpoint.
No existence or modal necessity is inferred from concreteness. -/
def Certificate : Prop := DirectLaw ∧ ProfileLaw ∧ EsseLaw ∧ Controls
end TruthCore.Causality.OwnerEndpointCalibration
