import TruthCore.Greek.Plato.Forms
import TruthCore.Greek.Plato.Timaeus

/-!
Scoped, independently challengeable reading bundles, not historical identities.
The classificatory projection intentionally leaves explanation open. The Phaedo
causal synthesis adds an explanatory relation without determining its mechanism.
The exemplar synthesis adds model/copy commitments; it does not equate imitation,
symmetric likeness, participation and efficient causation.

These are cross-dialogue research bundles. Each component has its own source
reading; none is attributed wholesale to every dialogue. Self-predication has two
optional variants. Neither includes an unrestricted one-over-many rule applying
to Forms themselves. Issues #258–#260 investigate further assumptions and replies.
No bundle defines a verdict on Catholicism or any other theory.
-/
namespace TruthCore.Comparison.PlatonicForms
open TruthCore.Greek.Plato.Forms

universe u v
variable {Entity : Type u} {Quality : Type v}

def Classificatory (s : Vocabulary Entity Quality) : Prop :=
  PropertyInstances s ∧ OneOverMany s ∧ UniqueForms s ∧
  ParticipationPredication s ∧ Nonidentity s

def SeparatedCausal (s : Vocabulary Entity Quality) : Prop :=
  PropertyInstances s ∧ OneOverMany s ∧ UniqueForms s ∧
  ParticipationPredication s ∧ Nonidentity s ∧ OntologicalSeparation s ∧
  ExplanatoryParticipation s

def Exemplar (s : Vocabulary Entity Quality) : Prop :=
  PropertyInstances s ∧ OneOverMany s ∧ UniqueForms s ∧
  ParticipationPredication s ∧ Nonidentity s ∧ OntologicalSeparation s ∧
  ExplanatoryParticipation s ∧ ExemplarParticipation s ∧ IntelligibleForms s

def SelfPredicating (s : Vocabulary Entity Quality) : Prop :=
  PropertyInstances s ∧ OneOverMany s ∧ UniqueForms s ∧
  ParticipationPredication s ∧ Nonidentity s ∧ OntologicalSeparation s ∧
  ExplanatoryParticipation s ∧ ExemplarParticipation s ∧ IntelligibleForms s ∧
  UniformSelfPredication s

def Essential (s : Vocabulary Entity Quality) : Prop :=
  PropertyInstances s ∧ OneOverMany s ∧ UniqueForms s ∧
  ParticipationPredication s ∧ Nonidentity s ∧ OntologicalSeparation s ∧
  ExplanatoryParticipation s ∧ ExemplarParticipation s ∧ IntelligibleForms s ∧
  EssentialCharacterization s

/-- A concrete three-entity, one-quality model of the self-predicative synthesis.
This tests only the encoded commitments, not the reality of explanatory powers. -/
def SelfPredicatingConsistent : Prop :=
  ∃ s : Vocabulary (Fin 3) Unit, SelfPredicating s

end TruthCore.Comparison.PlatonicForms
