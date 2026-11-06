module

public import TruthCore.Logic.CogitoConcrete
public import TruthCore.Causality.CogitoNecessaryConcrete
public import TruthCore.Causality.ExistenceActuality
public import TruthCore.Ontology.ConcreteAbstract

/-!
# Cogito in the adopted esse sense of concrete (#1113)

Owner decision on #1113 (2026-11-06): an individual existing in re is in act
of esse, so every real existent is concrete. Concreteness adds no restriction
beyond real existence in this interpretation. The generic `Ontic` and
`BruteFoundationBoundary.Profile` signatures and their frozen results remain
unchanged: their arbitrary predicate assignments do not assert this contract.

`profile` fixes concrete to `HasEsseInRe InAct esse`, retaining the SAME
ontic existence and grounding relations. `ExistingInActAt` is the explicit,
selected-world contract for reading that existence as existence in re. It is
not an extra floor approval and is not proved for arbitrary `Ontic` assignments.
The reverse implication, existence from esse, is not needed and is not asserted.

The old concrete-bearer omission model permits an existing but nonconcrete
bearer precisely because it has no such contract; it is not a countermodel to
the adopted interpretation. Occurrence-to-existence, occurrence itself, the
bearer principle, grounding premises and excluded middle remain separate.
-/

@[expose] public section

namespace TruthCore.Logic.CogitoEsse

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.ConcreteAbstract (HasEsseInRe)

/-- Specialize only the concrete predicate to the adopted esse criterion.
No causal or grounding edge, existence assignment or modal frame is changed.
InAct and esse retain the selected source-profile interpretation. -/
def profile {W B R : Type} (o : Ontic W B) (grounds : W → B → B → Prop)
    (InAct : B → R → Prop) (esse : R) : Profile W B where
  ontic := o
  concrete := HasEsseInRe InAct esse
  grounds := grounds

/-- Every represented existent at the selected world is concrete in the esse
sense. This conclusion does not classify nonexisting candidates, exclude
abstract candidates from the carrier, or equate concrete with spatiotemporal. -/
def EveryExistentConcreteAt {W B : Type} (o : Ontic W B)
    (concrete : B → Prop) (w : W) : Prop :=
  ∀ x, o.ExistsAt w x → concrete x

end TruthCore.Logic.CogitoEsse
