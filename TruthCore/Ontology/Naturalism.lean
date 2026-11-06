module

public import TruthCore.Ontology.Spatiotemporal

/-!
# Naturalism as a complete worldview: the ontological variants (#1109)

Each variant is a schema in a supplied **thesis predicate** `P : B → Prop`, so
that a proponent's own predicate is kept rather than replaced:

* spatiotemporal naturalism takes `P` to be one of the senses of
  `Spatiotemporal` (`Located F`, `Related F` or `PartOfSpacetime F`);
* Papineau's physicalism takes `P` to be "physical" in his sense
  (`DEF-PAPINEAU-PHYSICAL`). Passing from "physical" to "spatiotemporal" is a
  bridge that no source here states.

The variants, all at a selected world `w`, with existence the world-relative
`Ontic.ExistsAt`:

* **N1** `ExistenceNaturalism`: everything that exists is `P` (Armstrong's
  naturalism, as Murphy 2021 reports it: nothing exists apart from
  spatio-temporal objects).
* **N2** `ConcreteNaturalism`: everything that exists and is concrete is `P`.
  An analyst formulation, attribution deferred. N1 entails N2 with no premise
  (`N1-ENTAILS-N2`); under the owner's #1113 bridge, on which whatever exists in
  re is concrete, the two coincide for existents in re.
* **N3** `CausalPowerNaturalism`: everything with causal power is `P`
  (Papineau, *The Rise of Physicalism*, p.12, with `P` = physical).
* **N3i** `InteractionNaturalism`: whatever causes something that is `P` is
  itself `P` (Papineau p.11: "everything that interacts causally with the
  physical world is physical"). Neither N3 nor N3i entails the other without
  the exercise-to-power reading.

The methodological variants (Sellars' *scientia mensura*, Quine's naturalized
epistemology) are recorded as untyped statements: typing them needs vocabulary
for what science describes and explains, which the corpus does not have.
-/

@[expose] public section

namespace TruthCore.Ontology.Naturalism

open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-- N1: everything that exists at `w` satisfies the thesis predicate `P`. -/
def ExistenceNaturalism {W B : Type} (o : Ontic W B) (P : B → Prop) (w : W) : Prop :=
  ∀ x, o.ExistsAt w x → P x

/-- N2: everything that exists at `w` and is concrete satisfies `P`. -/
def ConcreteNaturalism {W B : Type} (o : Ontic W B) (concrete P : B → Prop) (w : W) :
    Prop :=
  ∀ x, o.ExistsAt w x → concrete x → P x

/-- N3: everything with causal power at `w` satisfies `P`. -/
def CausalPowerNaturalism {W B : Type} (hasCausalPower : W → B → Prop) (P : B → Prop)
    (w : W) : Prop :=
  ∀ x, hasCausalPower w x → P x

/-- N3i: whatever causes, at `w`, something that satisfies `P` satisfies `P`. -/
def InteractionNaturalism {W B : Type} (o : Ontic W B) (P : B → Prop) (w : W) : Prop :=
  ∀ x y, o.Causes w x y → P y → P x

/-- The concrete rival of N2: some existing concrete thing does not satisfy `P`.
With `P` a spatiotemporal sense, this is the Thomist combination
`Spatiotemporal.SomeConcreteNotSpatiotemporal`. -/
theorem concreteNaturalism_excludes {W B : Type} {o : Ontic W B} {concrete P : B → Prop}
    {w : W} (h : ConcreteNaturalism o concrete P w) :
    ¬ Spatiotemporal.SomeConcreteNotSpatiotemporal o concrete P w :=
  fun ⟨x, hx, hc, hnp⟩ => hnp (h x hx hc)

end TruthCore.Ontology.Naturalism
