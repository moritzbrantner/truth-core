module

public import TruthCore.Ontology.Naturalism
public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Case.Catholicism.StageTwo

/-!
# Naturalism, mereological dictionaries and the spacetime whole (#1109)

The part, occupant and relational senses remain distinct. The God contrast
uses the existing Case.Catholicism.RemoteFromAll and IsSimple predicates on
one shared ComponentOf/Composite dictionary. Neither an arbitrary Frame.partOf
relation nor the Case dictionary automatically connects a proper spacetime
part to composition. Two explicit selected-world bridges supply those steps.

The result concerns existence of a being with specified necessary properties,
not truth of a God-naming implication. There is no converse from the nominal
God description to every being called God. No causal, grounding, floor or
physical-to-spatiotemporal bridge is introduced.
-/

@[expose] public section

namespace TruthCore.Ontology.NaturalismContrasts

open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Case.Catholicism (RemoteFromAll IsSimple)

/-- Weak selected-world bridge: an existing proper part of this spacetime
whole is a component of that same whole. Mere membership, spatial occupation
and componenthood are not identified globally. -/
def ExistingProperPartsAreComponents {W B : Type} (o : Ontic W B) (F : Frame B)
    (ComponentOf : B → B → Prop) (w : W) : Prop :=
  ∀ x, o.ExistsAt w x → PartOfSpacetime F x → x ≠ F.whole → ComponentOf x F.whole

/-- Weak selected-world bridge: an existing component distinct from this
whole makes that same whole composite. This is not the converse of the
existing statement that every composite has a component. -/
def ExistingComponentsMakeWholeComposite {W B : Type} (o : Ontic W B) (F : Frame B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W) : Prop :=
  ∀ x, o.ExistsAt w x → ComponentOf x F.whole → x ≠ F.whole → Composite F.whole

/-- There are two numerically distinct actual candidates at the selected world. -/
def TwoExist {W B : Type} (o : Ontic W B) (w : W) : Prop :=
  ∃ x y, o.ExistsAt w x ∧ o.ExistsAt w y ∧ x ≠ y

/-- An existing candidate is both simple and remote under the existing Case
predicates, interpreted with this shared dictionary. -/
def ExistingSimpleRemote {W B : Type} (o : Ontic W B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W) : Prop :=
  ∃ g, o.ExistsAt w g ∧ IsSimple Composite g ∧ RemoteFromAll ComponentOf g

/-- The constructive population constraint: such a being is incompatible
with a distinct pair of existents. It does not claim positive equality of all
candidates or infer existence of the spacetime whole. -/
def RemoteSimplePopulationConstraint {W B : Type} (o : Ontic W B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W) : Prop :=
  ExistingSimpleRemote o ComponentOf Composite w → ¬ TwoExist o w

/-- No existent has both specified Case properties. This is not the negation
of a nominal God-naming implication. -/
def NoExistingSimpleRemote {W B : Type} (o : Ontic W B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W) : Prop :=
  ¬ ExistingSimpleRemote o ComponentOf Composite w

/-- The selected whole occupies no region, in the occupant sense only. -/
def WholeUnlocated {B : Type} (F : Frame B) : Prop := ¬ Located F F.whole

/-- The selected whole does not exist at this world. This does not assert a
complete relationalist theory of spacetime. -/
def WholeAbsent {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ¬ o.ExistsAt w F.whole

/-- A configuration gluing existing dictionaries; none of its fields is an
axiom and no relation is identified by this record alone. -/
structure Scenario where
  World : Type
  Being : Type
  o : Ontic World Being
  F : Frame Being
  ComponentOf : Being → Being → Prop
  Composite : Being → Prop
  w : World

/-- The exact joint hypotheses of the part-naturalism exclusion, for a
configuration. Each is still an explicit open framework commitment. -/
def PartBackground (s : Scenario) : Prop :=
  ExistenceNaturalism s.o (PartOfSpacetime s.F) s.w ∧
    ExistingProperPartsAreComponents s.o s.F s.ComponentOf s.w ∧
    ExistingComponentsMakeWholeComposite s.o s.F s.ComponentOf s.Composite s.w ∧
    TwoExist s.o s.w

/-- Populated controls retain every advertised field in their exported type:
(1) the full background is satisfiable; (2) without a second existent the
existing, located, self-part whole can be simple and remote; (3)-(5) each
remaining premise can fail while the other premises and a simple remote
existent hold; (6) occupant naturalism can keep existing located candidates
while the unlocated whole is absent. These are scoped interpretations, not
full metaphysical worldviews or claims about actual God, space or parts. -/
def ContrastControls : Prop :=
  (∃ s : Scenario, PartBackground s ∧
    NoExistingSimpleRemote s.o s.ComponentOf s.Composite s.w) ∧
  (∃ s : Scenario,
    ExistenceNaturalism s.o (PartOfSpacetime s.F) s.w ∧
    ExistingProperPartsAreComponents s.o s.F s.ComponentOf s.w ∧
    ExistingComponentsMakeWholeComposite s.o s.F s.ComponentOf s.Composite s.w ∧
    ¬ TwoExist s.o s.w ∧ ExistingSimpleRemote s.o s.ComponentOf s.Composite s.w ∧
    s.o.ExistsAt s.w s.F.whole ∧ Located s.F s.F.whole ∧
    PartOfSpacetime s.F s.F.whole ∧
    ExistenceNaturalism s.o (Located s.F) s.w) ∧
  (∃ s : Scenario,
    ExistenceNaturalism s.o (PartOfSpacetime s.F) s.w ∧
    ExistingProperPartsAreComponents s.o s.F s.ComponentOf s.w ∧
    ¬ ExistingComponentsMakeWholeComposite s.o s.F s.ComponentOf s.Composite s.w ∧
    TwoExist s.o s.w ∧ ExistingSimpleRemote s.o s.ComponentOf s.Composite s.w) ∧
  (∃ s : Scenario,
    ExistenceNaturalism s.o (PartOfSpacetime s.F) s.w ∧
    ¬ ExistingProperPartsAreComponents s.o s.F s.ComponentOf s.w ∧
    ExistingComponentsMakeWholeComposite s.o s.F s.ComponentOf s.Composite s.w ∧
    TwoExist s.o s.w ∧ ExistingSimpleRemote s.o s.ComponentOf s.Composite s.w) ∧
  (∃ s : Scenario,
    ¬ ExistenceNaturalism s.o (PartOfSpacetime s.F) s.w ∧
    ExistenceNaturalism s.o (Located s.F) s.w ∧
    ExistingProperPartsAreComponents s.o s.F s.ComponentOf s.w ∧
    ExistingComponentsMakeWholeComposite s.o s.F s.ComponentOf s.Composite s.w ∧
    TwoExist s.o s.w ∧ ExistingSimpleRemote s.o s.ComponentOf s.Composite s.w) ∧
  (∃ s : Scenario,
    ExistenceNaturalism s.o (Located s.F) s.w ∧ WholeUnlocated s.F ∧
    WholeAbsent s.o s.F s.w ∧
    ∃ x, s.o.ExistsAt s.w x ∧ x ≠ s.F.whole ∧ Located s.F x)

end TruthCore.Ontology.NaturalismContrasts
