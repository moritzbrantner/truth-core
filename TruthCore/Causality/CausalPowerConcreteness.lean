module

public import TruthCore.Causality.GroundingIdentityProfile

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

/-- Required interpretation contract for intended P2-B/P3 investigations.
The old ontic/grounding signature is preserved exactly. Disjointness and the
thin exercise-to-power dictionary fix the intended senses; power-to-concrete
is the owner's framework commitment. None is proved for arbitrary predicates.
Power possession and causal exercise require actual endpoints. No
grounding-to-causation or well-foundedness is included. -/
structure IntendedProfile (W B : Type) where
  underlying : BruteFoundationBoundary.Profile W B
  abstract : B → Prop
  hasCausalPower : W → B → Prop
  disjoint : AbstractConcreteDisjoint abstract underlying.concrete
  powerExists : ∀ w x, hasCausalPower w x → underlying.ontic.ExistsAt w x
  causalEndpoints : ∀ w x y, underlying.ontic.Causes w x y →
    underlying.ontic.ExistsAt w x ∧ underlying.ontic.ExistsAt w y
  exerciseHasPower : ∀ w x y,
    underlying.ontic.Causes w x y → hasCausalPower w x
  powerConcrete : ∀ w,
    PowerRequiresConcreteAt underlying.concrete hasCausalPower w

/-- Intended P2-B entry point: the semantic contract is required, while
existence of actual concrete grounds remains the old, separate open premise. -/
def P2At {W B : Type} (p : IntendedProfile W B) (w : W) : Prop :=
  BruteFoundationBoundary.EveryContingentGroundedAt p.underlying w

/-- Intended P3 entry point: EXACTLY the same underlying grounding relation
as P2At, with the interpretation contract required but WF not assumed by it. -/
def P3At {W B : Type} (p : IntendedProfile W B) (w : W) : Prop :=
  WellFounded (p.underlying.grounds w)

/-- Adapt the EXISTING doubled root-child profile without changing any old
field. Thin power belongs to the actually existing source-role roots; it is
not defined by concreteness or by currently having an outgoing edge. The old
inventory contains no abstract members, not a newly invented abstract roster. -/
def doubledExample : IntendedProfile Bool (Bool × (Bool × Bool)) where
  underlying := BruteFoundationDoubling.doubled BruteFoundationDoubling.exampleSource
  abstract := fun _ => False  -- category-constant: intended (old inventory has no abstract candidate; meets the #1094 contract but supplies no Anchors, so not an intended interpretation under #1103)
  hasCausalPower := fun w x =>
    (BruteFoundationDoubling.doubled BruteFoundationDoubling.exampleSource).ontic.ExistsAt w x ∧
      x.2.2 = false
  disjoint := fun _ h => h.elim
  powerExists := fun _ _ h => h.1
  causalEndpoints := fun w x y h =>
    let hs := BruteFoundationDoubling.doublesGroundSound
      BruteFoundationDoubling.exampleSource
      BruteFoundationDoubling.exampleSourceConditions.2.2.1 w x y h
    ⟨hs.1, hs.2.1⟩
  exerciseHasPower := fun w x y h =>
    ⟨(BruteFoundationDoubling.doublesGroundSound
      BruteFoundationDoubling.exampleSource
      BruteFoundationDoubling.exampleSourceConditions.2.2.1 w x y h).1,
      h.2.2.2.2.1⟩
  powerConcrete := fun _ _ _ => True.intro

/-- Adapt the EXISTING rigid companion using its literal old profile. Presence,
root-role power and the original causal/grounding edges are preserved at the
same worlds; no modal assignment or identity convention is changed. -/
def rigidExample : IntendedProfile Bool (Bool × (Bool × Bool)) where
  underlying := GroundingIdentityProfile.rigid BruteFoundationDoubling.exampleSource
  abstract := fun _ => False  -- category-constant: intended (old inventory has no abstract candidate; meets the #1094 contract but supplies no Anchors, so not an intended interpretation under #1103)
  hasCausalPower := fun w x =>
    (GroundingIdentityProfile.rigid BruteFoundationDoubling.exampleSource).ontic.ExistsAt w x ∧
      x.2.2 = false
  disjoint := fun _ h => h.elim
  powerExists := fun _ _ h => h.1
  causalEndpoints := fun _ x y h =>
    let hs := BruteFoundationDoubling.doublesGroundSound
      BruteFoundationDoubling.exampleSource
      BruteFoundationDoubling.exampleSourceConditions.2.2.1 false x y h
    ⟨hs.1, hs.2.1⟩
  exerciseHasPower := fun _ x y h =>
    ⟨(BruteFoundationDoubling.doublesGroundSound
      BruteFoundationDoubling.exampleSource
      BruteFoundationDoubling.exampleSourceConditions.2.2.1 false x y h).1,
      h.2.2.2.2.1⟩
  powerConcrete := fun _ _ _ => True.intro

end TruthCore.Causality.CausalPowerConcreteness
