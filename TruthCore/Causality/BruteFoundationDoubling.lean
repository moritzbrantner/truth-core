import TruthCore.Causality.BruteFoundationBoundary

/-!
# A disjoint-world lifting theorem for contingent first foundations

This is an analyst-constructed modal countermodel schema, not evidence that
a particular metaphysical theory is actually possible.

Starting from ANY nonempty one-world structure with concrete existing
individuals and a causal/grounding relation, duplicate its inventory into
two disjoint possible worlds. Existence is indexed by a rigid pair
(world-tag, base-individual); world-local grounding preserves the source
relation. Both worlds are mutually accessible, but no tagged individual
exists in both.

The construction therefore preserves a whole family of *world-local*
grounding constraints while refuting the proposed derivation of de re
necessary concrete existence from those constraints alone.

World-local constraints cannot by themselves determine which individual
exists across worlds. A substantive cross-world or anti-brute-foundation
principle is needed. This does not refute such a principle.
-/

namespace TruthCore.Causality.BruteFoundationDoubling

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference

/-- Source inventory and relation in one complete history. The carrier is
possibilist; existence and concreteness are independent predicates. -/
structure LocalState (Being : Type) where
  existsAt : Being → Prop
  concrete : Being → Prop
  grounds : Being → Being → Prop

/-- Two mutually accessible copies of the same local causal structure.
The copy-tag belongs to a rigid individual and determines its world
of existence, not a temporal movement or a counterpart relation. -/
def doubled (s : LocalState B) : Profile Bool (Bool × B) where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x.1 = w ∧ s.existsAt x.2
    Causes := fun w y x =>
      y.1 = w ∧ x.1 = w ∧ s.grounds y.2 x.2
  }
  concrete := fun x => s.concrete x.2
  grounds := fun w y x =>
    y.1 = w ∧ x.1 = w ∧ s.grounds y.2 x.2

/-- If the original local inventory is concretely inhabited, so are
both possible histories of its doubled interpretation. -/
theorem doublesPopulation (s : LocalState B)
    (hPop : ∃ x, s.concrete x ∧ s.existsAt x) :
    ∀ w, InhabitedAt (doubled s) w := by
  intro w
  rcases hPop with ⟨x, hc, he⟩
  exact ⟨(w, x), hc, ⟨rfl, he⟩⟩

/-- No rigid individual exists concretely and necessarily in the
two-world lift, even if the local source structure was populated. -/
theorem doubledHasNoNecessary (s : LocalState B) :
    ¬ NecessaryConcreteAt (doubled s) false := by
  intro h
  rcases h with ⟨x, _, hx, hNec⟩
  have hFalse : x.1 = false := hx.1
  have hTrue : x.1 = true := (hNec true True.intro).1
  rw [hFalse] at hTrue
  cases hTrue

/-- All actual-world causal/grounding edges are copied from the
source relation, with endpoints tagged for the selected world. -/
theorem copiedEdgeIff (s : LocalState B) (w : Bool) (y x : B) :
    (doubled s).grounds w (w, y) (w, x) ↔ s.grounds y x := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨rfl, rfl, h⟩

/-- Existential soundness and distinct causal endpoints are preserved
from the source structure to all world-local doubled edges. -/
theorem doublesGroundSound (s : LocalState B)
    (hSound : ∀ y x, s.grounds y x →
      s.existsAt y ∧ s.existsAt x ∧ y ≠ x) :
    ∀ w y x, (doubled s).grounds w y x →
      (doubled s).ontic.ExistsAt w y ∧
      (doubled s).ontic.ExistsAt w x ∧
      y ≠ x := by
  intro w y x h
  rcases h with ⟨hyTag, hxTag, hLink⟩
  rcases hSound y.2 x.2 hLink with ⟨hyEx, hxEx, hDistinct⟩
  refine ⟨⟨hyTag, hyEx⟩, ⟨hxTag, hxEx⟩, ?_⟩
  intro hEqual
  apply hDistinct
  exact congrArg Prod.snd hEqual

/-- A fixed source relation's well-foundedness is preserved when
its edges are copied within each world, with no cross-world edges.
The proof lifts accessibility certificates by induction. -/
theorem doublesWellFounded (s : LocalState B)
    (hWF : WellFounded s.grounds) :
    ∀ w, WellFounded ((doubled s).grounds w) := by
  intro w
  have liftAcc : ∀ b : B, Acc s.grounds b →
      Acc ((doubled s).grounds w) (w, b) := by
    intro b hb
    induction hb with
    | intro b _ ih =>
      apply Acc.intro
      intro y hEdge
      rcases hEdge with ⟨hyTag, _, hBase⟩
      have hyEq : y = (w, y.2) := Prod.ext hyTag rfl
      rw [hyEq]
      exact ih y.2 hBase
  refine ⟨?_⟩
  intro ⟨tag, b⟩
  by_cases ht : tag = w
  · subst tag
    exact liftAcc b (hWF.apply b)
  · apply Acc.intro
    intro y hy
    exact False.elim (ht hy.2.1)

/-- An independently specified noninitial predicate distinguishes
ordinary caused members from the initial roots. It is not defined in
terms of the existence of a predecessor, avoiding a tautological law. -/
def NoninitialCovered (s : LocalState B) (noninitial : B → Prop) : Prop :=
  ∀ x, s.concrete x → s.existsAt x → noninitial x →
    ∃ y, s.concrete y ∧ s.existsAt y ∧ s.grounds y x

/-- Every world in the lift inherits the source's law requiring causes
for all noninitial existing concreta, while saying nothing about roots. -/
theorem doublesNoninitialCoverage
    (s : LocalState B) (noninitial : B → Prop)
    (hLaw : NoninitialCovered s noninitial) :
    ∀ w x, (doubled s).concrete x →
      (doubled s).ontic.ExistsAt w x →
      noninitial x.2 →
      ∃ y, (doubled s).concrete y ∧
        (doubled s).ontic.ExistsAt w y ∧
        (doubled s).grounds w y x := by
  intro w x hc hx hn
  rcases hLaw x.2 hc hx.2 hn with ⟨y, hyConcrete, hyExists, hyLink⟩
  refine ⟨(w, y), hyConcrete, ⟨rfl, hyExists⟩, ?_⟩
  exact ⟨rfl, hx.1, hyLink⟩

/-- Schema-level countermodel: for every locally populated and well-founded
grounding structure, there is a two-world, universally accessible theory
with exactly the same local structure in both worlds, but without a single
rigid necessary concrete individual. Thus the local assumptions alone
cannot entail de re necessary existence. -/
theorem arbitraryWorldLocalGroundingDoesNotForceNecessary
    (s : LocalState B)
    (hPop : ∃ x, s.concrete x ∧ s.existsAt x)
    (hWF : WellFounded s.grounds) :
    (∀ w v, (doubled s).ontic.frame.access w v) ∧
      (∀ w, InhabitedAt (doubled s) w) ∧
      (∀ w, WellFounded ((doubled s).grounds w)) ∧
      ¬ NecessaryConcreteAt (doubled s) false := by
  exact ⟨(fun _ _ => True.intro), doublesPopulation s hPop,
    doublesWellFounded s hWF, doubledHasNoNecessary s⟩

end TruthCore.Causality.BruteFoundationDoubling
