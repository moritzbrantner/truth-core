module

public import TruthCore.German.Kant.CosmologicalInference

/-!
# Concrete and abstract: the shared vocabulary (#1103)

The corpus took `concrete : B → Prop` as a free parameter in dozens of files,
with no shared meaning, and several models set it to `True`. This module gives
the distinction one typed home.

* `Classification B` is the criterion-neutral interface: independently supplied
  `concrete` and `abstract` predicates with REQUIRED disjointness. It does not
  require exhaustiveness (`Exhaustive`), because the rival criteria need not be
  exhaustive. For the adopted esse sense, exhaustiveness is derived from
  excluded middle and disjointness from non-contradiction (`EsseDichotomy`).
* The **adopted sense** (owner decision on #1103, 2026-11-06) is the esse
  criterion. A candidate is concrete when it has its own esse *in re*, read with
  the shared Aquinas vocabulary as `InAct x esse` (`DEF-ESSE`). It is abstract
  when it lacks esse in re (`¬ InAct x esse`), having at most esse in the
  intellect, as the number 2 does. Abstract is the contradictory of concrete, so
  there are no borderline cases (owner, 2026-11-06). The source readings are De ente c.1–2 (being "quod aliquid
  in re ponit" versus propositional truth; a nature's double esse, "unum in
  singularibus et aliud in anima") and ST I q.85 a.1 ad 1–2 (mathematicals are
  abstracted by the intellect, not abstract "secundum rem"). Aquinas does not
  use the modern word "concrete". Identifying the modern contrast with this one
  is the owner's stipulation, not an attribution. What esse in re further
  requires is left to the metaphysical questions downstream.
* The rival criteria are sibling senses under `DISAMB-CONCRETE-ABSTRACT-CRITERIA`:
  causal efficacy, spatiotemporal occupation, Frege's "non-mental and
  non-physical" and abstraction (SEP "Abstract Objects", §§3–6). None of them
  defines the adopted sense. In particular, causal power does NOT define
  concreteness, so "only concrete things cause" stays a substantive proposition.
* `Anchors` are paradigm cases that every intended interpretation must respect.
  The reasoner is concrete and the set containing the number 2 is abstract
  (owner, 2026-11-06). They exclude constant interpretations by a checked
  theorem, `Anchors.not_constant`.
* Concreteness is world-independent: it is a classification of a candidate, not
  a world-relative state. Concreteness at a world is existence there together
  with concreteness (`ConcreteAt`).
-/

@[expose] public section

namespace TruthCore.Ontology.ConcreteAbstract

open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-- Criterion-neutral concrete/abstract classification. Both predicates are
supplied, and disjointness is required. Neither is defined as the complement of
the other, and nothing forces every candidate into one of them. -/
structure Classification (B : Type) where
  concrete : B → Prop
  abstract : B → Prop
  disjoint : ∀ x, abstract x → ¬ concrete x

/-- Every candidate is concrete or abstract. It is not assumed for an arbitrary
classification: the rival criteria need not satisfy it. For the esse
classification it is derived from excluded middle (`EsseDichotomy`). -/
def Exhaustive {B : Type} (c : Classification B) : Prop :=
  ∀ x, c.concrete x ∨ c.abstract x

/-- A category predicate is constant (degenerate) when it holds of every
candidate or of none. `corpus.py check` warns about such instantiations
in Lean sources unless they are declared intended. -/
def Constant {B : Type} (p : B → Prop) : Prop :=
  (∀ x, p x) ∨ (∀ x, ¬ p x)

/-- Concrete at a world: the candidate exists there and is concrete.
Existence is the world-relative `Ontic.ExistsAt`; concreteness is not. -/
def ConcreteAt {W B : Type} (o : Ontic W B) (c : Classification B)
    (w : W) (x : B) : Prop :=
  o.ExistsAt w x ∧ c.concrete x

/-- Paradigm anchors that every intended interpretation must respect (owner,
#1103, 2026-11-06): "everyone would identify himself or herself as a concrete
being and the set containing the number 2 as an abstract concept". `reasoner`
and `setOfTwo` name the candidates that play these roles in the model. -/
structure Anchors {B : Type} (c : Classification B) where
  reasoner : B
  setOfTwo : B
  reasonerConcrete : c.concrete reasoner
  setOfTwoAbstract : c.abstract setOfTwo

/-- An anchored classification is not degenerate. Neither `concrete` nor
`abstract` is constant: the reasoner is concrete and, by disjointness, not
abstract; the set of 2 is abstract and, by disjointness, not concrete. -/
theorem Anchors.not_constant {B : Type} {c : Classification B} (a : Anchors c) :
    ¬ Constant c.concrete ∧ ¬ Constant c.abstract := by
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · exact c.disjoint a.setOfTwo a.setOfTwoAbstract (h a.setOfTwo)
    · exact h a.reasoner a.reasonerConcrete
  · rintro (h | h)
    · exact c.disjoint a.reasoner (h a.reasoner) a.reasonerConcrete
    · exact h a.setOfTwo a.setOfTwoAbstract

/-! ## The adopted sense: esse in re -/

/-- Adopted sense of concrete (owner, #1103): the candidate has its own esse
in re. `InAct x esse` is the shared Aquinas vocabulary (`DEF-ESSE`, ST I q.4 a.1
ad 3) for "x is in act in the respect of being". It is read as being in the
first sense of De ente c.1, which "aliquid in re ponit". It does not cover the
second sense (propositional truth), in which privations "are". -/
def HasEsseInRe {B R : Type} (InAct : B → R → Prop) (esse : R) (x : B) : Prop :=
  InAct x esse

/-- Adopted sense of abstract (owner, #1103): the contradictory of concrete,
i.e. no esse in re. At most it has being in the intellect, as the number 2 or a
universal has (De ente c.2, "esse in anima"; ST I q.85 a.1 ad 2). There are no
borderline cases: "We have these words in order to draw a line" (owner). -/
def EsseAbstract {B R : Type} (InAct : B → R → Prop) (esse : R) (x : B) : Prop :=
  ¬ InAct x esse

/-- The esse classification. Its disjointness is derived from the definitions
by non-contradiction, constructively; it is not stipulated. -/
def esseClassification {B R : Type} (InAct : B → R → Prop) (esse : R) :
    Classification B where
  concrete := HasEsseInRe InAct esse
  abstract := EsseAbstract InAct esse
  disjoint := fun _ hAbstract hConcrete => hAbstract hConcrete

/-- The exact dichotomy for the esse criterion: every candidate is concrete or
abstract and none is both. Exhaustiveness is the instance of excluded middle at
"x has esse in re"; disjointness needs no premise. This holds for the esse
criterion only: the rival criteria below need not be exhaustive. -/
def EsseDichotomy {B R : Type} (InAct : B → R → Prop) (esse : R) : Prop :=
  ∀ x, (HasEsseInRe InAct esse x ∨ EsseAbstract InAct esse x) ∧
    ¬ (HasEsseInRe InAct esse x ∧ EsseAbstract InAct esse x)

/-! ## Rival criteria (sibling senses, not the adopted one)

Each rival is typed from its own supplied primitive, so that it can be compared
with the adopted sense rather than silently identified with it. -/

/-- Causal-efficacy criterion (SEP §3.2): concrete iff it has causal power at
some world. It is NOT used to define concreteness. If it were, "only concrete
things have causal power" would hold by definition. -/
def CausalCriterionConcrete {W B : Type} (hasCausalPower : W → B → Prop) (x : B) :
    Prop :=
  ∃ w, hasCausalPower w x

/-- Spatiotemporal criterion (SEP §3.1): concrete iff it occupies some region,
for a supplied occupation relation. It classifies immaterial agents as
non-concrete, which is why it is not the adopted sense. -/
def SpatiotemporalCriterionConcrete {B Region : Type} (occupies : B → Region → Prop)
    (x : B) : Prop :=
  ∃ r, occupies x r

/-- Frege's criterion (SEP §3): abstract iff neither mental nor physical, for
supplied predicates. -/
def FregeCriterionAbstract {B : Type} (mental physical : B → Prop) (x : B) : Prop :=
  ¬ mental x ∧ ¬ physical x

end TruthCore.Ontology.ConcreteAbstract
