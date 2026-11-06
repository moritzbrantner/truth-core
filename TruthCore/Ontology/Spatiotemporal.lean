module

public import TruthCore.Ontology.ConcreteAbstract

/-!
# Spatiotemporality as its own property (#1109)

Spatiotemporality is typed here as a property of its own. It is **not** a
criterion of concreteness: the adopted sense of concrete is having esse in re
(`ConcreteAbstract.HasEsseInRe`, owner decision on #1103), and whether a concrete
thing is in space and time is a further question. Thomism answers it with
concrete beings that are not spatiotemporal (God, angels, separated souls);
naturalism denies exactly that.

* `Frame B` supplies, for candidates `B`, a type of regions, an occupation
  relation, a spatiotemporal relation between candidates, a parthood relation
  and a candidate `whole` that plays the spacetime system. Nothing about them is
  assumed: no axioms of mereology, of location or of the geometry of regions.
  Whether the whole exists at a world is the separate, world-relative
  `Ontic.ExistsAt` question (relationalists deny that it does).
* The rival senses of "spatiotemporal" (`DISAMB-SPATIOTEMPORAL`) are kept apart:
  `Located` (occupies some region: the occupant sense), `Related` (stands in a
  spatiotemporal relation to something: the relational sense) and
  `PartOfSpacetime` (is a part of the spacetime whole, improper parthood
  allowed: the part-of-spacetime sense). No sense is defined from another.
* Occupation is dimensive location. Aquinas's presence of God everywhere "by
  power, presence and essence" (ST I q.8 a.3) and an angel's definitive
  presence by applying its power (ST I q.52 a.1–2) are not occupation; the
  frame does not represent them, so a God present everywhere by power is not
  thereby `Located`. This is a reading choice recorded in
  `DISAMB-SPATIOTEMPORAL`, not a source claim.
* `SpatiotemporalIndependentOfConcrete` says that for an anchored esse
  classification all four combinations of concrete/abstract with
  spatiotemporal/not can occur, in each sense. It is a consistency fact about the
  definitions, not a claim about which combinations are actual.
-/

@[expose] public section

namespace TruthCore.Ontology.Spatiotemporal

open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.ConcreteAbstract

/-- A spacetime frame over candidates `B`: regions, occupation of a region,
a spatiotemporal relation between candidates, parthood, and the candidate that
plays the spacetime whole. All are supplied; none is constrained. -/
structure Frame (B : Type) where
  Region : Type
  locatedAt : B → Region → Prop
  related : B → B → Prop
  partOf : B → B → Prop
  whole : B

/-- Occupant sense: the candidate occupies some region. The proposition is the
same as the rival concreteness criterion `SpatiotemporalCriterionConcrete`
(SEP "Abstract Objects" §3.1), reused here as a property, not as a criterion of
concreteness. -/
def Located {B : Type} (F : Frame B) (x : B) : Prop :=
  SpatiotemporalCriterionConcrete F.locatedAt x

/-- Relational sense: the candidate stands in a spatiotemporal relation to some
candidate. -/
def Related {B : Type} (F : Frame B) (x : B) : Prop :=
  ∃ y, F.related x y

/-- Part-of-spacetime sense: the candidate is a part of the spacetime whole.
Parthood here may be improper: whether the whole is a part of itself is left to
the supplied relation. -/
def PartOfSpacetime {B : Type} (F : Frame B) (x : B) : Prop :=
  F.partOf x F.whole

/-- All four combinations of a classification predicate and a spatiotemporal
predicate occur. -/
def IndependentOf {B : Type} (concrete st : B → Prop) : Prop :=
  (∃ x, concrete x ∧ st x) ∧ (∃ x, concrete x ∧ ¬ st x) ∧
    (∃ x, ¬ concrete x ∧ st x) ∧ (∃ x, ¬ concrete x ∧ ¬ st x)

/-- Spatiotemporality is a separate property: some anchored esse classification
(the reasoner concrete, the set of 2 abstract) and some frame make every one of
the three spatiotemporal senses independent of concreteness. Hence no sense
follows from concreteness or from abstractness, and none implies either. -/
def SpatiotemporalIndependentOfConcrete : Prop :=
  ∃ (B R : Type) (InAct : B → R → Prop) (esse : R) (F : Frame B),
    Nonempty (Anchors (esseClassification InAct esse)) ∧
      IndependentOf (HasEsseInRe InAct esse) (Located F) ∧
      IndependentOf (HasEsseInRe InAct esse) (Related F) ∧
      IndependentOf (HasEsseInRe InAct esse) (PartOfSpacetime F)

/-- The Thomist combination at a world: some existing concrete candidate is not
spatiotemporal in the supplied sense `st`. Aquinas's own texts say that God,
angels and the intellectual soul are incorporeal (ST I q.3 a.1; q.50 a.1;
q.75 a.2); reading incorporeal as not spatiotemporal is the analyst's step. -/
def SomeConcreteNotSpatiotemporal {W B : Type} (o : Ontic W B)
    (concrete st : B → Prop) (w : W) : Prop :=
  ∃ x, o.ExistsAt w x ∧ concrete x ∧ ¬ st x

end TruthCore.Ontology.Spatiotemporal
