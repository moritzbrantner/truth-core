module

public import TruthCore.Causality.NecessarySupportCoverage
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.Round3FourthWay

/-!
# Graded foundation: well-founded support from a well-founded grade of being

Analyst formulations, attribution deferred. Target: the two foundation
commitments of the modal spine's join and of its direct actual-grounding routes,
`NecessaryRootFork.ActualGroundingWF` (`STMT-ACTUAL-GROUNDING-WF`) and
`NecessaryConcreteUnderived.ConcreteNecessaryUnionWF`
(`STMT-CONCRETE-NECESSARY-UNION-WF`, J2). Question: do they rest on one deeper
commitment, a well-founded grade of being that support ascends?

Reused unchanged: the #505 `Profile` and its selected relation `grounds v a b`
(at world `v`, `a` sustains `b`'s being there), `ActualConcrete`,
`Round2Grounding.ActualGroundIsMoreInEsse` (`STMT-ACTUAL-GROUND-IS-MORE-IN-ESSE`)
and `Round3FourthWay.NoInfiniteAscentInBeing` (`STMT-NO-INFINITE-ASCENT-IN-BEING`),
both stated over the same primitive comparative `MoreIn esse` (DEF-MORE-IN at
the respect DEF-ESSE; `DISAMB-BEING-UNIVOCITY` and `DISAMB-ORDER-OF-BEING`
record that it is one primitive comparative compatible with the univocal and
the attribution order models), and the Aristotelian
`CauseOfQualityInAnotherIsMoreSuchReading` (`STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH`).

`MoreIn` takes no world argument: a grade comparison is rigid, the same at every
world. That is what lets one grade constrain support edges at different worlds.
New, all open analyst premises:

* `NecessarySupportAscendsInEsse`: at any admitted world, a concrete supporter
  of a concretum, both necessary from `w`, is more in esse than what it supports;
* `SupportAscendsInEsseEverywhere`: the same for every concrete supporter at
  every admitted world, necessary or not; it implies the previous condition and
  `ActualGroundIsMoreInEsse` at every world;
* `NoInfiniteAscentAmongActualConcreta` and
  `NoInfiniteAscentAmongNecessaryConcreta`: the weak versions of no infinite
  ascent in being that the two foundation conditions need; the global
  `NoInfiniteAscentInBeing` implies both and also feeds the grades-to-maximum
  route, so it is the one shared commitment;
* `ActualGroundIsDistinctEsseCause`: an actual concrete ground of an actual
  concretum is distinct from it and a cause of its being (`CausesIn _ _ esse`,
  CAUSE_2 at esse). The converse direction is the existing
  `STMT-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND`.

Two existential characterizations, `GradedActualGrounding` and
`GradedNecessarySupport`, say that SOME well-founded rigid grade is ascended. The
results show each is equivalent to the corresponding well-foundedness condition,
so the graded reformulation is not weaker than well-foundedness when the grade
may be chosen freely. Its extra content is the identification of the grade with
the Fourth Way's `MoreIn esse`, which `STMT-GRADES-TO-MAXIMUM-AT-BEING` also uses.
-/

@[expose] public section

namespace TruthCore.Causality.GradedSupportFoundation

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.Round2Grounding (ActualGroundIsMoreInEsse)
open TruthCore.Causality.Round3FourthWay (NoInfiniteAscentInBeing)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B R : Type}

/-- At every admitted world `v` (accessible from `w` or not), if concrete `a`
exists at `v` and stands to concrete `b` in the selected relation at `v`, and both
exist at every world accessible from `w`, then `a` is more in esse than `b`. The
grade is rigid (no world argument), so support edges between necessary concreta
at different worlds are all measured by one comparison. `b` need not exist at `v`. -/
def NecessarySupportAscendsInEsse (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∀ v a b, m.concrete a → m.concrete b → NecessaryAt m.ontic w a →
    NecessaryAt m.ontic w b → m.ontic.ExistsAt v a → m.grounds v a b → MoreIn esse a b

/-- At every admitted world `v`, a concrete candidate existing at `v` that stands
to a concrete candidate in the selected relation at `v` is more in esse than it.
No necessity restriction and no world parameter. -/
def SupportAscendsInEsseEverywhere (m : Profile W B)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∀ v a b, m.concrete a → m.concrete b → m.ontic.ExistsAt v a → m.grounds v a b →
    MoreIn esse a b

/-- At `w`, an actual concrete ground of an actual concretum is distinct from it
and is a cause of its being: `CausesIn a b esse`. Only this direction (ground to
cause) is stated. -/
def ActualGroundIsDistinctEsseCause (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ a b, ActualConcrete m w a → ActualConcrete m w b → m.grounds w a b →
    a ≠ b ∧ CausesIn a b esse

/-- At every admitted world `v`, a concrete candidate existing at `v` that
stands to a concrete candidate in the selected relation at `v` is distinct from
it and is a cause of its being, `CausesIn a b esse`. The cause dictionary takes no
world argument, so support at any world makes the supporter a cause of the
supported thing's being simpliciter: a cross-world identification, stated
explicitly. -/
def SupportIsDistinctEsseCauseEverywhere (m : Profile W B)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ v a b, m.concrete a → m.concrete b → m.ontic.ExistsAt v a → m.grounds v a b →
    a ≠ b ∧ CausesIn a b esse

/-- No infinite ascent in esse among actual concreta at `w`: the comparison
restricted to concreta existing at `w` is well-founded. The weak version of
`NoInfiniteAscentInBeing` (which forbids infinite ascent among all candidates,
merely possible ones included); it is all that well-founded actual grounding
needs. -/
def NoInfiniteAscentAmongActualConcreta (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  WellFounded fun y x => ActualConcrete m w y ∧ ActualConcrete m w x ∧ MoreIn esse y x

/-- No infinite ascent in esse among concreta necessary from `w`. The weak
version of `NoInfiniteAscentInBeing` that J2 needs. -/
def NoInfiniteAscentAmongNecessaryConcreta (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  WellFounded fun y x => m.concrete y ∧ m.concrete x ∧ NecessaryAt m.ontic w y ∧
    NecessaryAt m.ontic w x ∧ MoreIn esse y x

/-- Some rigid comparison on candidates (at a single respect) is ascended by
actual concrete grounding at `w` and has no infinite ascent. -/
def GradedActualGrounding (m : Profile W B) (w : W) : Prop :=
  ∃ MoreIn : Unit → B → B → Prop,
    ActualGroundIsMoreInEsse m w MoreIn () ∧ NoInfiniteAscentInBeing MoreIn ()

/-- Some rigid comparison on candidates (at a single respect) is ascended by
support between concreta necessary from `w` at every admitted world and has no
infinite ascent. -/
def GradedNecessarySupport (m : Profile W B) (w : W) : Prop :=
  ∃ MoreIn : Unit → B → B → Prop,
    NecessarySupportAscendsInEsse m w MoreIn () ∧ NoInfiniteAscentInBeing MoreIn ()

namespace Control

/-- The grade on `Bool` candidates used by the controls: `false` is more in esse
than `true`, at every respect. -/
def boolGrade (_ : Unit) (a b : Bool) : Prop := a = false ∧ b = true

/-- The reversed grade: `true` is more in esse than `false`. -/
def reversedGrade (_ : Unit) (a b : Bool) : Prop := a = true ∧ b = false

/-- The cause dictionary of the joint witness: `false` causes `true`'s being. -/
def boolCause (a b : Bool) (_ : Unit) : Prop := a = false ∧ b = true

/-- Joint witness on `NecessaryConcreteUnderived.witnessProfile` (the necessary
root `false` grounds the contingent `true` at the actual world `false`): every
new premise, both reused grade premises, the Aristotelian cause principle, both
foundation conditions and every existing joint premise hold, with a nonempty
grounding edge, grade and cause. -/
def GradedJointWitness : Prop :=
  NecessaryConcreteUnderived.JointWitness ∧
    SupportAscendsInEsseEverywhere witnessProfile boolGrade () ∧
    NecessarySupportAscendsInEsse witnessProfile false boolGrade () ∧
    ActualGroundIsMoreInEsse witnessProfile false boolGrade () ∧
    NoInfiniteAscentInBeing boolGrade () ∧
    ActualGroundIsDistinctEsseCause witnessProfile false boolCause () ∧
    TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
      boolCause boolGrade ∧
    witnessProfile.grounds false false true ∧ boolGrade () false true ∧
    boolCause false true ()

/-- Grounding descending in grade: in `witnessProfile` with the reversed grade
(the grounded `true` is more in esse than its ground `false`), actual grounding is
well-founded and the grade has no infinite ascent, yet the actual ground is not
more in esse than what it grounds. Well-foundedness of grounding and of the grade
do not give ascent. -/
def DescendingGrade : Prop :=
  ActualGroundingWF witnessProfile false ∧ NoInfiniteAscentInBeing reversedGrade () ∧
    ¬ ActualGroundIsMoreInEsse witnessProfile false reversedGrade ()

/-- Off-world ascent: in `NecessarySupportCoverage.Control.uncoveredEdge` (two
necessary concreta; only at the non-actual world `true` does `false` support
`true`), support at every world ascends the grade and the grade has no infinite
ascent, while coverage and the one-way no-novel-edge condition fail. -/
def OffWorldAscent : Prop :=
  SupportAscendsInEsseEverywhere Control.uncoveredEdge boolGrade () ∧
    NecessarySupportAscendsInEsse Control.uncoveredEdge false boolGrade () ∧
    NoInfiniteAscentInBeing boolGrade () ∧
    ConcreteNecessaryUnionWF Control.uncoveredEdge false ∧
    ¬ NecessarySupportActuallyCovered Control.uncoveredEdge false ∧
    ¬ NoNovelNecessarySupport (concreteOntic Control.uncoveredEdge)
        (concreteSupport Control.uncoveredEdge) false

/-- No rigid well-founded grade fits the recorded J2 rivals: in the rotating
triangle (at `t0`) and the rooted pair (at `false`, where the join's endpoint
holds), for no respect type, comparison and respect does support between
necessary concreta ascend a comparison with no infinite ascent. -/
def NoGradeForRivals : Prop :=
  (∀ (R : Type) (MoreIn : R → Control.Tri → Control.Tri → Prop) (esse : R),
    ¬ (NecessarySupportAscendsInEsse Control.rotatingTriangle .t0 MoreIn esse ∧
      NoInfiniteAscentAmongNecessaryConcreta Control.rotatingTriangle .t0 MoreIn esse)) ∧
  (∀ (R : Type) (MoreIn : R → Control.Tri → Control.Tri → Prop) (esse : R),
    ¬ (NecessarySupportAscendsInEsse Control.rootedPair false MoreIn esse ∧
      NoInfiniteAscentAmongNecessaryConcreta Control.rootedPair false MoreIn esse)) ∧
  NecessaryConcreteUnderivedAt Control.rootedPair false

/-- All graded-foundation controls. -/
def Controls : Prop := GradedJointWitness ∧ DescendingGrade ∧ OffWorldAscent ∧ NoGradeForRivals

end Control

end TruthCore.Causality.GradedSupportFoundation
