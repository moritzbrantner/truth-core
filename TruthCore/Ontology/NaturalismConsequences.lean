module

public import TruthCore.Ontology.Naturalism
public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
public import TruthCore.Causality.ExistenceActuality
public import TruthCore.Observation.Change
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Logic.EpistemicReasons

/-!
# Consequences of naturalism (#1109)

Vocabulary for the consequence analysis of the naturalist variants in
`TruthCore.Ontology.Naturalism`, by the defeat-by-consequence method of #1007.

**The caused universe (owner argument, 2026-11-06).** "If we also accept that
the universe has a cause, then that cause, which causes time to exist, does
cause and exist out of time." The cause is a cause of the **existence** of the
spacetime whole (dependence or conservation), not of a temporal beginning:
Aquinas holds that a beginning is not demonstrable, so nothing here uses the
kalam premise. The steps are separate inputs:

* `UniverseHasExistingCause`: the whole has an existing cause at `w` (open);
* `CausingWholeCausesParts`: causing the whole to exist includes causing each
  part of it to exist (open bridge, analyst formulation);
* the sourced `NothingIsEfficientCauseOfItselfReading` (ST I q.2 a.3), at the
  relation `fun x y _ => o.Causes w x y` with a trivial respect;
* `ContainedInSpacetime F P`: whatever satisfies the thesis predicate is a part
  of the spacetime whole (true by definition for `P = PartOfSpacetime F`, an
  open bridge for the occupant and relational senses and for Papineau's
  "physical").

The derived-location consequences (laws as immanent universals, pure sets)
and the God-naming consequence are not yet encoded (#1109 remaining work).
-/

@[expose] public section

namespace TruthCore.Ontology.NaturalismConsequences

open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism

/-! ## The caused universe -/

/-- The spacetime whole has an existing cause at `w`. `Causes` is read as
efficient causation of existence (conservation or dependence), not as the
cause of a temporal beginning. -/
def UniverseHasExistingCause {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ∃ c, o.ExistsAt w c ∧ o.Causes w c F.whole

/-- Causing the spacetime whole to exist includes causing each of its parts to
exist. -/
def CausingWholeCausesParts {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ∀ c y, o.Causes w c F.whole → PartOfSpacetime F y → o.Causes w c y

/-- Whatever satisfies the thesis predicate `P` is a part of the spacetime
whole. -/
def ContainedInSpacetime {B : Type} (F : Frame B) (P : B → Prop) : Prop :=
  ∀ x, P x → PartOfSpacetime F x

/-- The spacetime whole satisfies the thesis predicate `P`. -/
def WholeSatisfies {B : Type} (F : Frame B) (P : B → Prop) : Prop :=
  P F.whole

/-- Whatever causes something has causal power (the exercise-to-power
reading). -/
def CausingExercisesPower {W B : Type} (o : Ontic W B) (hasCausalPower : W → B → Prop)
    (w : W) : Prop :=
  ∀ x y, o.Causes w x y → hasCausalPower w x

/-- Every cause of the spacetime whole lies outside it: it is not a part of
spacetime. -/
def CausesOfUniverseOutsideSpacetime {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) :
    Prop :=
  ∀ c, o.Causes w c F.whole → ¬ PartOfSpacetime F c

/-- Whatever is temporal, in the supplied sense, is a part of the spacetime
whole: there is no time outside this spacetime. -/
def TemporalContainedInSpacetime {B : Type} (F : Frame B) (temporal : B → Prop) : Prop :=
  ∀ x, temporal x → PartOfSpacetime F x

/-- Strong version: every cause of the spacetime whole is not temporal at all. -/
def CausesOfUniverseAtemporal {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (temporal : B → Prop) : Prop :=
  ∀ c, o.Causes w c F.whole → ¬ temporal c

/-- The naturalist's brute-universe position: nothing causes the spacetime
whole at `w`. -/
def UniverseUncaused {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ∀ c, ¬ o.Causes w c F.whole

/-! ## Failure of each variant (refutation conclusions) -/

/-- N1 fails at `w`. -/
def ExistenceNaturalismFails {W B : Type} (o : Ontic W B) (P : B → Prop) (w : W) : Prop :=
  ¬ ExistenceNaturalism o P w

/-- N2 fails at `w`. -/
def ConcreteNaturalismFails {W B : Type} (o : Ontic W B) (concrete P : B → Prop) (w : W) :
    Prop :=
  ¬ ConcreteNaturalism o concrete P w

/-- N3 fails at `w`. -/
def CausalPowerNaturalismFails {W B : Type} (hasCausalPower : W → B → Prop) (P : B → Prop)
    (w : W) : Prop :=
  ¬ CausalPowerNaturalism hasCausalPower P w

/-- N3i fails at `w`. -/
def InteractionNaturalismFails {W B : Type} (o : Ontic W B) (P : B → Prop) (w : W) : Prop :=
  ¬ InteractionNaturalism o P w

/-! ## The naturalist escapes, as joint-model statements -/

open TruthCore.Ontology.ConcreteAbstract in
open TruthCore.Causality.CausalPowerConcreteness in
/-- The brute-universe and regress escapes are jointly consistent with every
naturalist variant (in the part-of-spacetime sense, N1 also in the occupant and
relational senses), the owner's #1113 bridge, the anchors, the weak
causal-concreteness floor item, the exercise-to-power reading, the whole-to-part
bridge, no self-causation, and change, motion and epistemic reasons all borne by
parts of spacetime: in some model all of these hold, the spacetime whole exists
and is located, nothing causes it, and every proper part of it has a cause. -/
def NaturalistUncausedUniverseSurvivor : Prop :=
  ∃ (W B R : Type) (o : Ontic W B) (F : Frame B) (InAct : B → R → Prop) (esse : R)
    (hasCausalPower : W → B → Prop) (w : W),
    (∃ a : Anchors (esseClassification InAct esse),
      o.ExistsAt w a.reasoner ∧ ¬ o.ExistsAt w a.setOfTwo) ∧
    TruthCore.Causality.ExistenceActuality.ExistingInActAt o InAct esse w ∧
    ExistenceNaturalism o (PartOfSpacetime F) w ∧ ExistenceNaturalism o (Located F) w ∧
    ExistenceNaturalism o (Related F) w ∧
    ConcreteNaturalism o (HasEsseInRe InAct esse) (PartOfSpacetime F) w ∧
    CausalPowerNaturalism hasCausalPower (PartOfSpacetime F) w ∧
    InteractionNaturalism o (PartOfSpacetime F) w ∧
    OwnerCommitmentAt o (HasEsseInRe InAct esse) hasCausalPower w ∧
    CausingExercisesPower o hasCausalPower w ∧
    CausingWholeCausesParts o F w ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading
      (fun x y (_ : Unit) => o.Causes w x y) ∧
    WholeSatisfies F (PartOfSpacetime F) ∧ o.ExistsAt w F.whole ∧ Located F F.whole ∧
    (∃ Changes : B → Prop, TruthCore.Observation.Change.SomethingChangesReading Changes ∧
      ∀ x, Changes x → PartOfSpacetime F x) ∧
    (∃ MovedIn : B → Unit → Prop,
      TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading MovedIn ∧
      ∀ x r, MovedIn x r → PartOfSpacetime F x) ∧
    (∃ Reason : B → B → Prop, TruthCore.Logic.EpistemicReasons.ThereAreEpistemicReasons Reason ∧
      ∀ a p, Reason a p → PartOfSpacetime F a) ∧
    UniverseUncaused o F w ∧
    (∀ x, PartOfSpacetime F x → x ≠ F.whole → ∃ c, o.Causes w c x)

open TruthCore.Ontology.ConcreteAbstract in
open TruthCore.Causality.CausalPowerConcreteness in
/-- The causal-loop escape: in some model the spacetime whole has an existing
cause, every naturalist variant (part-of-spacetime sense), the anchors, the
#1113 bridge, the causal-concreteness floor item, the exercise-to-power reading,
no self-causation and containment all hold, and the whole-to-part bridge fails.
The cause is a part of spacetime standing in a causal loop with another part. -/
def CausalLoopRejectsBridge : Prop :=
  ∃ (W B R : Type) (o : Ontic W B) (F : Frame B) (InAct : B → R → Prop) (esse : R)
    (hasCausalPower : W → B → Prop) (w : W),
    Nonempty (Anchors (esseClassification InAct esse)) ∧
    TruthCore.Causality.ExistenceActuality.ExistingInActAt o InAct esse w ∧
    ExistenceNaturalism o (PartOfSpacetime F) w ∧
    ConcreteNaturalism o (HasEsseInRe InAct esse) (PartOfSpacetime F) w ∧
    CausalPowerNaturalism hasCausalPower (PartOfSpacetime F) w ∧
    InteractionNaturalism o (PartOfSpacetime F) w ∧
    OwnerCommitmentAt o (HasEsseInRe InAct esse) hasCausalPower w ∧
    CausingExercisesPower o hasCausalPower w ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading
      (fun x y (_ : Unit) => o.Causes w x y) ∧
    ContainedInSpacetime F (PartOfSpacetime F) ∧ WholeSatisfies F (PartOfSpacetime F) ∧
    UniverseHasExistingCause o F w ∧ ¬ CausingWholeCausesParts o F w

end TruthCore.Ontology.NaturalismConsequences
