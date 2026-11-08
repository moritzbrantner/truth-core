module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
public import TruthCore.Alternatives.NightCosmogony
public import TruthCore.Case.Catholicism.StageOneConvergence
public import TruthCore.Causality.Round2ExistenceAct
public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Causality.RivalRefutationsRound2

/-!
# Round 4: revisited derivation leads (exploration maps)

Open analyst premises for derivations of six root-path statements whose
derivation leads were rejected earlier (ATTEMPT-REJECTED-DERIVATION-LEADS-20261107)
mainly because each would add bare premises, which the exploration direction of
2026-11-07 now allows when they are labelled open:

* `ActSimplyPriorToPotencyReading` (`STMT-ACT-SIMPLY-PRIOR-TO-POTENCY`), through a
  ground of every potency, idle potency included, or through a fork on whether the
  potency is being actualized;
* `MatterFormAndEsseEssenceAreCompositionsReading`
  (`STMT-MATTER-FORM-AND-ESSE-ESSENCE-ARE-COMPOSITIONS`), through a component
  analysis of `Composite` by two distinct constituent principles;
* `CauseOfNecessaryBeingCausesItsNecessity`
  (`STMT-CAUSE-OF-NECESSARY-BEING-CAUSES-ITS-NECESSITY`), through the respect in
  which a necessary being's necessity consists, or through necessity as a
  perfection carried by the cause of being;
* `ImmaterialIsIntellectualReading` (`STMT-IMMATERIAL-IS-INTELLECTUAL`), through a
  grade order of immateriality;
* `InhabitedConcreteAt` (`STMT-COGITO-INHABITED-CONCRETE-WORLD`), through the
  causal criterion of concreteness applied to the bearer's intellectual exercise;
* `PerSeMoverLinkIsPerSeCauseLinkReading`
  (`STMT-PER-SE-MOVER-LINK-IS-PER-SE-CAUSE-LINK`), from three existing open
  premises (no new vocabulary).

Maps: `explorations/round4-*.toml`. Every definition below is an OPEN analyst
formulation with attribution deferred. New predicate parameters
(`GroundsPotency`, `ConstituentOf`, `NecessityConsistsIn`, `AtLeastAsImmaterial`)
are unconstrained except by the premises that use them; their intended senses are
recorded in the linked `DEF-` records. The reused vocabulary keeps its meaning.
-/

@[expose] public section

namespace TruthCore.Causality.Round4Revisited

open TruthCore.Latin.Aquinas.SummaTheologiae

/-! ## Map 1: act simply prior to potency -/

/-- OPEN: every potency has a ground: whatever is in potency in a respect has
some being on which that potency depends (`DEF-POTENCY-GROUND`), whether or not
the potency is now being actualized. A potency that floats free of every
actual principle (a brute, idle possibility) falsifies it. -/
def PotencyHasGround {B R : Type} (InPotency : B → R → Prop)
    (GroundsPotency : B → B → R → Prop) : Prop :=
  ∀ x r, InPotency x r → ∃ y, GroundsPotency y x r

/-- OPEN: whatever grounds a potency in a respect is in act in that respect. The
q.3 a.1 sentence (*quod est in potentia, non reducitur in actum nisi per ens
actu*) says this of what reduces a potency to act; this premise says it of what
grounds a potency, idle potency included. -/
def GroundOfPotencyIsInAct {B R : Type} (GroundsPotency : B → B → R → Prop)
    (InAct : B → R → Prop) : Prop :=
  ∀ y x r, GroundsPotency y x r → InAct y r

/-- OPEN: whatever grounds a thing's potency is simply prior to that thing
(dependence of the potency is simple posteriority of its bearer,
`DEF-SIMPLE-PRIORITY`). -/
def GroundOfPotencyIsSimplyPrior {B R : Type} (GroundsPotency : B → B → R → Prop)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ y x r, GroundsPotency y x r → PriorSimply y x

/-- OPEN, restricted to idle potency: whatever is in potency in a respect and is
not being moved in that respect is simply posterior to some being in act in that
respect. It is the half of act's simple priority that the prima via premises do
not supply (`STMT-ACT-PRIOR-FROM-MOTION-FACTS`). -/
def IdlePotencyPosteriorToAct {B R : Type} (InPotency MovedIn InAct : B → R → Prop)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ x r, InPotency x r → ¬ MovedIn x r → ∃ y, InAct y r ∧ PriorSimply y x

/-! ## Map 2: matter-form and esse-essence compositions -/

/-- OPEN component analysis of `Composite`, sufficiency direction: whatever has
two distinct constituent principles is composite (`DEF-CONSTITUENT-PRINCIPLE`).
It does not say that every composite has two constituents. -/
def TwoDistinctConstituentsMakeComposite {B P : Type} (ConstituentOf : P → B → Prop)
    (Composite : B → Prop) : Prop :=
  ∀ x p q, ConstituentOf p x → ConstituentOf q x → p ≠ q → Composite x

/-- OPEN: whatever is composed of matter and form has two distinct constituent
principles (its matter is not its form). -/
def MatterFormCompositeHasDistinctConstituents {B P : Type}
    (ComposedOfMatterAndForm : B → Prop) (ConstituentOf : P → B → Prop) : Prop :=
  ∀ x, ComposedOfMatterAndForm x → ∃ p q, ConstituentOf p x ∧ ConstituentOf q x ∧ p ≠ q

/-- OPEN: when a thing's esse is other than its essence, both are constituent
principles of it. Silent on a thing whose esse is its essence. -/
def DistinctEsseEssenceAreConstituents {B P : Type} (ConstituentOf : P → B → Prop)
    (essenceOf esseOf : B → P) : Prop :=
  ∀ x, esseOf x ≠ essenceOf x → ConstituentOf (essenceOf x) x ∧ ConstituentOf (esseOf x) x

/-! ## Map 3: a cause of a necessary being causes its necessity -/

/-- OPEN: the necessity of a necessary being consists in the respect of being
(`esse`): its necessity is the necessity of its being
(`DEF-NECESSITY-CONSISTS-IN`). -/
def NecessityConsistsInBeing {B T R : Type} (Possible : (T → Prop) → Prop)
    (IsAt : B → T → Prop) (NecessityConsistsIn : B → R → Prop) (esse : R) : Prop :=
  ∀ x, IsNecessary Possible IsAt x → NecessityConsistsIn x esse

/-- OPEN: whoever causes a thing in the respect in which its necessity consists
causes its necessity. -/
def CausingNecessityRespectCausesNecessity {B R : Type}
    (CausesIn : B → B → R → Prop) (NecessityConsistsIn : B → R → Prop)
    (CausesNecessityOf : B → B → Prop) : Prop :=
  ∀ c x r, CausesIn c x r → NecessityConsistsIn x r → CausesNecessityOf c x

/-- OPEN and contested: a necessary being is in act in a respect `nec`, its
necessity, read as a perfection it actually has. Whoever takes necessity to be a
mode of being, not a perfection, denies it. -/
def NecessaryBeingInActOfNecessity {B T R : Type} (Possible : (T → Prop) → Prop)
    (IsAt : B → T → Prop) (InAct : B → R → Prop) (nec : R) : Prop :=
  ∀ x, IsNecessary Possible IsAt x → InAct x nec

/-- OPEN: whoever causes a thing in the respect `nec` causes its necessity. -/
def CausingInNecessityCausesNecessity {B R : Type} (CausesIn : B → B → R → Prop)
    (nec : R) (CausesNecessityOf : B → B → Prop) : Prop :=
  ∀ c x, CausesIn c x nec → CausesNecessityOf c x

/-! ## Map 4: the immaterial is intellectual -/

/-- OPEN reading of "the mode of knowledge follows the mode of immateriality":
having intellect (the primitive power `HasIntellect`, not an actual reception)
is closed upward along the grade order of immateriality
(`DEF-GRADE-OF-IMMATERIALITY`): whatever is at least as immaterial as something
with intellect has intellect. Abstract objects, if at least as immaterial as an
intellectual being, would have intellect; whoever denies that rejects this
premise. -/
def IntellectFollowsGradeOfImmateriality {B : Type} (HasIntellect : B → Prop)
    (AtLeastAsImmaterial : B → B → Prop) : Prop :=
  ∀ x y, HasIntellect y → AtLeastAsImmaterial x y → HasIntellect x

/-- OPEN: something has intellect (a human being, for example). -/
def SomeBeingHasIntellect {B : Type} (HasIntellect : B → Prop) : Prop :=
  ∃ y, HasIntellect y

/-- OPEN: what is altogether immaterial (no matter-form composite and no
component of anything) is at least as immaterial as every being: the highest
grade. -/
def AltogetherImmaterialIsMaximallyImmaterial {B : Type}
    (ComposedOfMatterAndForm : B → Prop) (ComponentOf : B → B → Prop)
    (AtLeastAsImmaterial : B → B → Prop) : Prop :=
  ∀ x, ¬ ComposedOfMatterAndForm x → (∀ y, ¬ ComponentOf x y) → ∀ y, AtLeastAsImmaterial x y

/-! ## Controls -/

namespace Control

open TruthCore.Case.Catholicism
open TruthCore.Alternatives.NightCosmogony
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.Round2ExistenceAct.Control (ont att)
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Causality.RivalRefutationsRound2
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic.CogitoEsse
open TruthCore.Logic.CogitoSubject

/-- Distinct pairs over `Bool`. -/
abbrev neB (y x : Bool) : Prop := y ≠ x

/-- Nothing is possible: every being is necessary. -/
abbrev noPossible : (Unit → Prop) → Prop := fun _ => False

/-! ### Map 1 -/

/-- `actPriorFromGround`, omit `hGround`: an ungrounded potency. -/
def omitGround : Prop :=
  ¬ PotencyHasGround (fun (_ : Unit) (_ : Unit) => True) (fun _ _ _ => False) ∧
    GroundOfPotencyIsInAct (fun (_ _ : Unit) (_ : Unit) => False) (fun _ _ => False) ∧
    GroundOfPotencyIsSimplyPrior (fun (_ _ : Unit) (_ : Unit) => False) (fun _ _ => False) ∧
    ¬ ActSimplyPriorToPotencyReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ _ => True) (fun _ _ => False)

/-- `actPriorFromGround`, omit `hInAct`: the ground is not in act. -/
def omitGroundInAct : Prop :=
  PotencyHasGround (fun (_ : Unit) (_ : Unit) => True) (fun _ _ _ => True) ∧
    ¬ GroundOfPotencyIsInAct (fun (_ _ : Unit) (_ : Unit) => True) (fun _ _ => False) ∧
    GroundOfPotencyIsSimplyPrior (fun (_ _ : Unit) (_ : Unit) => True) (fun _ _ => True) ∧
    ¬ ActSimplyPriorToPotencyReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ _ => True) (fun _ _ => True)

/-- `actPriorFromGround`, omit `hPrior`: the ground is not simply prior. -/
def omitGroundPrior : Prop :=
  PotencyHasGround (fun (_ : Unit) (_ : Unit) => True) (fun _ _ _ => True) ∧
    GroundOfPotencyIsInAct (fun (_ _ : Unit) (_ : Unit) => True) (fun _ _ => True) ∧
    ¬ GroundOfPotencyIsSimplyPrior (fun (_ _ : Unit) (_ : Unit) => True) (fun _ _ => False) ∧
    ¬ ActSimplyPriorToPotencyReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ => True) (fun _ _ => False)

/-- `actPriorFromMotionFork`, omit `hReduced` (excluded middle holds classically
in every model and is not restated): a moved potency with no mover. -/
def omitReduced : Prop :=
  ¬ ReducedOnlyByABeingInActReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ _ => False) (fun _ _ => False) ∧
    NothingMovesItselfInSameRespectReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ _ => False) ∧
    ActualMoverIsSimplyPriorReading (fun (_ : Unit) (_ : Unit) => False) (fun _ _ => True)
      (fun _ _ _ => False) (fun _ _ => False) ∧
    IdlePotencyPosteriorToAct (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ => False) ∧
    ¬ ActSimplyPriorToPotencyReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ _ => True) (fun _ _ => False)

/-- `actPriorFromMotionFork`, omit `hSelf`: the only mover moves itself. -/
def omitSelfMover : Prop :=
  ReducedOnlyByABeingInActReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ _ => True) (fun _ _ => True) ∧
    ¬ NothingMovesItselfInSameRespectReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ _ => True) ∧
    ActualMoverIsSimplyPriorReading (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ _ => True) (fun _ _ => False) ∧
    IdlePotencyPosteriorToAct (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => False) ∧
    ¬ ActSimplyPriorToPotencyReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ => True) (fun _ _ => False)

/-- `actPriorFromMotionFork`, omit `hMoverPrior`: two beings move each other,
neither is simply prior. -/
def omitMoverPrior : Prop :=
  ReducedOnlyByABeingInActReading (fun (_ : Bool) (_ : Unit) => True)
      (fun y x _ => neB y x) (fun _ _ => True) ∧
    NothingMovesItselfInSameRespectReading (fun (_ : Bool) (_ : Unit) => True)
      (fun y x _ => neB y x) ∧
    ¬ ActualMoverIsSimplyPriorReading (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun y x _ => neB y x) (fun _ _ => False) ∧
    IdlePotencyPosteriorToAct (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => False) ∧
    ¬ ActSimplyPriorToPotencyReading (fun (_ : Bool) (_ : Unit) => True)
      (fun _ _ => True) (fun _ _ => False)

/-- `actPriorFromMotionFork`, omit `hIdle`: an idle potency with nothing in act. -/
def omitIdle : Prop :=
  ReducedOnlyByABeingInActReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => False) (fun _ _ => False) ∧
    NothingMovesItselfInSameRespectReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => False) ∧
    ActualMoverIsSimplyPriorReading (fun (_ : Unit) (_ : Unit) => False) (fun _ _ => True)
      (fun _ _ _ => False) (fun _ _ => False) ∧
    ¬ IdlePotencyPosteriorToAct (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => False) ∧
    ¬ ActSimplyPriorToPotencyReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ _ => True) (fun _ _ => False)

/-! ### Map 2 -/

/-- `compositionsFromConstituents`, omit `hTwo`: two distinct constituents, not
composite. -/
def omitTwoConstituents : Prop :=
  ¬ TwoDistinctConstituentsMakeComposite (fun (_ : Bool) (_ : Unit) => True) (fun _ => False) ∧
    MatterFormCompositeHasDistinctConstituents (fun (_ : Unit) => True)
      (fun (_ : Bool) _ => True) ∧
    DistinctEsseEssenceAreConstituents (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => true) (fun _ => true) ∧
    ¬ MatterFormAndEsseEssenceAreCompositionsReading (fun (_ : Unit) => True)
      (fun _ => False) (fun _ => true) (fun _ => true)

/-- `compositionsFromConstituents`, omit `hMatterForm`: a matter-form composite
without constituents. -/
def omitMatterFormConstituents : Prop :=
  TwoDistinctConstituentsMakeComposite (fun (_ : Bool) (_ : Unit) => False) (fun _ => False) ∧
    ¬ MatterFormCompositeHasDistinctConstituents (fun (_ : Unit) => True)
      (fun (_ : Bool) _ => False) ∧
    DistinctEsseEssenceAreConstituents (fun (_ : Bool) (_ : Unit) => False)
      (fun _ => true) (fun _ => true) ∧
    ¬ MatterFormAndEsseEssenceAreCompositionsReading (fun (_ : Unit) => True)
      (fun _ => False) (fun _ => true) (fun _ => true)

/-- `compositionsFromConstituents`, omit `hEsse`: esse other than essence, neither
a constituent. -/
def omitEsseEssenceConstituents : Prop :=
  TwoDistinctConstituentsMakeComposite (fun (_ : Bool) (_ : Unit) => False) (fun _ => False) ∧
    MatterFormCompositeHasDistinctConstituents (fun (_ : Unit) => False)
      (fun (_ : Bool) _ => False) ∧
    ¬ DistinctEsseEssenceAreConstituents (fun (_ : Bool) (_ : Unit) => False)
      (fun _ => true) (fun _ => false) ∧
    ¬ MatterFormAndEsseEssenceAreCompositionsReading (fun (_ : Unit) => False)
      (fun _ => False) (fun _ => true) (fun _ => false)

/-! ### Map 3 -/

/-- `necessityFromConsistsInBeing`, omit `hConsists`. -/
def omitConsistsInBeing : Prop :=
  ¬ NecessityConsistsInBeing noPossible (fun (_ : Unit) _ => True)
      (fun _ (_ : Unit) => False) () ∧
    CausingNecessityRespectCausesNecessity (fun (_ _ : Unit) (_ : Unit) => True)
      (fun _ _ => False) (fun _ _ => False) ∧
    ¬ CauseOfNecessaryBeingCausesItsNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ _ (_ : Unit) => True) () (fun _ _ => False)

/-- `necessityFromConsistsInBeing`, omit `hCausing`. -/
def omitCausingRespect : Prop :=
  NecessityConsistsInBeing noPossible (fun (_ : Unit) _ => True)
      (fun _ (_ : Unit) => True) () ∧
    ¬ CausingNecessityRespectCausesNecessity (fun (_ _ : Unit) (_ : Unit) => True)
      (fun _ _ => True) (fun _ _ => False) ∧
    ¬ CauseOfNecessaryBeingCausesItsNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ _ (_ : Unit) => True) () (fun _ _ => False)

/-- `necessityFromPerfection`, omit `hEvery`: the cause of being causes only being
(respects: `true` = esse, `false` = necessity). -/
def omitCauseOfBeing : Prop :=
  ¬ CauseOfBeingCausesEveryPerfection (fun (_ : Unit) (_ : Bool) => True)
      (fun _ _ r => r = true) true ∧
    NecessaryBeingInActOfNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ (_ : Bool) => True) false ∧
    CausingInNecessityCausesNecessity (fun (_ _ : Unit) r => r = true) false
      (fun _ _ => False) ∧
    ¬ CauseOfNecessaryBeingCausesItsNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ _ r => r = true) true (fun _ _ => False)

/-- `necessityFromPerfection`, omit `hNecAct`: a necessary being not in act of
necessity. -/
def omitNecessityInAct : Prop :=
  CauseOfBeingCausesEveryPerfection (fun (_ : Unit) (r : Bool) => r = true)
      (fun _ _ r => r = true) true ∧
    ¬ NecessaryBeingInActOfNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ (r : Bool) => r = true) false ∧
    CausingInNecessityCausesNecessity (fun (_ _ : Unit) r => r = true) false
      (fun _ _ => False) ∧
    ¬ CauseOfNecessaryBeingCausesItsNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ _ r => r = true) true (fun _ _ => False)

/-- `necessityFromPerfection`, omit `hCausingNec`. -/
def omitCausingNecessity : Prop :=
  CauseOfBeingCausesEveryPerfection (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ _ => True) () ∧
    NecessaryBeingInActOfNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ (_ : Unit) => True) () ∧
    ¬ CausingInNecessityCausesNecessity (fun (_ _ : Unit) (_ : Unit) => True) ()
      (fun _ _ => False) ∧
    ¬ CauseOfNecessaryBeingCausesItsNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ _ (_ : Unit) => True) () (fun _ _ => False)

/-! ### Map 4 -/

/-- `immaterialIntellectualFromGrades`, omit `hFollows`: `true` has intellect,
`false` is as immaterial as anything and lacks it. -/
def omitFollows : Prop :=
  ¬ IntellectFollowsGradeOfImmateriality (fun (y : Bool) => y = true) (fun _ _ => True) ∧
    SomeBeingHasIntellect (fun (y : Bool) => y = true) ∧
    AltogetherImmaterialIsMaximallyImmaterial (fun (_ : Bool) => False) (fun _ _ => False)
      (fun _ _ => True) ∧
    ¬ ImmaterialIsIntellectualReading (fun (_ : Bool) => False) (fun y => y = true)
      (fun _ _ => False)

/-- `immaterialIntellectualFromGrades`, omit `hSome`: nothing has intellect. -/
def omitSomeIntellect : Prop :=
  IntellectFollowsGradeOfImmateriality (fun (_ : Unit) => False) (fun _ _ => True) ∧
    ¬ SomeBeingHasIntellect (fun (_ : Unit) => False) ∧
    AltogetherImmaterialIsMaximallyImmaterial (fun (_ : Unit) => False) (fun _ _ => False)
      (fun _ _ => True) ∧
    ¬ ImmaterialIsIntellectualReading (fun (_ : Unit) => False) (fun _ => False)
      (fun _ _ => False)

/-- `immaterialIntellectualFromGrades`, omit `hMax`: grades are discrete (each
being only as immaterial as itself). -/
def omitMaximal : Prop :=
  IntellectFollowsGradeOfImmateriality (fun (y : Bool) => y = true) (fun x y => x = y) ∧
    SomeBeingHasIntellect (fun (y : Bool) => y = true) ∧
    ¬ AltogetherImmaterialIsMaximallyImmaterial (fun (_ : Bool) => False) (fun _ _ => False)
      (fun x y => x = y) ∧
    ¬ ImmaterialIsIntellectualReading (fun (_ : Bool) => False) (fun y => y = true)
      (fun _ _ => False)

/-! ### Map 5 -/

/-- `inhabitedFromProduction`, omit `hO`: no thought occurs. -/
def omitOccursProd : Prop :=
  ¬ ThoughtOccurs (fun (_ : Unit) => False) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => False) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => False) (fun _ _ => True) (att False) ∧
    IntellectualExerciseProducesAt (ont False False) (att False) () ∧
    EveryBearerExistsAt (ont False False) (fun (_ : Unit) => False) (fun (_ _ : Unit) => True) () ∧
    CausersRequireConcreteAt (ont False False) (fun _ => False) () ∧
    ¬ InhabitedConcreteAt (ont False False) (fun _ => False) ()

/-- `inhabitedFromProduction`, omit `hB`: a bearerless thought. -/
def omitBearerProd : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    ¬ EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => False) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => False) (att False) ∧
    IntellectualExerciseProducesAt (ont False False) (att False) () ∧
    EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => False) () ∧
    CausersRequireConcreteAt (ont False False) (fun _ => False) () ∧
    ¬ InhabitedConcreteAt (ont False False) (fun _ => False) ()

/-- `inhabitedFromProduction`, omit `hEx`: the bearer does not exercise intellect. -/
def omitExerciseProd : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    ¬ BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att False) ∧
    IntellectualExerciseProducesAt (ont True False) (att False) () ∧
    EveryBearerExistsAt (ont True False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    CausersRequireConcreteAt (ont True False) (fun _ => False) () ∧
    ¬ InhabitedConcreteAt (ont True False) (fun _ => False) ()

/-- `inhabitedFromProduction`, omit `hProd`: the exercise causes nothing. -/
def omitProduction : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    ¬ IntellectualExerciseProducesAt (ont True False) (att True) () ∧
    EveryBearerExistsAt (ont True False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    CausersRequireConcreteAt (ont True False) (fun _ => False) () ∧
    ¬ InhabitedConcreteAt (ont True False) (fun _ => False) ()

/-- `inhabitedFromProduction`, omit `hE`: a concrete causing bearer that does not
exist at the world. -/
def omitExistsProd : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciseProducesAt (ont False True) (att True) () ∧
    ¬ EveryBearerExistsAt (ont False True) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    CausersRequireConcreteAt (ont False True) (fun _ => True) () ∧
    ¬ InhabitedConcreteAt (ont False True) (fun _ => True) ()

/-- `inhabitedFromProduction`, omit `hCauser`: a causing bearer that is not
concrete. -/
def omitCauserConcrete : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciseProducesAt (ont True True) (att True) () ∧
    EveryBearerExistsAt (ont True True) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    ¬ CausersRequireConcreteAt (ont True True) (fun _ => False) () ∧
    ¬ InhabitedConcreteAt (ont True True) (fun _ => False) ()

/-- `inhabitedFromPower`, omit `hO`. -/
def omitOccursPow : Prop :=
  ¬ ThoughtOccurs (fun (_ : Unit) => False) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => False) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => False) (fun _ _ => True) (att False) ∧
    IntellectualExerciserHasPowerAt (att False) (fun (_ _ : Unit) => False) () ∧
    EveryBearerExistsAt (ont False False) (fun (_ : Unit) => False) (fun (_ _ : Unit) => True) () ∧
    PowerRequiresConcreteAt (fun (_ : Unit) => False) (fun (_ _ : Unit) => False) () ∧
    ¬ InhabitedConcreteAt (ont False False) (fun _ => False) ()

/-- `inhabitedFromPower`, omit `hB`. -/
def omitBearerPow : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    ¬ EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => False) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => False) (att False) ∧
    IntellectualExerciserHasPowerAt (att False) (fun (_ _ : Unit) => False) () ∧
    EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => False) () ∧
    PowerRequiresConcreteAt (fun (_ : Unit) => False) (fun (_ _ : Unit) => False) () ∧
    ¬ InhabitedConcreteAt (ont False False) (fun _ => False) ()

/-- `inhabitedFromPower`, omit `hEx`. -/
def omitExercisePow : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    ¬ BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att False) ∧
    IntellectualExerciserHasPowerAt (att False) (fun (_ _ : Unit) => False) () ∧
    EveryBearerExistsAt (ont True False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    PowerRequiresConcreteAt (fun (_ : Unit) => False) (fun (_ _ : Unit) => False) () ∧
    ¬ InhabitedConcreteAt (ont True False) (fun _ => False) ()

/-- `inhabitedFromPower`, omit `hPow`: the exerciser has no causal power. -/
def omitExerciserPower : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    ¬ IntellectualExerciserHasPowerAt (att True) (fun (_ _ : Unit) => False) () ∧
    EveryBearerExistsAt (ont True False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    PowerRequiresConcreteAt (fun (_ : Unit) => False) (fun (_ _ : Unit) => False) () ∧
    ¬ InhabitedConcreteAt (ont True False) (fun _ => False) ()

/-- `inhabitedFromPower`, omit `hE`. -/
def omitExistsPow : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciserHasPowerAt (att True) (fun (_ _ : Unit) => True) () ∧
    ¬ EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    PowerRequiresConcreteAt (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    ¬ InhabitedConcreteAt (ont False False) (fun _ => True) ()

/-- `inhabitedFromPower`, omit `hPowConcrete`: a powerful bearer that is not
concrete. -/
def omitPowerConcrete : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciserHasPowerAt (att True) (fun (_ _ : Unit) => True) () ∧
    EveryBearerExistsAt (ont True False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    ¬ PowerRequiresConcreteAt (fun (_ : Unit) => False) (fun (_ _ : Unit) => True) () ∧
    ¬ InhabitedConcreteAt (ont True False) (fun _ => False) ()

/-! ### Map 6 -/

/-- `perSeMoverLinkFromEfficientCausing`, omit `hLink`: a per se mover link with
no moving. -/
def omitLinkAnalysis : Prop :=
  ¬ PerSeMoverLinkIsMovingByMovedMoverReading (fun (_ _ : Unit) (_ : Unit) => False)
      (fun _ _ => True) ∧
    MoverIsEfficientCauseReading (fun (_ _ : Unit) (_ : Unit) => False) (fun _ _ _ => False) ∧
    SecondEfficientCausesCauseOnlyAsCausedReading (fun (_ _ : Unit) (_ : Unit) => False)
      (fun _ _ => False) ∧
    ¬ PerSeMoverLinkIsPerSeCauseLinkReading (fun (_ _ : Unit) => True) (fun _ _ => False)

/-- `perSeMoverLinkFromEfficientCausing`, omit `hEfficient`: occasionalism, two
beings move each other and cause nothing. -/
def omitMoverEfficient : Prop :=
  PerSeMoverLinkIsMovingByMovedMoverReading (fun (y x : Bool) (_ : Unit) => neB y x) neB ∧
    ¬ MoverIsEfficientCauseReading (fun (y x : Bool) (_ : Unit) => neB y x)
      (fun _ _ _ => False) ∧
    SecondEfficientCausesCauseOnlyAsCausedReading (fun (_ _ : Bool) (_ : Unit) => False)
      (fun _ _ => False) ∧
    ¬ PerSeMoverLinkIsPerSeCauseLinkReading neB (fun _ _ => False)

/-- `perSeMoverLinkFromEfficientCausing`, omit `hSecond`: caused causes that are
not per se links. -/
def omitSecondWay : Prop :=
  PerSeMoverLinkIsMovingByMovedMoverReading (fun (y x : Bool) (_ : Unit) => neB y x) neB ∧
    MoverIsEfficientCauseReading (fun (y x : Bool) (_ : Unit) => neB y x)
      (fun y x _ => neB y x) ∧
    ¬ SecondEfficientCausesCauseOnlyAsCausedReading (fun (y x : Bool) (_ : Unit) => neB y x)
      (fun _ _ => False) ∧
    ¬ PerSeMoverLinkIsPerSeCauseLinkReading neB (fun _ _ => False)

/-! ### Joint witness -/

/-- One nonvacuous interpretation per map, in which every premise and the
conclusion of each derivation hold together: a potency in `false` grounded by and
moved by `true`, which is in act and simply prior; a matter-form composite whose
esse differs from its essence; a necessary being caused in every respect; a being
with intellect at the top grade of immateriality; an occurring thought whose
bearer exists, exercises intellect, causes, has power and is concrete; and two
beings that move and cause each other per se. -/
def witness : Prop :=
  -- map 1
  PotencyHasGround (fun (x : Bool) (_ : Unit) => x = false)
      (fun y x _ => y = true ∧ x = false) ∧
    GroundOfPotencyIsInAct (fun (y x : Bool) (_ : Unit) => y = true ∧ x = false)
      (fun y _ => y = true) ∧
    GroundOfPotencyIsSimplyPrior (fun (y x : Bool) (_ : Unit) => y = true ∧ x = false)
      (fun y x => y = true ∧ x = false) ∧
    ReducedOnlyByABeingInActReading (fun (x : Bool) (_ : Unit) => x = false)
      (fun y x _ => y = true ∧ x = false) (fun y _ => y = true) ∧
    NothingMovesItselfInSameRespectReading (fun (x : Bool) (_ : Unit) => x = false)
      (fun y x _ => y = true ∧ x = false) ∧
    ActualMoverIsSimplyPriorReading (fun (y : Bool) (_ : Unit) => y = true)
      (fun x _ => x = false) (fun y x _ => y = true ∧ x = false)
      (fun y x => y = true ∧ x = false) ∧
    IdlePotencyPosteriorToAct (fun (x : Bool) (_ : Unit) => x = false) (fun x _ => x = false)
      (fun y _ => y = true) (fun y x => y = true ∧ x = false) ∧
    ActSimplyPriorToPotencyReading (fun (y : Bool) (_ : Unit) => y = true)
      (fun x _ => x = false) (fun y x => y = true ∧ x = false) ∧
  -- map 2
    TwoDistinctConstituentsMakeComposite (fun (_ : Bool) (_ : Unit) => True) (fun _ => True) ∧
    MatterFormCompositeHasDistinctConstituents (fun (_ : Unit) => True)
      (fun (_ : Bool) _ => True) ∧
    DistinctEsseEssenceAreConstituents (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => true) (fun _ => false) ∧
    MatterFormAndEsseEssenceAreCompositionsReading (fun (_ : Unit) => True)
      (fun _ => True) (fun _ => true) (fun _ => false) ∧
  -- map 3
    NecessityConsistsInBeing noPossible (fun (_ : Unit) _ => True)
      (fun _ (_ : Unit) => True) () ∧
    CausingNecessityRespectCausesNecessity (fun (_ _ : Unit) (_ : Unit) => True)
      (fun _ _ => True) (fun _ _ => True) ∧
    CauseOfBeingCausesEveryPerfection (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ _ => True) () ∧
    NecessaryBeingInActOfNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ (_ : Unit) => True) () ∧
    CausingInNecessityCausesNecessity (fun (_ _ : Unit) (_ : Unit) => True) ()
      (fun _ _ => True) ∧
    CauseOfNecessaryBeingCausesItsNecessity noPossible (fun (_ : Unit) _ => True)
      (fun _ _ (_ : Unit) => True) () (fun _ _ => True) ∧
  -- map 4
    IntellectFollowsGradeOfImmateriality (fun (_ : Unit) => True) (fun _ _ => True) ∧
    SomeBeingHasIntellect (fun (_ : Unit) => True) ∧
    AltogetherImmaterialIsMaximallyImmaterial (fun (_ : Unit) => False) (fun _ _ => False)
      (fun _ _ => True) ∧
    ImmaterialIsIntellectualReading (fun (_ : Unit) => False) (fun _ => True)
      (fun _ _ => False) ∧
  -- map 5
    ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciseProducesAt (ont True True) (att True) () ∧
    IntellectualExerciserHasPowerAt (att True) (fun (_ _ : Unit) => True) () ∧
    EveryBearerExistsAt (ont True True) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    CausersRequireConcreteAt (ont True True) (fun _ => True) () ∧
    PowerRequiresConcreteAt (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    InhabitedConcreteAt (ont True True) (fun _ => True) () ∧
  -- map 6
    PerSeMoverLinkIsMovingByMovedMoverReading (fun (y x : Bool) (_ : Unit) => neB y x) neB ∧
    MoverIsEfficientCauseReading (fun (y x : Bool) (_ : Unit) => neB y x)
      (fun y x _ => neB y x) ∧
    SecondEfficientCausesCauseOnlyAsCausedReading (fun (y x : Bool) (_ : Unit) => neB y x)
      neB ∧
    PerSeMoverLinkIsPerSeCauseLinkReading neB neB ∧
    (∃ y x : Bool, neB y x)

/-- The batch controls: one omission model per premise of each derivation
(excluded middle excepted: it is logical and holds classically in every model)
and one joint nonvacuity witness. Satisfiability and omission only; no model is
claimed to describe reality. -/
def Certificate : Prop :=
  omitGround ∧ omitGroundInAct ∧ omitGroundPrior ∧
    omitReduced ∧ omitSelfMover ∧ omitMoverPrior ∧ omitIdle ∧
    omitTwoConstituents ∧ omitMatterFormConstituents ∧ omitEsseEssenceConstituents ∧
    omitConsistsInBeing ∧ omitCausingRespect ∧
    omitCauseOfBeing ∧ omitNecessityInAct ∧ omitCausingNecessity ∧
    omitFollows ∧ omitSomeIntellect ∧ omitMaximal ∧
    omitOccursProd ∧ omitBearerProd ∧ omitExerciseProd ∧ omitProduction ∧ omitExistsProd ∧
    omitCauserConcrete ∧
    omitOccursPow ∧ omitBearerPow ∧ omitExercisePow ∧ omitExerciserPower ∧ omitExistsPow ∧
    omitPowerConcrete ∧
    omitLinkAnalysis ∧ omitMoverEfficient ∧ omitSecondWay ∧ witness

end Control

end TruthCore.Causality.Round4Revisited
