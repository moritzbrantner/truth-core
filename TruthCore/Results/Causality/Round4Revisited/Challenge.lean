import TruthCore.Causality.Round4Revisited

namespace TruthCore.Results.Causality.Round4Revisited
open TruthCore.Causality.Round4Revisited
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.NightCosmogony
open TruthCore.Case.Catholicism
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Causality.RivalRefutationsRound2
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect (OperationAttribution)
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic.CogitoEsse
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic

/-! ## Map 1: act simply prior to potency -/

/-- Every potency, idle or not, has a ground; the ground is in act in the
respect and simply prior to the bearer of the potency. -/
theorem actPriorFromGround {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (GroundsPotency : B → B → R → Prop)
    (hGround : PotencyHasGround InPotency GroundsPotency)
    (hInAct : GroundOfPotencyIsInAct GroundsPotency InAct)
    (hPrior : GroundOfPotencyIsSimplyPrior GroundsPotency PriorSimply) :
    ActSimplyPriorToPotencyReading InAct InPotency PriorSimply := by
  sorry

/-- Fork on whether the potency is being actualized. If `x` is being moved in
`r`, some mover in act moves it (q.2 a.3 reading), that mover is not `x`
(nothing moves itself in the same respect), so it is simply prior (the open
mover-priority bridge). If `x` is not being moved, the open idle-potency premise
applies. Excluded middle on `MovedIn x r` is used and listed. -/
theorem actPriorFromMotionFork {B R : Type} (InAct InPotency MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (hEM : ExcludedMiddle)
    (hReduced : ReducedOnlyByABeingInActReading MovedIn MovesIn InAct)
    (hSelf : NothingMovesItselfInSameRespectReading MovedIn MovesIn)
    (hMoverPrior : ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply)
    (hIdle : IdlePotencyPosteriorToAct InPotency MovedIn InAct PriorSimply) :
    ActSimplyPriorToPotencyReading InAct InPotency PriorSimply := by
  sorry

/-! ## Map 2: matter-form and esse-essence compositions -/

/-- A matter-form composite has two distinct constituents, and a thing whose esse
is other than its essence has both as constituents; two distinct constituents
make a thing composite. -/
theorem compositionsFromConstituents {B P : Type}
    (ComposedOfMatterAndForm Composite : B → Prop) (essenceOf esseOf : B → P)
    (ConstituentOf : P → B → Prop)
    (hTwo : TwoDistinctConstituentsMakeComposite ConstituentOf Composite)
    (hMatterForm : MatterFormCompositeHasDistinctConstituents ComposedOfMatterAndForm ConstituentOf)
    (hEsse : DistinctEsseEssenceAreConstituents ConstituentOf essenceOf esseOf) :
    MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf := by
  sorry

/-! ## Map 3: a cause of a necessary being causes its necessity -/

/-- A necessary being's necessity consists in its being; whoever causes a thing
in the respect in which its necessity consists causes its necessity. -/
theorem necessityFromConsistsInBeing {B T R : Type} (Possible : (T → Prop) → Prop)
    (IsAt : B → T → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (CausesNecessityOf : B → B → Prop) (NecessityConsistsIn : B → R → Prop)
    (hConsists : NecessityConsistsInBeing Possible IsAt NecessityConsistsIn esse)
    (hCausing : CausingNecessityRespectCausesNecessity CausesIn NecessityConsistsIn
      CausesNecessityOf) :
    CauseOfNecessaryBeingCausesItsNecessity Possible IsAt CausesIn esse CausesNecessityOf := by
  sorry

/-- The cause of a thing's being causes each perfection it is in act of; a
necessary being is in act of necessity (contested); whoever causes a thing's
necessity-perfection causes its necessity. -/
theorem necessityFromPerfection {B T R : Type} (Possible : (T → Prop) → Prop)
    (IsAt : B → T → Prop) (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (esse nec : R) (CausesNecessityOf : B → B → Prop)
    (hEvery : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNecAct : NecessaryBeingInActOfNecessity Possible IsAt InAct nec)
    (hCausingNec : CausingInNecessityCausesNecessity CausesIn nec CausesNecessityOf) :
    CauseOfNecessaryBeingCausesItsNecessity Possible IsAt CausesIn esse CausesNecessityOf := by
  sorry

/-! ## Map 4: the immaterial is intellectual -/

/-- Something has intellect; what is altogether immaterial is at least as
immaterial as it; intellect is closed upward along grades of immateriality. -/
theorem immaterialIntellectualFromGrades {B : Type}
    (ComposedOfMatterAndForm HasIntellect : B → Prop) (ComponentOf : B → B → Prop)
    (AtLeastAsImmaterial : B → B → Prop)
    (hFollows : IntellectFollowsGradeOfImmateriality HasIntellect AtLeastAsImmaterial)
    (hSome : SomeBeingHasIntellect HasIntellect)
    (hMax : AltogetherImmaterialIsMaximallyImmaterial ComposedOfMatterAndForm ComponentOf
      AtLeastAsImmaterial) :
    ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect ComponentOf := by
  sorry

/-! ## Map 5: the Cogito populates the world with a concrete being -/

/-- An occurring thought has a bearer, who exercises intellect in it, so causes
something at `w` (the inner word, contested); every causer at `w` is concrete;
the bearer exists at `w`. -/
theorem inhabitedFromProduction {W E Episode : Type} (m : Ontic W E)
    (concrete : E → Prop) (w : W) (Occurs : Episode → Prop) (Bears : E → Episode → Prop)
    (a : OperationAttribution E Episode)
    (hO : ThoughtOccurs Occurs)
    (hB : EveryThoughtHasSubject Occurs Bears)
    (hEx : BorneThoughtExercisesIntellect Occurs Bears a)
    (hProd : IntellectualExerciseProducesAt m a w)
    (hE : EveryBearerExistsAt m Occurs Bears w)
    (hCauser : CausersRequireConcreteAt m concrete w) :
    InhabitedConcreteAt m concrete w := by
  sorry

/-- As `inhabitedFromProduction`, with the capacity clause: the exerciser has
causal power at `w`, and whatever has causal power at `w` is concrete. -/
theorem inhabitedFromPower {W E Episode : Type} (m : Ontic W E)
    (concrete : E → Prop) (w : W) (Occurs : Episode → Prop) (Bears : E → Episode → Prop)
    (a : OperationAttribution E Episode) (hasCausalPower : W → E → Prop)
    (hO : ThoughtOccurs Occurs)
    (hB : EveryThoughtHasSubject Occurs Bears)
    (hEx : BorneThoughtExercisesIntellect Occurs Bears a)
    (hPow : IntellectualExerciserHasPowerAt a hasCausalPower w)
    (hE : EveryBearerExistsAt m Occurs Bears w)
    (hPowConcrete : PowerRequiresConcreteAt concrete hasCausalPower w) :
    InhabitedConcreteAt m concrete w := by
  sorry

/-! ## Map 6: a per se mover link is a per se cause link -/

/-- A per se mover link is a moving by a distinct mover that is itself moved;
every moving is efficient causing; an efficient cause other than its effect that
is itself caused causes only as caused. -/
theorem perSeMoverLinkFromEfficientCausing {B R : Type} (MovesIn : B → B → R → Prop)
    (EfficientlyCausesIn : B → B → R → Prop) (MovesAsMoved CausesAsCaused : B → B → Prop)
    (hLink : PerSeMoverLinkIsMovingByMovedMoverReading MovesIn MovesAsMoved)
    (hEfficient : MoverIsEfficientCauseReading MovesIn EfficientlyCausesIn)
    (hSecond : SecondEfficientCausesCauseOnlyAsCausedReading EfficientlyCausesIn
      CausesAsCaused) :
    PerSeMoverLinkIsPerSeCauseLinkReading MovesAsMoved CausesAsCaused := by
  sorry

/-! ## Controls -/

open TruthCore.Causality.Round4Revisited.Control
open TruthCore.Causality.Round2ExistenceAct.Control (ont att)

/-- The batch controls: one omission model per premise of each derivation
(excluded middle excepted) and one joint nonvacuity witness. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.Round4Revisited
