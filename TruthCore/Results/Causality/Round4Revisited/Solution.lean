module

public import TruthCore.Causality.Round4Revisited

@[expose] public section

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
  intro x r hx
  obtain ⟨y, hy⟩ := hGround x r hx
  exact ⟨y, hInAct y x r hy, hPrior y x r hy⟩

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
  intro x r hx
  cases hEM (MovedIn x r) with
  | inl hm =>
    obtain ⟨y, hmy, hay⟩ := hReduced x r hm
    have hne : y ≠ x := by
      intro h
      subst h
      exact hSelf y r hm hmy
    exact ⟨y, hay, hMoverPrior y x r hx hmy hay hne⟩
  | inr hn => exact hIdle x r hx hn

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
  intro x
  refine ⟨fun hmf => ?_, fun hne => ?_⟩
  · obtain ⟨p, q, hp, hq, hpq⟩ := hMatterForm x hmf
    exact hTwo x p q hp hq hpq
  · obtain ⟨he, hs⟩ := hEsse x hne
    exact hTwo x (esseOf x) (essenceOf x) hs he hne

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
  intro c x hx hc
  exact hCausing c x esse hc (hConsists x hx)

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
  intro c x hx hc
  exact hCausingNec c x (hEvery c x nec hc (hNecAct x hx))

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
  intro x hmf hcomp
  obtain ⟨y, hy⟩ := hSome
  exact hFollows x y hy (hMax x hmf hcomp y)

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
  obtain ⟨e, he⟩ := hO
  obtain ⟨b, hb⟩ := hB e he
  obtain ⟨y, hy⟩ := hProd b e (hEx b e he hb)
  exact ⟨b, hCauser b y hy, hE b e he hb⟩

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
  obtain ⟨e, he⟩ := hO
  obtain ⟨b, hb⟩ := hB e he
  exact ⟨b, hPowConcrete b (hPow b e (hEx b e he hb)), hE b e he hb⟩

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
  intro y x hyx
  obtain ⟨hne, ⟨r, hr⟩, z, r', hz⟩ := hLink y x hyx
  exact hSecond y x r hne (hEfficient y x r hr) ⟨z, r', hEfficient z y r' hz⟩

/-! ## Controls -/

section Controls
open TruthCore.Causality.Round4Revisited.Control
open TruthCore.Causality.Round2ExistenceAct.Control (ont att)

macro "ctrl" : tactic => `(tactic| (
  delta PotencyHasGround GroundOfPotencyIsInAct GroundOfPotencyIsSimplyPrior
    IdlePotencyPosteriorToAct TwoDistinctConstituentsMakeComposite
    MatterFormCompositeHasDistinctConstituents DistinctEsseEssenceAreConstituents
    NecessityConsistsInBeing CausingNecessityRespectCausesNecessity
    NecessaryBeingInActOfNecessity CausingInNecessityCausesNecessity
    IntellectFollowsGradeOfImmateriality SomeBeingHasIntellect
    AltogetherImmaterialIsMaximallyImmaterial
    ActSimplyPriorToPotencyReading ReducedOnlyByABeingInActReading
    NothingMovesItselfInSameRespectReading ActualMoverIsSimplyPriorReading
    MatterFormAndEsseEssenceAreCompositionsReading CauseOfNecessaryBeingCausesItsNecessity
    CauseOfBeingCausesEveryPerfection IsNecessary PossibleNotToBe
    ImmaterialIsIntellectualReading ThoughtOccurs EveryThoughtHasSubject
    BorneThoughtExercisesIntellect IntellectualExerciseProducesAt
    IntellectualExerciserHasPowerAt EveryBearerExistsAt CausersRequireConcreteAt
    PowerRequiresConcreteAt InhabitedConcreteAt PerSeMoverLinkIsMovingByMovedMoverReading
    MoverIsEfficientCauseReading SecondEfficientCausesCauseOnlyAsCausedReading
    PerSeMoverLinkIsPerSeCauseLinkReading
  and_intros <;> decide))

theorem omitGround_holds : omitGround := by delta omitGround; ctrl
theorem omitGroundInAct_holds : omitGroundInAct := by delta omitGroundInAct; ctrl
theorem omitGroundPrior_holds : omitGroundPrior := by delta omitGroundPrior; ctrl
theorem omitReduced_holds : omitReduced := by delta omitReduced; ctrl
theorem omitSelfMover_holds : omitSelfMover := by delta omitSelfMover; ctrl
theorem omitMoverPrior_holds : omitMoverPrior := by delta omitMoverPrior; ctrl
theorem omitIdle_holds : omitIdle := by delta omitIdle; ctrl
theorem omitTwoConstituents_holds : omitTwoConstituents := by delta omitTwoConstituents; ctrl
theorem omitMatterFormConstituents_holds : omitMatterFormConstituents := by
  delta omitMatterFormConstituents; ctrl
theorem omitEsseEssenceConstituents_holds : omitEsseEssenceConstituents := by
  delta omitEsseEssenceConstituents; ctrl
theorem omitConsistsInBeing_holds : omitConsistsInBeing := by delta omitConsistsInBeing; ctrl
theorem omitCausingRespect_holds : omitCausingRespect := by delta omitCausingRespect; ctrl
theorem omitCauseOfBeing_holds : omitCauseOfBeing := by delta omitCauseOfBeing; ctrl
theorem omitNecessityInAct_holds : omitNecessityInAct := by delta omitNecessityInAct; ctrl
theorem omitCausingNecessity_holds : omitCausingNecessity := by delta omitCausingNecessity; ctrl
theorem omitFollows_holds : omitFollows := by delta omitFollows; ctrl
theorem omitSomeIntellect_holds : omitSomeIntellect := by delta omitSomeIntellect; ctrl
theorem omitMaximal_holds : omitMaximal := by delta omitMaximal; ctrl
theorem omitOccursProd_holds : omitOccursProd := by delta omitOccursProd; ctrl
theorem omitBearerProd_holds : omitBearerProd := by delta omitBearerProd; ctrl
theorem omitExerciseProd_holds : omitExerciseProd := by delta omitExerciseProd; ctrl
theorem omitProduction_holds : omitProduction := by delta omitProduction; ctrl
theorem omitExistsProd_holds : omitExistsProd := by delta omitExistsProd; ctrl
theorem omitCauserConcrete_holds : omitCauserConcrete := by delta omitCauserConcrete; ctrl
theorem omitOccursPow_holds : omitOccursPow := by delta omitOccursPow; ctrl
theorem omitBearerPow_holds : omitBearerPow := by delta omitBearerPow; ctrl
theorem omitExercisePow_holds : omitExercisePow := by delta omitExercisePow; ctrl
theorem omitExerciserPower_holds : omitExerciserPower := by delta omitExerciserPower; ctrl
theorem omitExistsPow_holds : omitExistsPow := by delta omitExistsPow; ctrl
theorem omitPowerConcrete_holds : omitPowerConcrete := by delta omitPowerConcrete; ctrl
theorem omitLinkAnalysis_holds : omitLinkAnalysis := by delta omitLinkAnalysis; ctrl
theorem omitMoverEfficient_holds : omitMoverEfficient := by delta omitMoverEfficient; ctrl
theorem omitSecondWay_holds : omitSecondWay := by delta omitSecondWay; ctrl
theorem witness_holds : witness := by
  delta witness
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ctrl

/-- The batch controls: one omission model per premise of each derivation
(excluded middle excepted) and one joint nonvacuity witness. -/
theorem controls : Certificate :=
  ⟨omitGround_holds, omitGroundInAct_holds, omitGroundPrior_holds,
   omitReduced_holds, omitSelfMover_holds, omitMoverPrior_holds, omitIdle_holds,
   omitTwoConstituents_holds, omitMatterFormConstituents_holds,
   omitEsseEssenceConstituents_holds,
   omitConsistsInBeing_holds, omitCausingRespect_holds,
   omitCauseOfBeing_holds, omitNecessityInAct_holds, omitCausingNecessity_holds,
   omitFollows_holds, omitSomeIntellect_holds, omitMaximal_holds,
   omitOccursProd_holds, omitBearerProd_holds, omitExerciseProd_holds, omitProduction_holds,
   omitExistsProd_holds, omitCauserConcrete_holds,
   omitOccursPow_holds, omitBearerPow_holds, omitExercisePow_holds, omitExerciserPower_holds,
   omitExistsPow_holds, omitPowerConcrete_holds,
   omitLinkAnalysis_holds, omitMoverEfficient_holds, omitSecondWay_holds, witness_holds⟩

end Controls

end TruthCore.Results.Causality.Round4Revisited
