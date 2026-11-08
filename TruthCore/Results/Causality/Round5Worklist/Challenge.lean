import TruthCore.Causality.Round5Worklist

namespace TruthCore.Results.Causality.Round5Worklist
open TruthCore.Causality.Round5Worklist
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism.StageOne.CausalFinitism
open TruthCore.Causality.FiniteBranching
open TruthCore.Alternatives.ActPotencyRegress (SimplePriorityTransitiveReading)
open TruthCore.Greek.Aristotle.Physics (FourCauseExhaustiveReading)
open TruthCore.Causality.CausalMapsBatch1 (PriorityRequiresNonmutualDependence)
open TruthCore.Case.Catholicism (SimplyPriorIsCauseOfBeing)
open TruthCore.Causality.SelfOperationLife
open TruthCore.Causality.LifeBoundaryPotency
open TruthCore.Causality.SuccessionPotency
open TruthCore.Causality.IntellectualInclination

/-! ## Map 1: causal history and priority -/

/-- Every causal path is a chain of simple priorities (each edge is an efficient
causing, efficient causes are simply prior, priority is transitive), so a loop
would make something prior to itself. Induction on the path. -/
theorem noLoopsFromPriority {B R : Type} (cause : B → B → Prop)
    (EfficientlyCausesIn : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (hEdges : HistoryEdgesAreEfficientCausings cause EfficientlyCausesIn)
    (hPrior : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
    (hTrans : SimplePriorityTransitiveReading PriorSimply)
    (hIrrefl : NothingPriorToItselfReading PriorSimply) :
    NoCausalLoops cause := by
  sorry

/-- The causal relation is contained in simple priority, and a subrelation of a
well-founded relation is well-founded. -/
theorem wellFoundedFromPriority {B R : Type} (cause : B → B → Prop)
    (EfficientlyCausesIn : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (hEdges : HistoryEdgesAreEfficientCausings cause EfficientlyCausesIn)
    (hPrior : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
    (hWF : SimplePriorityWellFounded PriorSimply) :
    WellFoundedPredecessors cause := by
  sorry

/-- The direct causes of `x` lie in the union of its causes in the four modes,
a union of four finite sets. -/
theorem finitePredecessorsFromModes {B : Type} (cause : B → B → Prop)
    (Material Formal SourceOfChange Final : B → B → Prop)
    (hFour : FourCauseExhaustiveReading cause Material Formal SourceOfChange Final)
    (hFinite : FinitelyManyCausesPerMode Material Formal SourceOfChange Final) :
    FiniteImmediatePredecessors cause := by
  sorry

/-- What is simply prior to `x` is something `x` depends on for its being (first
half of the dependence reading of priority), and what a thing depends on for its
being causes its being. -/
theorem simplyPriorCausesBeing {B R : Type} (PriorSimply DependsForBeing : B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPriority : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing)
    (hDependence : DependenceForBeingIsCausedBeing DependsForBeing CausesIn esse) :
    SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse := by
  sorry

/-! ## Map 2: life, operation and change -/

/-- A pure act is not in potency in being, so it is in act in being; it then has
an operation, which is either from itself or comes with its being moved; being
moved needs potency, which it lacks. -/
theorem pureActOperatesFromBeing {B R O : Type} (InAct InPotency MovedIn : B → R → Prop)
    (Operates : B → Prop) (OperationOf : O → B → Prop) (esse : R)
    (hDivision : ActOrPotencyInBeing InAct InPotency esse)
    (hOperation : BeingInActHasOperation InAct OperationOf esse)
    (hSelfOrMoved : OperationFromSelfOrAsMoved OperationOf Operates MovedIn)
    (hMoved : MovedOnlyAsInPotencyReading MovedIn InPotency) :
    PureActOperates InPotency Operates := by
  sorry

/-- A self-operation is present at some time, and operating from itself at a time
is living at it. The unmoved clause of the conclusion is not used: under these
premises every self-operating thing lives. -/
theorem selfOperatingUnmovedLivesFromOperation {B R T : Type} (Operates : B → Prop)
    (MovedIn : B → R → Prop) (OperatesFromItselfAt LivesAt : B → T → Prop)
    (hPresent : SelfOperationPresentAtSomeTime Operates OperatesFromItselfAt)
    (hLiving : OperatingFromItselfIsLiving OperatesFromItselfAt LivesAt) :
    SelfOperatingUnmovedLives Operates MovedIn LivesAt := by
  sorry

/-- A life boundary between two times is a change in some respect, and a change
in a respect is potency in it; a pure act has none. -/
theorem noLifeBoundaryFromChange {B R T : Type} [LT T] (InPotency : B → R → Prop)
    (LivesAt : B → T → Prop) (ChangesBetween : B → R → T → T → Prop)
    (hBoundary : LifeBoundaryIsChange LivesAt ChangesBetween)
    (hChange : ChangeRequiresPotencyInSubject ChangesBetween InPotency) :
    ImmutableHasNoLifeBoundary InPotency LivesAt := by
  sorry

/-- A succession of life-states is a change between two times at both of which
the thing lives, and such a change of a persisting subject is a motion. -/
theorem successionMotionFromChange {B R T S : Type} [LT T] (LivesAt : B → T → Prop)
    (lifeStateAt : B → T → S) (MovedIn : B → R → Prop)
    (ChangesBetween : B → R → T → T → Prop)
    (hState : StateDifferenceIsChange lifeStateAt ChangesBetween)
    (hMotion : ChangeOfPersistingSubjectIsMotion LivesAt ChangesBetween MovedIn) :
    SuccessionIsBeingMoved LivesAt lifeStateAt MovedIn := by
  sorry

/-! ## Map 3: will from intelligible form -/

/-- Each form is the principle of an operation, the operation is for an end, and
operating through a form toward an end is an inclination following the form. -/
theorem everyFormInclinedFromFinality {B F O E : Type} (HasForm InclinedTo : B → F → Prop)
    (OperatesThrough : B → F → O → Prop) (DirectedTo : O → E → Prop)
    (hPrinciple : FormIsPrincipleOfOperation HasForm OperatesThrough)
    (hFinality : EveryOperationHasAnEnd OperatesThrough DirectedTo)
    (hInclination : EndDirectedOperationIsInclination OperatesThrough DirectedTo InclinedTo) :
    EveryFormHasInclination HasForm InclinedTo := by
  sorry

/-- An intellect understands something, and to understand is to be in act through
an intelligible form. -/
theorem intellectFormFromUnderstanding {B F Q : Type} (HasIntellect : B → Prop)
    (HasForm : B → F → Prop) (Intelligible : F → Prop) (Understands : B → Q → Prop)
    (hUnderstands : IntellectUnderstandsSomething HasIntellect Understands)
    (hThrough : UnderstandingIsThroughIntelligibleForm Understands HasForm Intelligible) :
    IntellectHasIntelligibleForm HasIntellect HasForm Intelligible := by
  sorry

/-- An inclination following an intelligible form belongs to an appetitive
principle following intellect, and such a principle is will. -/
theorem willFromIntellectualAppetite {B F P : Type} (Intelligible : F → Prop)
    (InclinedTo : B → F → Prop) (HasWill : B → Prop) (AppetitivePowerOf : P → B → Prop)
    (FollowsIntellect : P → Prop)
    (hAppetite : IntelligibleInclinationIsIntellectualAppetite Intelligible InclinedTo
      AppetitivePowerOf FollowsIntellect)
    (hWill : IntellectualAppetiteIsWill AppetitivePowerOf FollowsIntellect HasWill) :
    IntelligibleInclinationIsWill Intelligible InclinedTo HasWill := by
  sorry

/-! ## Controls -/

open TruthCore.Causality.Round5Worklist.Control

macro "ctrl" : tactic => `(tactic| (
  delta HistoryEdgesAreEfficientCausings EfficientCauseIsPriorToEffectReading
    SimplePriorityTransitiveReading NothingPriorToItselfReading
    PriorityRequiresNonmutualDependence DependenceForBeingIsCausedBeing SimplyPriorIsCauseOfBeing
    ActOrPotencyInBeing BeingInActHasOperation OperationFromSelfOrAsMoved
    MovedOnlyAsInPotencyReading PureActOperates PureAct SelfOperationPresentAtSomeTime
    OperatingFromItselfIsLiving SelfOperatingUnmovedLives LifeBoundaryIsChange
    ChangeRequiresPotencyInSubject ImmutableHasNoLifeBoundary LifeBeginsOrEnds
    StateDifferenceIsChange ChangeOfPersistingSubjectIsMotion SuccessionIsBeingMoved
    LifeHasSuccession FormIsPrincipleOfOperation EveryOperationHasAnEnd
    EndDirectedOperationIsInclination EveryFormHasInclination IntellectUnderstandsSomething
    UnderstandingIsThroughIntelligibleForm IntellectHasIntelligibleForm
    IntelligibleInclinationIsIntellectualAppetite IntellectualAppetiteIsWill
    IntelligibleInclinationIsWill t2 f2 t3 f3 neB downB begins livesB stateB
  decide))

/-- The batch controls: one omission model per premise of each of the eleven
derivations and one joint nonvacuity witness per map. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.Round5Worklist
