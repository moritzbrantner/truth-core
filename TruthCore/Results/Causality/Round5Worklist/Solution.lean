module

public import TruthCore.Causality.Round5Worklist

@[expose] public section

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
  have hPath : ∀ y x, Relation.TransGen cause y x → PriorSimply y x := by
    intro y x hyx
    induction hyx with
    | single hc =>
      obtain ⟨r, hr⟩ := hEdges _ _ hc
      exact hPrior _ _ r hr
    | tail _ hc ih =>
      obtain ⟨r, hr⟩ := hEdges _ _ hc
      exact hTrans _ _ _ ih (hPrior _ _ r hr)
  intro x hx
  exact hIrrefl x (hPath x x hx)

/-- The causal relation is contained in simple priority, and a subrelation of a
well-founded relation is well-founded. -/
theorem wellFoundedFromPriority {B R : Type} (cause : B → B → Prop)
    (EfficientlyCausesIn : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (hEdges : HistoryEdgesAreEfficientCausings cause EfficientlyCausesIn)
    (hPrior : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
    (hWF : SimplePriorityWellFounded PriorSimply) :
    WellFoundedPredecessors cause := by
  have hSub : Subrelation cause PriorSimply := by
    intro y x hc
    obtain ⟨r, hr⟩ := hEdges y x hc
    exact hPrior y x r hr
  exact Subrelation.wf hSub hWF

/-- The direct causes of `x` lie in the union of its causes in the four modes,
a union of four finite sets. -/
theorem finitePredecessorsFromModes {B : Type} (cause : B → B → Prop)
    (Material Formal SourceOfChange Final : B → B → Prop)
    (hFour : FourCauseExhaustiveReading cause Material Formal SourceOfChange Final)
    (hFinite : FinitelyManyCausesPerMode Material Formal SourceOfChange Final) :
    FiniteImmediatePredecessors cause := by
  intro x
  obtain ⟨hM, hF, hS, hE⟩ := hFinite x
  refine (((hM.union hF).union hS).union hE).subset ?_
  intro y hy
  rcases hFour y x hy with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- What is simply prior to `x` is something `x` depends on for its being (first
half of the dependence reading of priority), and what a thing depends on for its
being causes its being. -/
theorem simplyPriorCausesBeing {B R : Type} (PriorSimply DependsForBeing : B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPriority : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing)
    (hDependence : DependenceForBeingIsCausedBeing DependsForBeing CausesIn esse) :
    SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse := by
  intro y x hyx
  obtain ⟨hDepends, _⟩ := hPriority y x hyx
  exact hDependence x y hDepends

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
  intro x hx
  have hAct : InAct x esse := (hDivision x).resolve_right (hx esse)
  obtain ⟨o, ho⟩ := hOperation x hAct
  rcases hSelfOrMoved o x ho with hSelf | ⟨r, hr⟩
  · exact hSelf
  · exact absurd (hMoved x r hr) (hx r)

/-- A self-operation is present at some time, and operating from itself at a time
is living at it. The unmoved clause of the conclusion is not used: under these
premises every self-operating thing lives. -/
theorem selfOperatingUnmovedLivesFromOperation {B R T : Type} (Operates : B → Prop)
    (MovedIn : B → R → Prop) (OperatesFromItselfAt LivesAt : B → T → Prop)
    (hPresent : SelfOperationPresentAtSomeTime Operates OperatesFromItselfAt)
    (hLiving : OperatingFromItselfIsLiving OperatesFromItselfAt LivesAt) :
    SelfOperatingUnmovedLives Operates MovedIn LivesAt := by
  intro x hx _
  obtain ⟨t, ht⟩ := hPresent x hx
  exact ⟨t, hLiving x t ht⟩

/-- A life boundary between two times is a change in some respect, and a change
in a respect is potency in it; a pure act has none. -/
theorem noLifeBoundaryFromChange {B R T : Type} [LT T] (InPotency : B → R → Prop)
    (LivesAt : B → T → Prop) (ChangesBetween : B → R → T → T → Prop)
    (hBoundary : LifeBoundaryIsChange LivesAt ChangesBetween)
    (hChange : ChangeRequiresPotencyInSubject ChangesBetween InPotency) :
    ImmutableHasNoLifeBoundary InPotency LivesAt := by
  intro x hx ⟨t₁, t₂, hlt, hne⟩
  obtain ⟨r, hr⟩ := hBoundary x t₁ t₂ hlt hne
  exact hx r (hChange x r t₁ t₂ hr)

/-- A succession of life-states is a change between two times at both of which
the thing lives, and such a change of a persisting subject is a motion. -/
theorem successionMotionFromChange {B R T S : Type} [LT T] (LivesAt : B → T → Prop)
    (lifeStateAt : B → T → S) (MovedIn : B → R → Prop)
    (ChangesBetween : B → R → T → T → Prop)
    (hState : StateDifferenceIsChange lifeStateAt ChangesBetween)
    (hMotion : ChangeOfPersistingSubjectIsMotion LivesAt ChangesBetween MovedIn) :
    SuccessionIsBeingMoved LivesAt lifeStateAt MovedIn := by
  intro x ⟨t₁, t₂, hlt, h₁, h₂, hne⟩
  obtain ⟨r, hr⟩ := hState x t₁ t₂ hlt hne
  exact ⟨r, hMotion x r t₁ t₂ hr h₁ h₂⟩

/-! ## Map 3: will from intelligible form -/

/-- Each form is the principle of an operation, the operation is for an end, and
operating through a form toward an end is an inclination following the form. -/
theorem everyFormInclinedFromFinality {B F O E : Type} (HasForm InclinedTo : B → F → Prop)
    (OperatesThrough : B → F → O → Prop) (DirectedTo : O → E → Prop)
    (hPrinciple : FormIsPrincipleOfOperation HasForm OperatesThrough)
    (hFinality : EveryOperationHasAnEnd OperatesThrough DirectedTo)
    (hInclination : EndDirectedOperationIsInclination OperatesThrough DirectedTo InclinedTo) :
    EveryFormHasInclination HasForm InclinedTo := by
  intro x f hf
  obtain ⟨o, ho⟩ := hPrinciple x f hf
  obtain ⟨e, he⟩ := hFinality x f o ho
  exact hInclination x f o e ho he

/-- An intellect understands something, and to understand is to be in act through
an intelligible form. -/
theorem intellectFormFromUnderstanding {B F Q : Type} (HasIntellect : B → Prop)
    (HasForm : B → F → Prop) (Intelligible : F → Prop) (Understands : B → Q → Prop)
    (hUnderstands : IntellectUnderstandsSomething HasIntellect Understands)
    (hThrough : UnderstandingIsThroughIntelligibleForm Understands HasForm Intelligible) :
    IntellectHasIntelligibleForm HasIntellect HasForm Intelligible := by
  intro x hx
  obtain ⟨q, hq⟩ := hUnderstands x hx
  exact hThrough x q hq

/-- An inclination following an intelligible form belongs to an appetitive
principle following intellect, and such a principle is will. -/
theorem willFromIntellectualAppetite {B F P : Type} (Intelligible : F → Prop)
    (InclinedTo : B → F → Prop) (HasWill : B → Prop) (AppetitivePowerOf : P → B → Prop)
    (FollowsIntellect : P → Prop)
    (hAppetite : IntelligibleInclinationIsIntellectualAppetite Intelligible InclinedTo
      AppetitivePowerOf FollowsIntellect)
    (hWill : IntellectualAppetiteIsWill AppetitivePowerOf FollowsIntellect HasWill) :
    IntelligibleInclinationIsWill Intelligible InclinedTo HasWill := by
  intro x f hf hx
  obtain ⟨p, hp, hFollows⟩ := hAppetite x f hf hx
  exact hWill p x hp hFollows

/-! ## Controls -/

section Controls
open TruthCore.Causality.Round5Worklist.Control

/-- A relation with a reflexive edge is not well-founded. -/
theorem not_wf_of_self {α : Type} {r : α → α → Prop} (a : α) (h : r a a) :
    ¬ WellFounded r := fun hw => (hw.apply a).rec
  (motive := fun x _ => r x x → False) (fun x _ ih hx => ih x hx hx) h

theorem wf_false {α : Type} : WellFounded (fun (_ _ : α) => False) :=
  ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩

theorem wf_downB : WellFounded downB := by
  have hf : Acc downB false := ⟨false, fun y h => by cases h.2⟩
  refine ⟨fun x => ?_⟩
  cases x with
  | false => exact hf
  | true =>
    refine ⟨true, fun y h => ?_⟩
    rw [h.1]
    exact hf

theorem loop_t2 : ¬ NoCausalLoops t2 := fun h => h () (Relation.TransGen.single trivial)

theorem not_finite_nat : ¬ FiniteImmediatePredecessors (fun (_ _ : ℕ) => True) := by
  intro h
  exact Set.infinite_univ (h 0)

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

theorem omitEdgesLoops_holds : omitEdgesLoops := by
  refine ⟨by ctrl, by ctrl, by ctrl, by ctrl, loop_t2⟩
theorem omitPriorLoops_holds : omitPriorLoops := by
  refine ⟨by ctrl, by ctrl, by ctrl, by ctrl, loop_t2⟩
theorem omitTransLoops_holds : omitTransLoops := by
  refine ⟨by ctrl, by ctrl, by ctrl, by ctrl, fun h => h false ?_⟩
  exact Relation.TransGen.tail (Relation.TransGen.single (b := true) (show false ≠ true by decide))
    (show true ≠ false by decide)
theorem omitIrreflLoops_holds : omitIrreflLoops := by
  refine ⟨by ctrl, by ctrl, by ctrl, by ctrl, loop_t2⟩
theorem omitEdgesWF_holds : omitEdgesWF :=
  ⟨by ctrl, by ctrl, wf_false, not_wf_of_self () trivial⟩
theorem omitPriorWF_holds : omitPriorWF :=
  ⟨by ctrl, by ctrl, wf_false, not_wf_of_self () trivial⟩
theorem omitWFPriority_holds : omitWFPriority :=
  ⟨by ctrl, by ctrl, not_wf_of_self () trivial, not_wf_of_self () trivial⟩
theorem omitFourModes_holds : omitFourModes := by
  refine ⟨fun h => ?_, fun _ => ?_, not_finite_nat⟩
  · rcases h 0 0 trivial with h | h | h | h <;> exact h
  · simp only [Set.setOf_false, Set.finite_empty, and_self]
theorem omitFinitePerMode_holds : omitFinitePerMode := by
  refine ⟨fun _ _ _ => Or.inl trivial, fun h => ?_, not_finite_nat⟩
  exact Set.infinite_univ (h 0).1
theorem omitPriorityDependence_holds : omitPriorityDependence := by
  refine ⟨by ctrl, by ctrl, by ctrl⟩
theorem omitDependenceCausation_holds : omitDependenceCausation := by
  refine ⟨by ctrl, by ctrl, by ctrl⟩

theorem witnessHistory_holds : witnessHistory := by
  have hEdges : HistoryEdgesAreEfficientCausings downB
      (fun (y x : Bool) (_ : Unit) => downB y x) := by ctrl
  have hPrior : EfficientCauseIsPriorToEffectReading
      (fun (y x : Bool) (_ : Unit) => downB y x) downB := by ctrl
  have hTrans : SimplePriorityTransitiveReading downB := by ctrl
  have hIrrefl : NothingPriorToItselfReading downB := by ctrl
  have hFour : FourCauseExhaustiveReading downB (fun _ _ => False) (fun _ _ => False) downB
      (fun _ _ => False) := fun _ _ h => Or.inr (Or.inr (Or.inl h))
  have hFinite : FinitelyManyCausesPerMode (fun (_ _ : Bool) => False) (fun _ _ => False) downB
      (fun _ _ => False) := fun _ => ⟨Set.toFinite _, Set.toFinite _, Set.toFinite _,
        Set.toFinite _⟩
  have hPriority : PriorityRequiresNonmutualDependence downB (fun x y => downB y x) := by ctrl
  have hDependence : DependenceForBeingIsCausedBeing (fun x y => downB y x)
      (fun (y x : Bool) (_ : Unit) => downB y x) () := by ctrl
  exact ⟨hEdges, hPrior, hTrans, hIrrefl, wf_downB, hFour, hFinite, hPriority, hDependence,
    noLoopsFromPriority _ _ _ hEdges hPrior hTrans hIrrefl,
    wellFoundedFromPriority _ _ _ hEdges hPrior wf_downB,
    finitePredecessorsFromModes _ _ _ _ _ hFour hFinite,
    simplyPriorCausesBeing _ _ _ _ hPriority hDependence, ⟨rfl, rfl⟩⟩

theorem omitDivision_holds : omitDivision := by delta omitDivision; ctrl
theorem omitOperationFollows_holds : omitOperationFollows := by delta omitOperationFollows; ctrl
theorem omitSelfOrMoved_holds : omitSelfOrMoved := by delta omitSelfOrMoved; ctrl
theorem omitMovedPotency_holds : omitMovedPotency := by delta omitMovedPotency; ctrl
theorem omitPresent_holds : omitPresent := by delta omitPresent; ctrl
theorem omitLiving_holds : omitLiving := by delta omitLiving; ctrl
theorem omitBoundaryChange_holds : omitBoundaryChange := by delta omitBoundaryChange; ctrl
theorem omitChangePotency_holds : omitChangePotency := by delta omitChangePotency; ctrl
theorem omitStateChange_holds : omitStateChange := by delta omitStateChange; ctrl
theorem omitPersistingMotion_holds : omitPersistingMotion := by delta omitPersistingMotion; ctrl
theorem witnessLife_holds : witnessLife := by
  delta witnessLife
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ctrl
theorem omitFormPrinciple_holds : omitFormPrinciple := by delta omitFormPrinciple; ctrl
theorem omitFinality_holds : omitFinality := by delta omitFinality; ctrl
theorem omitEndInclination_holds : omitEndInclination := by delta omitEndInclination; ctrl
theorem omitUnderstandsSomething_holds : omitUnderstandsSomething := by
  delta omitUnderstandsSomething; ctrl
theorem omitThroughForm_holds : omitThroughForm := by delta omitThroughForm; ctrl
theorem omitAppetite_holds : omitAppetite := by delta omitAppetite; ctrl
theorem omitAppetiteWill_holds : omitAppetiteWill := by delta omitAppetiteWill; ctrl
theorem witnessWill_holds : witnessWill := by delta witnessWill; ctrl

/-- The batch controls: one omission model per premise of each of the eleven
derivations and one joint nonvacuity witness per map. -/
theorem controls : Certificate :=
  ⟨omitEdgesLoops_holds, omitPriorLoops_holds, omitTransLoops_holds, omitIrreflLoops_holds,
   omitEdgesWF_holds, omitPriorWF_holds, omitWFPriority_holds,
   omitFourModes_holds, omitFinitePerMode_holds,
   omitPriorityDependence_holds, omitDependenceCausation_holds, witnessHistory_holds,
   omitDivision_holds, omitOperationFollows_holds, omitSelfOrMoved_holds, omitMovedPotency_holds,
   omitPresent_holds, omitLiving_holds, omitBoundaryChange_holds, omitChangePotency_holds,
   omitStateChange_holds, omitPersistingMotion_holds, witnessLife_holds,
   omitFormPrinciple_holds, omitFinality_holds, omitEndInclination_holds,
   omitUnderstandsSomething_holds, omitThroughForm_holds, omitAppetite_holds,
   omitAppetiteWill_holds, witnessWill_holds⟩

end Controls

end TruthCore.Results.Causality.Round5Worklist
