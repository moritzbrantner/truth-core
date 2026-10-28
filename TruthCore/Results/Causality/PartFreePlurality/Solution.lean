import TruthCore.Causality.PartFreePlurality

namespace TruthCore.Results.Causality.PartFreePlurality
open TruthCore.Causality.PartFreePlurality
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

theorem leftFirst : IsFirstUnmovedMover moved moves .left :=
  ⟨⟨.instrument, .drive, trivial⟩, by intro r; cases r <;> exact (fun h => h)⟩

theorem rightFirst : IsFirstUnmovedMover moved moves .right :=
  ⟨⟨.instrument, .drive, trivial⟩, by intro r; cases r <;> exact (fun h => h)⟩

theorem firstIsRoot (x : Being) (h : IsFirstUnmovedMover moved moves x) : root x := by
  cases x with
  | left => trivial
  | right => trivial
  | constituent => exact (h.2 .drive trivial).elim
  | instrument => exact (h.2 .drive trivial).elim
  | effect => exact (h.2 .heat trivial).elim

theorem firstBeing : FirstUnmovedMoverIsFirstBeing moved moves prior := by
  intro x hx y hy
  have hr := firstIsRoot x hx
  cases x with
  | left => exact (Nat.not_lt_zero _ hy).elim
  | right => exact (Nat.not_lt_zero _ hy).elim
  | constituent => exact hr.elim
  | instrument => exact hr.elim
  | effect => exact hr.elim

theorem noBody : NoBodyMovesUnlessMovedReading moved moves body := by
  intro x hb _
  cases x with
  | left => exact (Nat.lt_irrefl 0 hb).elim
  | right => exact (Nat.lt_irrefl 0 hb).elim
  | constituent => exact ⟨.drive, trivial⟩
  | instrument => exact ⟨.drive, trivial⟩
  | effect => exact ⟨.heat, trivial⟩

theorem compositeInstrument : composite .instrument :=
  ⟨.constituent, ⟨by decide, by change 1 < 2; decide⟩, Being.noConfusion⟩

theorem compositeEffect : composite .effect :=
  ⟨.instrument, ⟨by decide, by change 2 < 3; decide⟩, Being.noConfusion⟩

theorem kinds : MatterFormAndEsseEssenceAreCompositionsReading
    matterForm composite essence esse := by
  intro x
  cases x with
  | left => exact ⟨fun h => (Nat.not_lt_zero 1 h).elim, fun h => (h rfl).elim⟩
  | right => exact ⟨fun h => (Nat.not_lt_zero 1 h).elim, fun h => (h rfl).elim⟩
  | constituent => exact ⟨fun h => (Nat.lt_irrefl 1 h).elim, fun h => (h rfl).elim⟩
  | instrument => exact ⟨fun _ => compositeInstrument, fun _ => compositeInstrument⟩
  | effect => exact ⟨fun _ => compositeEffect, fun _ => compositeEffect⟩

theorem notBoth : NotActAndPotencyInSameRespectReading inAct moved := by
  intro x r h
  cases x <;> cases r <;> first | exact h.1 | exact h.2

theorem actPrior : ActSimplyPriorToPotencyReading inAct moved prior := by
  intro x r hp
  refine ⟨.left, trivial, ?_⟩
  cases x with
  | left => cases r <;> exact hp.elim
  | right => cases r <;> exact hp.elim
  | constituent => change 0 < 1; decide
  | instrument => change 0 < 2; decide
  | effect => change 0 < 3; decide

theorem perfect : FirstUnmovedMoverHasEveryPerfection moved moves inAct := by
  intro x hx r
  have hr := firstIsRoot x hx
  cases x with
  | left => trivial
  | right => trivial
  | constituent => exact hr.elim
  | instrument => exact hr.elim
  | effect => exact hr.elim

theorem differentOrSame : FirstUnmovedMoversIdenticalOrDistinct moved moves := by
  intro x y _ _
  exact if h : x = y then Or.inl h else Or.inr h

theorem notUnique : ¬ AtMostOneFirstUnmovedMover moved moves := by
  intro h
  exact Being.noConfusion (h .left .right leftFirst rightFirst)

theorem ontology : OntologyControl := by
  refine ⟨(fun _ _ => trivial), (fun _ _ => trivial),
    (fun _ _ => trivial), (fun _ _ => trivial), ?_, ?_, ?_, ?_, ?_,
    (fun _ => ⟨by change 0 < 2; decide, by change 0 < 2; decide, by change 2 < 3; decide⟩),
    (fun _ _ _ _ => trivial), (fun _ x _ => ⟨.intrinsic x, rfl⟩),
    (fun _ _ => rfl), (fun y x _ => ⟨by cases y <;> trivial, by cases x <;> trivial⟩),
    ⟨trivial, Being.noConfusion⟩, ⟨trivial, Being.noConfusion⟩,
    ?_, (fun _ _ h => h)⟩
  · exact ⟨(fun _ _ _ _ => ⟨trivial, trivial⟩),
      (fun _ _ _ _ => ⟨trivial, trivial⟩),
      (fun _ _ _ _ => ⟨trivial, trivial⟩),
      (fun _ _ _ h => h), (fun _ _ _ h => h)⟩
  · exact ⟨trivial, trivial, fun y h => Nat.not_lt_zero (rank y) h⟩
  · exact ⟨trivial, trivial, fun y h => Nat.not_lt_zero (rank y) h⟩
  · intro _ ⟨y, _, _, h⟩
    exact Nat.not_lt_zero (rank y) h
  · intro _ ⟨y, _, _, h⟩
    exact Nat.not_lt_zero (rank y) h
  · intro x hd
    cases x with
    | left => exact (hd.2 rfl).elim
    | right => exact (hd.2 rfl).elim
    | constituent => exact (hd.2 rfl).elim
    | instrument => exact Or.inr ⟨.left, Being.noConfusion, trivial, by change 0 < 2; decide⟩
    | effect => exact Or.inr ⟨.left, Being.noConfusion, trivial, by change 0 < 3; decide⟩

theorem simplicity : SimplicityControl := by
  have hMoves : MovesOnlyAsInActReading moves inAct := by
    intro y x r hm
    cases y <;> cases x <;> cases r <;>
      first | exact hm.elim | exact trivial
  have hReduced : ReducedOnlyByAMoverReading moved moves := by
    intro x r hm
    cases x <;> cases r <;> first
      | exact hm.elim
      | exact ⟨.left, trivial⟩
      | exact ⟨.instrument, trivial⟩
  have hSecond : SecondMoversMoveOnlyAsMovedReading moved moves asMoved := by
    intro y x r _ hm ⟨r', hy⟩
    cases y <;> cases x <;> cases r <;> cases r' <;>
      first | exact hm.elim | exact hy.elim | exact trivial
  have hNo : NoInfinitePerSeMoverSeriesReading asMoved := by
    have hRank : ∀ y x, asMoved y x → rank y < rank x := by
      intro y x h
      cases y <;> cases x <;> first | exact h.elim | decide
    exact (Subrelation.wf (fun h => hRank _ _ h) (InvImage.wf rank Nat.lt_wfRel.wf)).apply
  have hPosterior : CompositePosteriorToComponentsReading component prior :=
    fun _ _ h => h.2
  have hOther : CompositeHasComponentOtherThanItselfReading composite component :=
    fun _ h => h
  refine ⟨⟨.instrument, .drive, trivial⟩, (fun _ _ h => h), hMoves, hReduced,
    notBoth, hSecond, hNo, actPrior, firstBeing, noBody, hPosterior, hOther, kinds,
    ?_, ?_, perfect, leftFirst, rightFirst, trivial, compositeInstrument, compositeEffect⟩
  · exact TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple.firstMoverSimple
      moved moves prior component body matterForm composite essence esse
      noBody firstBeing hPosterior hOther kinds
  · exact TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.firstMoverPureAct
      moved moves moved inAct prior firstBeing actPrior notBoth

theorem uniqueness : UniquenessControl := by
  have hIndividual : IndividuatingBasisIsIncommunicableReading suppositum :=
    fun _ _ h => h
  have hNature : GodSuppositumIsNatureReading root suppositum essence := by
    intro x hx
    cases x with
    | left => rfl
    | right => rfl
    | constituent => exact hx.elim
    | instrument => exact hx.elim
    | effect => exact hx.elim
  refine ⟨Being.noConfusion, notUnique, hIndividual, hNature, ?_, ?_⟩
  · intro deity hCommon
    have hOne := TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.godIsOneFromNature
      root suppositum essence deity hIndividual hNature hCommon
    exact Being.noConfusion (hOne .left trivial .right trivial)
  · intro hDiffer
    exact notUnique (TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.oneFirstMover
      moved moves inAct perfect hDiffer differentOrSame)

theorem noComponentFirst : NoComponentIsFirstBeingReading component prior := by
  intro p x hp hfirst
  have hroot : prior .left p := hp.1
  have heq := hfirst .left hroot
  subst p
  exact Nat.lt_irrefl 0 hp.1

theorem rootsPartFree : ∀ x, ¬ component .left x ∧ ¬ component .right x := by
  intro x
  exact ⟨fun h => Nat.lt_irrefl 0 h.1, fun h => Nat.lt_irrefl 0 h.1⟩

theorem unitingCause : CompositeHasAUnitingCauseReading composite esseProfile.CausesIn TruthCore.Causality.NecessarySimplePlurality.Respect.esse := by
  intro x ⟨p, hp, hne⟩
  exact ⟨p, hne, hp.2⟩

theorem jointControl : JointControl :=
  ⟨ontology, simplicity, uniqueness, noComponentFirst, rootsPartFree, unitingCause⟩

end TruthCore.Results.Causality.PartFreePlurality
