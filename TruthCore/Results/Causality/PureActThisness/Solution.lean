module

public import TruthCore.Causality.PureActThisness
public import TruthCore.Results.Causality.RootMultiplication.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PureActThisness
open TruthCore.Case.Catholicism
open TruthCore.Causality.PureActThisness

/-- Unrestricted perfection and strict pure actuality leave only bare plurality:
any two first movers have exactly the same real determinations. Neither a
different perfection nor a non-pure individuating, receiving or limiting
principle can distinguish them. No first mover is produced. -/
theorem pureActPluralityIsBare {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure) :
    FirstMoversReallyIndiscernible Moved Moves Has :=
  fun f g hf hg d =>
    ⟨fun h => hEvery g hg d (hPure f hf d h), fun h => hEvery f hf d (hPure g hg d h)⟩

/-- A real thisness of a first mover is a pure perfection under strict pure
actuality: what makes it this one is an actuality, not an added principle. -/
theorem thisnessIsPure {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hThis : FirstMoverHasRealThisness Moved Moves Has) (f : B)
    (hf : IsFirstUnmovedMover Moved Moves f) :
    ∃ d, Pure d ∧ Has f d ∧ ∀ y, Has y d → y = f :=
  let ⟨d, hd, honly⟩ := hThis f hf
  ⟨d, hPure f hf d hd, hd, honly⟩

/-- If each first mover has a real thisness, strict pure actuality makes that
thisness a pure perfection and unrestricted perfection gives it to every first
mover, so there is at most one. Conditional on three OPEN premises. -/
theorem uniqueFromRealThisness {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hThis : FirstMoverHasRealThisness Moved Moves Has) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  intro f g hf hg
  obtain ⟨d, hd, _, honly⟩ := thisnessIsPure Moved Moves Has Pure hPure hThis f hf
  exact (honly g (hEvery g hg d hd)).symm

/-- Bare plurality excluded by identity of real indiscernibles over all beings.
Conditional on three OPEN premises; the third denies bare numerical difference
everywhere, not only among first movers. -/
theorem uniqueFromRealIndividuation {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hIndividuate : RealDeterminationsIndividuate Has) :
    AtMostOneFirstUnmovedMover Moved Moves :=
  fun f g hf hg => hIndividuate f g (pureActPluralityIsBare Moved Moves Has Pure hEvery hPure f g hf hg)

/-- The existing every-perfection reading is the case in which every respect is
a real determination and a pure perfection. Under that reading strict pure
actuality holds trivially, so it adds nothing to the existing route. -/
theorem everyPerfectionIsAllPureCase {B R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (InAct : B → R → Prop) :
    FirstUnmovedMoverHasEveryPerfection Moved Moves InAct ↔
      FirstMoverHasEveryPureDetermination Moved Moves InAct (fun _ => True) :=
  ⟨fun h f hf d _ => h f hf d, fun h f hf d => h f hf d trivial⟩

section Controls
open TruthCore.Causality.PureActThisness.Control
open TruthCore.Causality.PartFreePlurality
open TruthCore.Results.Causality.PartFreePlurality (leftFirst rightFirst perfect notUnique)
open TruthCore.Results.Causality.RootMultiplication (onlyG gFirst)

theorem bareRival :
    FirstMoverHasEveryPureDetermination moved moves actHas allPure ∧
    FirstMoverDeterminationsArePure moved moves actHas allPure ∧
    BarelyDistinctFirstMovers moved moves actHas ∧
    ¬ FirstMoverHasRealThisness moved moves actHas ∧
    ¬ RealDeterminationsIndividuate actHas ∧
    ¬ AtMostOneFirstUnmovedMover moved moves := by
  have hEvery : FirstMoverHasEveryPureDetermination moved moves actHas allPure :=
    (everyPerfectionIsAllPureCase moved moves inAct).1 perfect
  have hPure : FirstMoverDeterminationsArePure moved moves actHas allPure :=
    fun _ _ _ _ => trivial
  exact ⟨hEvery, hPure,
    ⟨.left, .right, leftFirst, rightFirst, (fun e => nomatch e),
      pureActPluralityIsBare moved moves actHas allPure hEvery hPure _ _ leftFirst rightFirst⟩,
    fun h => notUnique (uniqueFromRealThisness moved moves actHas allPure hEvery hPure h),
    fun h => notUnique (uniqueFromRealIndividuation moved moves actHas allPure hEvery hPure h),
    notUnique⟩

theorem thisReal : FirstMoverHasRealThisness moved moves thisHas :=
  fun f _ => ⟨.inr f, rfl, fun _ hy => hy⟩

theorem thisIndividuates : RealDeterminationsIndividuate thisHas :=
  fun x _ h => ((h (.inr x)).1 rfl).symm

theorem thisDiscernible : ¬ FirstMoversReallyIndiscernible moved moves thisHas :=
  fun h => nomatch ((h .left .right leftFirst rightFirst (.inr .left)).1 rfl)

theorem withoutStrictPurity :
    FirstMoverHasEveryPureDetermination moved moves thisHas actOnly ∧
    ¬ FirstMoverDeterminationsArePure moved moves thisHas actOnly ∧
    FirstMoverHasRealThisness moved moves thisHas ∧
    RealDeterminationsIndividuate thisHas ∧
    ¬ FirstMoversReallyIndiscernible moved moves thisHas ∧
    ¬ AtMostOneFirstUnmovedMover moved moves := by
  refine ⟨?_, fun h => h .left leftFirst (.inr .left) rfl, thisReal, thisIndividuates,
    thisDiscernible, notUnique⟩
  intro f hf d hd
  cases d with
  | inl r => exact perfect f hf r
  | inr _ => exact hd.elim

theorem withoutUnrestrictedPerfection :
    ¬ FirstMoverHasEveryPureDetermination moved moves thisHas everyPure ∧
    FirstMoverDeterminationsArePure moved moves thisHas everyPure ∧
    FirstMoverHasRealThisness moved moves thisHas ∧
    RealDeterminationsIndividuate thisHas ∧
    ¬ FirstMoversReallyIndiscernible moved moves thisHas ∧
    ¬ AtMostOneFirstUnmovedMover moved moves :=
  ⟨fun h => (nomatch (h .left leftFirst (.inr .right) trivial)),
    fun _ _ _ _ => trivial, thisReal, thisIndividuates, thisDiscernible, notUnique⟩

theorem individuationExceedsUniqueness :
    FirstMoverHasEveryPureDetermination jMoved jMoves onlyGHas (fun _ => True) ∧
    FirstMoverDeterminationsArePure jMoved jMoves onlyGHas (fun _ => True) ∧
    FirstMoverHasRealThisness jMoved jMoves onlyGHas ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    ¬ RealDeterminationsIndividuate onlyGHas :=
  ⟨fun a ha _ _ => onlyG a ha, fun _ _ _ _ => trivial,
    fun a ha => ⟨(), onlyG a ha, fun _ hy => hy.trans (onlyG a ha).symm⟩,
    fun a b ha hb => (onlyG a ha).trans (onlyG b hb).symm,
    fun h => (nomatch (h .f .x fun _ => ⟨(fun e => nomatch e), (fun e => nomatch e)⟩))⟩

theorem thisnessNotUniqueness :
    FirstMoverHasEveryPureDetermination jMoved jMoves (fun (_ : JB) (_ : Empty) => False)
      (fun _ => True) ∧
    FirstMoverDeterminationsArePure jMoved jMoves (fun (_ : JB) (_ : Empty) => False)
      (fun _ => True) ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    IsFirstUnmovedMover jMoved jMoves (.g : JB) ∧
    ¬ FirstMoverHasRealThisness jMoved jMoves (fun (_ : JB) (_ : Empty) => False) :=
  ⟨(fun _ _ d _ => nomatch d), (fun _ _ d _ => nomatch d),
    fun a b ha hb => (onlyG a ha).trans (onlyG b hb).symm, gFirst,
    fun h => (let ⟨d, _⟩ := h .g gFirst; nomatch d)⟩

theorem positiveWitness :
    FirstMoverHasEveryPureDetermination jMoved jMoves individuatedHas unitPure ∧
    FirstMoverDeterminationsArePure jMoved jMoves individuatedHas unitPure ∧
    FirstMoverHasRealThisness jMoved jMoves individuatedHas ∧
    RealDeterminationsIndividuate individuatedHas ∧
    IsFirstUnmovedMover jMoved jMoves (.g : JB) := by
  refine ⟨?_, ?_, fun a ha => ⟨.inr (), onlyG a ha, fun _ hy => hy.trans (onlyG a ha).symm⟩,
    ?_, gFirst⟩
  · intro a ha d hd
    cases d with
    | inl _ => exact hd.elim
    | inr _ => exact onlyG a ha
  · intro a ha d hd
    cases d with
    | inl _ => exact (hd.2 (onlyG a ha)).elim
    | inr _ => trivial
  · intro a b h
    cases a with
    | g => exact ((h (.inr ())).1 rfl).symm
    | f => exact ((h (.inl .f)).1 ⟨rfl, fun e => nomatch e⟩).1.symm
    | x => exact ((h (.inl .x)).1 ⟨rfl, fun e => nomatch e⟩).1.symm
    | c => exact ((h (.inl .c)).1 ⟨rfl, fun e => nomatch e⟩).1.symm

end Controls

theorem controls : TruthCore.Causality.PureActThisness.Control.Certificate :=
  ⟨bareRival, withoutStrictPurity, withoutUnrestrictedPerfection,
    individuationExceedsUniqueness, thisnessNotUniqueness, positiveWitness⟩

end TruthCore.Results.Causality.PureActThisness
