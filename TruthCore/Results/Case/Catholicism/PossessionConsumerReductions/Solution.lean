module

public import TruthCore.Case.Catholicism.PossessionConsumerReductions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.PossessionConsumerReductions
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Logic

theorem nothingMovesExceptInAct {B R : Type} (MovesIn CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (PartOf : B → B → Prop)
    (hEM : ExcludedMiddle)
    (hCause : MoverCausesWhatItMovesTo MovesIn CausesIn)
    (hHas : DistinctCauseHasWhatItGives CausesIn InAct)
    (hSelf : SelfMoverMovesByADistinctPart MovesIn PartOf)
    (hWhole : WholeInActThroughItsPart PartOf InAct) :
    MovesOnlyAsInActReading MovesIn InAct := by
  have distinct : ∀ y x r, y ≠ x → MovesIn y x r → InAct y r :=
    fun y x r hne hm => hHas y x r hne (hCause y x r hm)
  intro y x r hm
  rcases hEM (y = x) with hyx | hne
  · subst hyx
    obtain ⟨p, hp, hpne, hpm⟩ := hSelf y r hm
    exact hWhole p y r hp (distinct p y r hpne hpm)
  · exact distinct y x r hne hm

theorem gradesHaveAMaximum {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (hBearer : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hCause : DistinctCauseHasWhatItGives CausesIn InAct)
    (hExceeded : ExceededPerfectionIsCausedReading InAct MoreIn CausesIn)
    (hRegress : NoInfiniteRegressOfCausesOfAPerfectionReading CausesIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GradesByApproachToAMaximumReading InAct MoreIn := by
  intro r ⟨x, y, hxy⟩
  have key : ∀ z, InAct z r → ∃ m, IsMaximumIn InAct MoreIn r m := by
    intro z
    refine (hRegress r).induction (C := fun z => InAct z r → ∃ m, IsMaximumIn InAct MoreIn r m)
      z ?_
    intro z ih hz
    rcases hEM (∃ w, MoreIn r w z) with ⟨w, hw⟩ | hNo
    · obtain ⟨c, hne, hc⟩ := hExceeded r z w hz hw
      exact ih c ⟨hne, hc⟩ (hCause c z r hne hc)
    · exact ⟨z, hz, fun w hw => hNo ⟨w, hw⟩⟩
  exact key x (hBearer r x y hxy)

end TruthCore.Results.Case.Catholicism.PossessionConsumerReductions
