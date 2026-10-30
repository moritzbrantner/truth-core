import TruthCore.Models.FiniteSupport
import TruthCore.Results.Alternatives.GenerationFromNightRefuted.Solution

/-! One joint moving survivor of the Night elimination. Three beings share one
respect: `idle` is in potency with no actual being simply prior to it; `moved`
is in potency and is being moved by the actual `mover`, which is simply prior
to `moved`. Thus the bare potency-priority rival survives all four root-core
commitments together with present motion. This strengthens the nonmoving
Residual control without joining facts from separate interpretations.

This finite interpretation certifies satisfiability of the predicates only.
`idle` is not being moved at this evaluation; no assertion of permanent rest,
metaphysical possibility, or truth of the bare rival follows. The stronger
Night commitment fails, and global act-priority still fails. -/
namespace TruthCore.Models.NightMovingResidual
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.NightCosmogony

inductive Being where
  | idle | moved | mover
  deriving DecidableEq

structure Model where
  InAct : Being → Unit → Prop
  InPotency : Being → Unit → Prop
  MovedIn : Being → Unit → Prop
  MovesIn : Being → Being → Unit → Prop
  PriorSimply : Being → Being → Prop

def model : Model where
  InAct := fun x _ => x = .mover
  InPotency := fun x _ => x ≠ .mover
  MovedIn := fun x _ => x = .moved
  MovesIn := fun y x _ => y = .mover ∧ x = .moved
  PriorSimply := fun y x => y = .mover ∧ x = .moved

theorem enumerateBeing : ∀ x : Being,
    x = .idle ∨ x = .moved ∨ x = .mover := by
  intro x
  cases x
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem evaluation0 :
    PotencyPriorToActReading model.InAct model.InPotency model.PriorSimply := by
  refine ⟨.idle, (), ?_, ?_⟩
  · intro h
    cases h
  · intro y hAct hPrior
    cases hPrior.2

theorem evaluation1 : ReducedOnlyByAMoverReading model.MovedIn model.MovesIn :=
  fun _ _ h => ⟨.mover, rfl, h⟩

theorem evaluation2 : MovesOnlyAsInActReading model.MovesIn model.InAct :=
  fun _ _ _ h => h.1

theorem evaluation3 :
    NotActAndPotencyInSameRespectReading model.InAct model.InPotency :=
  fun _ _ h => h.2 h.1

theorem evaluation4 :
    ActualMoverIsSimplyPriorReading model.InAct model.InPotency
      model.MovesIn model.PriorSimply :=
  fun _ _ _ _ h _ _ => h

theorem evaluation5 : SomethingIsMovedReading model.MovedIn :=
  ⟨.moved, (), rfl⟩

theorem evaluation6 : ¬ UnprecededPotencyActualizedReading
    model.InAct model.InPotency model.MovedIn model.PriorSimply :=
  TruthCore.Results.Alternatives.GenerationFromNightRefuted.coreFromRootPremises
    Being Unit model.InAct model.InPotency model.MovedIn model.MovesIn model.PriorSimply
    evaluation1 evaluation2 evaluation3 evaluation4

theorem evaluation7 :
    ¬ ActSimplyPriorToPotencyReading model.InAct model.InPotency model.PriorSimply := by
  intro h
  have hIdle : model.InPotency .idle () := by intro h; cases h
  obtain ⟨y, hAct, hPrior⟩ := h .idle () hIdle
  cases hPrior.2

/-- Explicit idle witness, at this evaluation only. The other potency `moved`
is simultaneously being moved, as evaluation5 certifies in this same model. -/
theorem idleWitness : ∃ x r, model.InPotency x r ∧
    (∀ y, model.InAct y r → ¬ model.PriorSimply y x) ∧ ¬ model.MovedIn x r := by
  refine ⟨.idle, (), ?_, ?_, ?_⟩
  · intro h
    cases h
  · intro y hAct hPrior
    cases hPrior.2
  · intro h
    cases h

end TruthCore.Models.NightMovingResidual
