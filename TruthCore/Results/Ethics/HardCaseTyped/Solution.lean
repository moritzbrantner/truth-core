import TruthCore.Ethics.HardCaseTyped
namespace TruthCore.Results.Ethics.HardCaseTyped
open TruthCore.Ethics.HardCaseTyped TruthCore.Modal.DeonticFutureBoundary

def facts : Facts where
  feasible := fun c a => (c = .violation ∧ a = .violate) ∨ (c = .killing ∧ a = .kill) ∨ (c = .conflict ∧ (a = .keepPromise ∨ a = .preventHarm))
  actor := fun _ => .offender
  target := fun _ => .victim
  nonconsensual := fun c a => c = .violation ∧ a = .violate
  deliberateKilling := fun c a => c = .killing ∧ a = .kill
  innocent := fun c p => c = .killing ∧ p = .victim
  nonthreatening := fun c p => c = .killing ∧ p = .victim
  indifferent := fun p => p = .offender
  benefits := fun c p a => p = .offender ∧ ((c = .violation ∧ a = .violate) ∨ (c = .killing ∧ a = .kill))
  unpunished := fun c p a => p = .offender ∧ ((c = .violation ∧ a = .violate) ∨ (c = .killing ∧ a = .kill))
  realizes := fun c a g => c = .conflict ∧ ((a = .keepPromise ∧ g = .promiseKeeping) ∨ (a = .preventHarm ∧ g = .harmPrevention))
  recognized := fun c g => c = .conflict ∧ (g = .promiseKeeping ∨ g = .harmPrevention)

def yes : Verdict := ⟨fun c a => (c = .violation ∧ a = .violate) ∨ (c = .killing ∧ a = .kill), fun _ _ _ => True⟩
def no : Verdict := ⟨fun _ _ => False, fun _ _ _ => False⟩
def withoutReason : Verdict := ⟨yes.forbidden, fun _ _ _ => False⟩

theorem certificate : TruthCore.Ethics.HardCaseTyped.Certificate := by
  constructor
  · refine ⟨facts, yes, no, yes, withoutReason, ?_⟩
    dsimp [HardCases, facts, yes, no, withoutReason]
    repeat' apply And.intro
    all_goals decide
  · refine ⟨facts, ⟨fun _ a => a = .keepPromise⟩, ⟨fun _ a => a = .preventHarm⟩, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (dsimp [facts]; decide)
    · exact ⟨.keepPromise, rfl, Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)⟩
    · exact ⟨.preventHarm, rfl, Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)⟩
    · intro _ h; exact h
    · intro _ h; exact h
end TruthCore.Results.Ethics.HardCaseTyped
