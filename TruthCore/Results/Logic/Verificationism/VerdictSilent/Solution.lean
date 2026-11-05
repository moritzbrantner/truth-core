module

public import TruthCore.Logic.Verificationism

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.VerdictSilent
open TruthCore.Logic.Verificationism

/-- Two-coordinate language: a world fixes an observable and an unobservable
Boolean coordinate; sentences are their truth functions on worlds. -/
def twoCoordinate : Language where
  Sentence := Bool × Bool → Bool
  World := Bool × Bool
  holds w s := s w = true
  neg s w := !s w
  conj s t w := s w && t w
  disj s t w := s w || t w
  holds_neg w s := by
    show (!s w) = true ↔ ¬ s w = true
    generalize s w = b; cases b <;> decide
  holds_conj w s t := by
    show (s w && t w) = true ↔ (s w = true ∧ t w = true)
    generalize s w = b; generalize t w = c; cases b <;> cases c <;> decide
  holds_disj w s t := by
    show (s w || t w) = true ↔ (s w = true ∨ t w = true)
    generalize s w = b; generalize t w = c; cases b <;> cases c <;> decide

/-- Observation statements depend only on the observable coordinate; analytic
sentences are true at every world. -/
def observableFrame : Frame twoCoordinate where
  observation s := ∀ a b c, s (a, b) = s (a, c)
  analytic s := ∀ w, s w = true

/-- A criterion's verdict settles nothing about truth: some sentence that is neither analytic nor conclusively verifiable is true at a world of a language with an observation statement. -/
theorem criterionVerdictSilentOnTruth : CriterionVerdictSilentOnTruth := by
  refine ⟨twoCoordinate, observableFrame, fun w => w.2, (false, true),
    ⟨fun w => w.1, fun _ _ _ => rfl⟩, ?_, ?_, rfl⟩
  · intro h; exact Bool.noConfusion (h (false, false))
  · intro ⟨os, hobs, ⟨w0, hw0⟩, hent⟩
    have h1 : ∀ g, g ∈ os → twoCoordinate.holds (w0.1, false) g := by
      intro g hg
      show g (w0.1, false) = true
      rw [hobs g hg w0.1 false w0.2]
      exact hw0 g hg
    exact Bool.noConfusion (hent (w0.1, false) h1)
end TruthCore.Results.Logic.Verificationism.VerdictSilent
