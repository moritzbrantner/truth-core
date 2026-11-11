module

public import TruthCore.Causality.ToleranceOriginRival
public import TruthCore.Causality.SpineRivalsStageOne

@[expose] public section

namespace TruthCore.Results.Causality.ToleranceOriginRival
open TruthCore.Causality.ToleranceOriginRival
open TruthCore.Causality.ToleranceOriginRival.Control
open TruthCore.Causality.SpineRivalsStageOne (ReflexiveNonEuclidean)

/-- Strength order: the tolerance rival at any world gives the stepwise rival's
global statement on the same frame. -/
theorem toleranceReflexiveNonEuclidean {W : Type} (frame : TruthCore.Modal.Frame W) (w : W)
    (hTolerance : ToleranceNonEuclideanAt frame w) : ReflexiveNonEuclidean frame :=
  ⟨hTolerance.1, w, hTolerance.2.2⟩

/-- The tolerance omission model and its closure reading, by case analysis. -/
theorem controls : Control.Certificate := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro a; cases a <;> simp [tolerance]
  · intro a b; cases a <;> cases b <;> simp [tolerance]
  · exact ⟨Origin.minus, Origin.plus, by simp [tolerance], by simp [tolerance], by simp [tolerance]⟩
  · simp [TruthCore.Causality.NecessarilyUnderived.ActualReflexive, toleranceHistory, tolerance]
  · intro hE
    have h := hE Origin.minus Origin.plus (by simp [tolerance]) (by simp [tolerance])
    simp [tolerance] at h
  · intro v x t hp
    rcases hp with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨hx.1, hx.2.1⟩
  · intro v s t _ hEmpty
    cases v
    · intro x _ hx
      simp [toleranceHistory] at hx
    · exact absurd (Or.inl ⟨rfl, by simp⟩) (hEmpty false trivial)
    · exact absurd (Or.inl ⟨rfl, by simp⟩) (hEmpty false trivial)
  · refine ⟨Origin.plus, by simp [toleranceHistory, tolerance], 0, 1, Nat.zero_lt_one, ?_,
      true, trivial, ⟨Or.inr ⟨rfl, rfl⟩, Origin.actual, by simp [toleranceHistory, tolerance], ?_⟩,
      Or.inr ⟨rfl, rfl, rfl⟩⟩
    · intro x _ hCont hxs
      rcases hxs with hx | hx
      · obtain ⟨_, u, hu, hAbsent⟩ := hCont
        rw [hx.1] at hAbsent
        cases u <;> simp [toleranceHistory, tolerance] at hu hAbsent
      · exact absurd hx.2.2 (by decide)
    · simp [toleranceHistory]
  · rintro ⟨c, _, _, hNec⟩
    have h := hNec Origin.minus (by simp [toleranceHistory, tolerance])
    cases c <;> simp [toleranceHistory] at h
  · intro _ _ _ _; trivial
  · rintro ⟨v, _, s, t, _, hFree, x, _, ⟨hxv, _⟩, hxt⟩
    -- `false` exists at v, so v ≠ minus; it is contingent there (absent at minus)
    -- and present at s, contradicting freedom from contingents at s.
    have hv : v ≠ Origin.minus := by
      intro hv; subst hv; cases x <;> simp [chainedHistory, toleranceHistory] at hxv
    apply hFree false trivial
    · exact ⟨Or.inl ⟨rfl, hv⟩, Origin.minus, trivial, by simp [chainedHistory, toleranceHistory]⟩
    · exact Or.inl ⟨rfl, hv⟩
  · rintro ⟨c, _, _, hNec⟩
    have h := hNec Origin.minus trivial
    cases c <;> simp [chainedHistory, toleranceHistory] at h

end TruthCore.Results.Causality.ToleranceOriginRival
