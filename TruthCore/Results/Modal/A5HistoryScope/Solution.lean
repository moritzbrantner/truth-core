module

public import TruthCore.Modal.A5HistoryScope

@[expose] public section

namespace TruthCore.Results.Modal.A5HistoryScope
open TruthCore.Modal.A5HistoryScope
open TruthCore.Modal.A5HistoryScope.Controls
open TruthCore.Modal.TemporalHistory

private theorem discreteNonvacuityChecked : discreteNonvacuity := by
  unfold discreteNonvacuity
  simp only [PopulationFirst, MemberFirst, BeginsAt, PopulationPredecessor,
    MemberPredecessor, onset, history]
  refine ⟨⟨⟨false, trivial, by omega⟩, ?_⟩,
    ⟨trivial, by omega, ?_⟩, ⟨⟨false, trivial, by omega⟩, -1, by omega, ?_, ?_⟩,
    trivial, by omega, -1, by omega, ?_, by omega⟩ <;>
    intros <;> (try simp_all) <;> omega


private theorem denseSeparationChecked : denseSeparation := by
  unfold denseSeparation
  constructor
  · exact ⟨⟨false, trivial, le_refl _⟩, fun s hs ⟨_, _, hb⟩ => (not_le_of_gt hs) hb⟩
  · rintro ⟨_, s, hs, hgap, _⟩
    exact hgap (s / 2) (by linarith) (by linarith)


private theorem firstMomentSeparationChecked : firstMomentSeparation := by
  unfold firstMomentSeparation
  exact ⟨⟨⟨false, trivial, trivial⟩, fun _ => Nat.not_lt_zero _⟩,
    ⟨trivial, trivial, fun _ => Nat.not_lt_zero _⟩,
    fun ⟨_, s, hs, _⟩ => Nat.not_lt_zero s hs⟩


private theorem memberNotPopulationChecked : memberNotPopulation := by
  unfold memberNotPopulation
  constructor
  · exact ⟨trivial, Or.inr (le_refl _), fun s hs h => h.elim Bool.noConfusion (not_le_of_gt hs)⟩
  · intro h
    exact h.2 (-1) (by decide) ⟨false, trivial, Or.inl rfl⟩


private theorem predecessorNotFirstChecked : predecessorNotFirst := by
  unfold predecessorNotFirst
  constructor
  · refine ⟨⟨false, trivial, Or.inl rfl⟩, -1, by omega, ?_, ?_⟩
    · intros; omega
    · rintro ⟨_, _, h⟩; change (-1 : Int) = 0 ∨ (-1 : Int) = -2 at h; omega
  · intro h
    exact h.2 (-2) (by decide) ⟨false, trivial, Or.inr rfl⟩


private theorem rosterControlsChecked : rosterControls := by
  unfold rosterControls
  simp [RigidEverRoster, onset, history]
  exact ⟨0, le_refl _⟩


private theorem classificationSeparationChecked : classificationSeparation := by
  unfold classificationSeparation
  simp [RigidEverRoster, EvaluatedEverRoster, onset, history]
  exact ⟨0, le_refl _⟩


private theorem cutoffSeparationChecked : cutoffSeparation := by
  unfold cutoffSeparation
  simp [RigidEverRoster, EvaluatedPastRoster, history]

private theorem rigidPastControlsChecked : rigidPastControls := by
  unfold rigidPastControls
  simp [RigidPastRoster, RigidEverRoster, onset, history]
  exact ⟨0, le_refl _, le_refl _⟩

theorem controls : ControlSuite := by
  exact ⟨discreteNonvacuityChecked, denseSeparationChecked, firstMomentSeparationChecked, memberNotPopulationChecked, predecessorNotFirstChecked, rosterControlsChecked, classificationSeparationChecked, cutoffSeparationChecked,
    rigidPastControlsChecked⟩

end TruthCore.Results.Modal.A5HistoryScope
