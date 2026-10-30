import TruthCore.Models.TemporalHistoryControls

namespace TruthCore.Results.Modal.TemporalHistoryControls
open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Models.TemporalHistoryControls

/-- The two explicit coherent history controls separate temporal perpetuity,
beginning, modal status and actual causal/grounding dependence. -/
theorem controls : TruthCore.Models.TemporalHistoryControls.JointControls := by
  have hEverCoherent : CoherentAtNow everlasting := fun _ _ => Iff.rfl
  have hEver : EverlastingAt everlasting false (false, true) := fun _ => rfl
  have hCont : ContingentAt everlasting.ontic false (false, true) :=
    boundaryRivalAllContingent false (false, true) rfl
  have hDependent : ∃ y, y ≠ (false, true) ∧ boundaryRival.concrete y ∧
      everlasting.ontic.ExistsAt false y ∧
      everlasting.ontic.Causes false y (false, true) ∧
      boundaryRival.grounds false y (false, true) :=
    ⟨(false, false), (by decide), trivial, rfl,
      ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
  have hBeginCoherent : CoherentAtNow beginning := by
    intro w x
    change (x = false) ↔ (x = false ∧ (0 : Int) ≤ 0)
    exact ⟨fun hx => ⟨hx, le_rfl⟩, fun h => h.1⟩
  have hBegins : BeginsAt beginning false false 0 := by
    refine ⟨⟨rfl, le_rfl⟩, ?_⟩
    intro s hs hPresent
    exact (not_le_of_gt hs) hPresent.2
  have hNecessary : NecessaryAt beginning.ontic false false := fun _ _ => rfl
  have hNotContingent : ¬ ContingentAt beginning.ontic false false := by
    rintro ⟨_, v, hv, hn⟩
    exact hn (hNecessary v hv)
  exact ⟨hEverCoherent, hEver, hCont, hDependent,
    hBeginCoherent, hBegins, hNecessary, hNotContingent⟩

end TruthCore.Results.Modal.TemporalHistoryControls
