import TruthCore.Modal.OptimalCreationChoice
namespace TruthCore.Results.Modal.OptimalCreationChoice
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.OptimalCreationChoice
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Results.Modal.SelectedEffectBridge

theorem uniqueOptimalStable {W B A V : Type} [PartialOrder V]
    (p : OutputProfile W B A) (w : W) (a : A) (feasible : Set B) (quality : B → V)
    (h : OptimalOutputs p w a feasible quality)
    (unique : ∀ x y, Optimal feasible quality x → Optimal feasible quality y → x = y) :
    StableActOutput p w a := by
  intro x hx v hv hp
  obtain ⟨y, hy⟩ := (h v (Or.inr hv)).1 hp
  have heq := unique x y ((h w (Or.inl rfl)).2 x hx) ((h v (Or.inr hv)).2 y hy)
  exact heq ▸ hy

theorem noOptimalWhenImprovable {B V : Type} [PartialOrder V]
    (feasible : Set B) (quality : B → V) (h : StrictlyImprovable feasible quality) :
    ¬ ∃ x, Optimal feasible quality x := by
  rintro ⟨x, hx, hmax⟩
  obtain ⟨y, hy, hlt⟩ := h x hx
  exact (not_le_of_gt hlt) (hmax.2 ⟨y, hy, rfl⟩)

theorem tiedOptimal (b : Bool) : Optimal tiedCandidates tiedQuality (some b) := by
  refine ⟨⟨b, rfl⟩, ⟨⟨some b, ⟨b, rfl⟩, rfl⟩, ?_⟩⟩
  rintro _ ⟨y, _, rfl⟩
  exact Nat.le_refl 0

theorem checks : OptimalChoiceCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B A V inst p w a feasible quality h hu
    exact uniqueOptimalStable p w a feasible quality h hu
  · intro W B A V inst p w a x feasible quality h hu hs hr ha hx
    exact selectedEffectNecessary p w a x hs hr ha
      (uniqueOptimalStable p w a feasible quality h hu) hx
  · intro B V inst feasible quality h
    exact noOptimalWhenImprovable feasible quality h
  · intro B V inst feasible quality x y hx hy
    exact le_antisymm (hy.2.2 ⟨x, hx.1, rfl⟩) (hx.2.2 ⟨y, hy.1, rfl⟩)
  · intro x _
    exact ⟨x + 1, Set.mem_univ _, Nat.lt_succ_self x⟩
  · refine ⟨?_, tiedOptimal false, tiedOptimal true, ?_, varyingChecks.2.2.2.2.1,
      varyingChecks.2.2.2.2.2.2.1, varyingChecks.2.2.2.2.2.2.2.2.2⟩
    · intro v _
      constructor
      · intro _
        exact ⟨some v, rfl⟩
      · intro x hx
        rw [hx]
        exact tiedOptimal v
    · intro h
      cases h
end TruthCore.Results.Modal.OptimalCreationChoice
