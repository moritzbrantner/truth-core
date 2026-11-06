module

public import TruthCore.Mereology.ActualFusionProfile
public import TruthCore.Results.Mereology.AtomlessFusionProfile.Solution
public import TruthCore.Results.Mereology.SumOneComplementation.Solution

@[expose] public section
namespace TruthCore.Results.Mereology.ActualFusionProfile
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.ActualFusionProfile
open TruthCore.German.Kant.CosmologicalInference

private theorem noNecessary (w x : Body) : ¬ NecessaryAt model w x := by
  intro hn
  obtain ⟨b, hb⟩ := x.property
  have hf : b = false := hn (atom false) trivial hb
  have ht : b = true := hn (atom true) trivial hb
  exact Bool.noConfusion (hf.symm.trans ht)

theorem checks : Certificate := by
  have old := TruthCore.Results.Mereology.AtomlessFusionProfile.atomicModel
  refine ⟨old, ?_, ?_, ?_, ?_, ?_, noNecessary, ?_, ?_, ?_, ?_⟩
  · intro _ _; trivial
  · intro w; exact ⟨w, le_refl w⟩
  · intro x; exact ⟨x, le_refl x⟩
  · intro w x p hx hp
    exact hp.trans hx
  · intro w family hn ha
    obtain ⟨u, hu⟩ := old.2.1.2.2 family hn
    have hlub :=
      (TruthCore.Results.Mereology.SumOneComplementation.sumOneComparison
        Body old.2.1.1 family hn u).mpr hu
    exact ⟨u, hu, hlub.2 ha⟩
  · rintro w ⟨x, _, hx⟩
    exact noNecessary w x hx
  · intro w
    exact ⟨w, le_refl w, fun _ hx => hx⟩
  · rintro ⟨u, hu⟩
    exact noNecessary whole u (fun v _ => hu v)
  · refine ⟨atom false, atom false, ?_, le_refl _, ?_⟩
    · intro _ _; trivial
    · intro h
      have bad : true ∈ (atom false).val := h (show true ∈ whole.val from trivial)
      exact Bool.noConfusion (Set.mem_singleton_iff.mp bad)

end TruthCore.Results.Mereology.ActualFusionProfile
