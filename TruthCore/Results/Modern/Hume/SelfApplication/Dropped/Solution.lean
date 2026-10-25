import TruthCore.Modern.Hume.SelfApplication
namespace TruthCore.Results.Modern.Hume.SelfApplication.Dropped
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability
open TruthCore.Modern.Hume.SelfApplication

private theorem middleBridge (C : Conception ChainWorld)
    (h : ∀ P, ¬ C P .middle) : StrongBridge chain C .middle := by
  intro P hc
  exact (h P hc).elim

private theorem lastFailure : ¬ StrongBridge chain chainConception .last := by
  intro h
  obtain ⟨_, _, hf⟩ := h (fun _ => False) True.intro
  exact hf

theorem checks : DroppedPremiseModels := by
  have hm : StrongBridge chain chainConception .middle :=
    middleBridge chainConception (fun _ h => h)
  have hu : StrongBridge chain unsoundRoot .middle :=
    middleBridge unsoundRoot (fun _ h => h)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w
    cases w with
    | root => exact ⟨.middle, True.intro⟩
    | middle => exact ⟨.last, True.intro⟩
    | last => exact ⟨.last, True.intro⟩
  · intro h
    exact h .root .middle .last True.intro True.intro
  · intro P hp
    exact ⟨.middle, True.intro, hp⟩
  · intro v hv
    cases v with
    | root => exact hv.elim
    | middle => exact hm
    | last => exact hv.elim
  · intro v hv
    cases v with
    | root => exact hv.elim
    | middle => exact hv.elim
    | last => exact lastFailure
  · exact True.intro
  · intro h
    obtain ⟨v, hv, hn⟩ := h
    cases v with
    | root => exact hv.elim
    | middle => exact hn hu
    | last => exact hv.elim
  · intro h
    obtain ⟨_, _, hf⟩ := h (fun _ => False) True.intro
    exact hf
end TruthCore.Results.Modern.Hume.SelfApplication.Dropped
