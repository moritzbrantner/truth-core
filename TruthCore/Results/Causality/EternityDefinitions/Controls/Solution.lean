module

public import TruthCore.Causality.EternityDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EternityDefinitions.Controls
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.EternityDefinitionFork

/-- Frozen analyst consequence; no semantic calibration or actual-life premise adopted. -/
theorem controls : Controls := by
  have interminable (l : Unit → Bool → Prop) (h : ∀ x t, l x t) :
      ∀ x, Interminable l x := by
    intro x hh
    obtain ⟨t, s, _, hn⟩ := hh
    exact hn ⟨fun _ => h x s, fun _ => h x t⟩
  have successiveFails : ¬ BoethianEternal successive.LivesAt successive.lifeStateAt () := by
    intro h
    exact h.2.2 ⟨false, true, by change ((!false && true) = true); rfl, True.intro, True.intro, Bool.noConfusion⟩
  have stableEternal : ∀ x, BoethianEternal unrecognized.LivesAt unrecognized.lifeStateAt x := by
    intro x
    refine ⟨⟨false, True.intro⟩, interminable _ (fun _ _ => True.intro) x, ?_⟩
    intro h
    obtain ⟨t, s, _, _, _, hn⟩ := h
    exact hn rfl
  refine ⟨⟨?_, ?_, ?_, successiveFails⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x
    constructor
    · intro _; exact ⟨⟨false, True.intro⟩, interminable _ (fun _ _ => True.intro) x⟩
    · intro _; exact True.intro
  · intro h; exact successiveFails ((h ()).mp True.intro)
  · exact ⟨⟨false, True.intro⟩, interminable _ (fun _ _ => True.intro) ()⟩
  · intro x _; exact True.intro
  · intro h; exact successiveFails ((h ()).mp True.intro)
  · intro x hh
    obtain ⟨t, s, _, _, _, hn⟩ := hh
    exact False.elim (hn rfl)
  · intro x hh
    obtain ⟨t, s, _, hn⟩ := hh
    exact False.elim (hn ⟨fun _ => True.intro, fun _ => True.intro⟩)
  · intro x _; exact ⟨false, True.intro⟩
  · intro r h; exact h
  · intro h; exact h () (fun _ hp => hp)
  · intro x; exact ⟨fun _ => stableEternal x, fun _ => True.intro⟩
  · intro x
    exact ⟨fun _ => ⟨⟨false, True.intro⟩, interminable _ (fun _ _ => True.intro) x⟩,
      fun _ => True.intro⟩
  · intro h
    obtain ⟨⟨t, ht⟩, _, _⟩ := (h ()).mp True.intro
    exact ht
  · intro h
    obtain ⟨⟨t, ht⟩, _⟩ := (h ()).mp True.intro
    exact ht

end TruthCore.Results.Causality.EternityDefinitions.Controls
