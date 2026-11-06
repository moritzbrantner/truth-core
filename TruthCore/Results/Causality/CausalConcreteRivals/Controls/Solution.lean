module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.Controls
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem controls : Controls := by
  have hAnchor : Anchored base := ⟨⟨Role.reasoner, Role.anchor, True.intro, fun h => h⟩⟩
  have hBase : OwnerCommitmentAt base.ontic base.concrete base.power base.selected := by
    constructor
    · intro x hx
      cases hx
      trivial
    · intro x y hc
      cases hc.1
      trivial
  have hElse : OwnerCommitmentAt elsewhere.ontic elsewhere.concrete elsewhere.power elsewhere.selected := by
    constructor
    · exact hBase.1
    · intro x y hc
      rcases hc with h | ⟨h, _⟩
      · exact hBase.2 x y h
      · cases h
  have hElseNo : ¬ SelectedCounter elsewhere := by
    rintro ⟨x, hn, hp | ⟨y, hc⟩⟩
    · exact hn (hElse.1 x hp)
    · exact hn (hElse.2 x y hc)
  have hOther : OtherCounter dormant := by
    constructor
    · exact ⟨Role.fact, fun h => h, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    · intro h
      have : SelectedCounter elsewhere := by
        rcases h with ⟨x, y, _, hn, hc⟩ | ⟨x, y, _, hn, hc⟩ | ⟨x, y, _, _, hn, hc⟩
        all_goals exact ⟨x, hn, Or.inr ⟨y, hc⟩⟩
      exact hElseNo this
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ => Iff.rfl, hAnchor, hBase, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨.producer, .effect, Or.inr rfl, rfl, rfl⟩
    · exact ⟨.producer, .effect, rfl, rfl, rfl⟩
    · exact ⟨.fact, .effect, rfl, rfl, rfl⟩
    · intro h
      exact h .producer .effect (Or.inr rfl) ⟨rfl, rfl⟩ True.intro
    · intro h
      exact h .producer .effect rfl ⟨rfl, rfl⟩ True.intro
    · intro h
      have := (h .fact .effect rfl ⟨rfl, rfl⟩).1
      cases this
  · exact ⟨fun _ => Iff.rfl, hAnchor, ⟨true, .fact, fun h => h,
      Or.inr ⟨.effect, Or.inr ⟨rfl, rfl, rfl⟩⟩⟩, hElse, hElseNo⟩
  · refine ⟨fun _ => Iff.rfl, hAnchor, hOther, ?_, hElse.2,
      Or.inr ⟨rfl, rfl⟩, True.intro, Or.inr ⟨rfl, rfl, rfl⟩⟩
    intro h
    exact h.1 .fact (Or.inr ⟨rfl, rfl⟩)

end TruthCore.Results.Causality.CausalConcreteRivals.Controls
