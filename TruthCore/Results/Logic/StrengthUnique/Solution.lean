import TruthCore.Logic.Strength.UniqueExistence
namespace TruthCore.Results.Logic.StrengthUnique
open TruthCore.Logic.Strength.UniqueExistence
universe u

theorem implication {α : Type u} (P : α → Prop) (hS : Unique P) : TruthCore.Logic.Strength.UniqueExistence.Exists P := by
  obtain ⟨x, hx, _⟩ := hS
  exact ⟨x, hx⟩

theorem deltaForward {α : Type u} (P : α → Prop) (hS : Unique P) : AtMostOne P := by
  obtain ⟨w, _, hw⟩ := hS
  intro x y hx hy
  exact (hw x hx).trans (hw y hy).symm

theorem reconstruction {α : Type u} (P : α → Prop) (hW : TruthCore.Logic.Strength.UniqueExistence.Exists P) (hD : AtMostOne P) : Unique P := by
  obtain ⟨x, hx⟩ := hW
  exact ⟨x, hx, fun y hy => hD y x hy hx⟩

theorem equivalence : ExactDelta := by
  intro α P
  exact ⟨fun h => ⟨implication P h, deltaForward P h⟩,
    fun h => reconstruction P h.1 h.2⟩

theorem separator : TwoPointsSeparate := by
  refine ⟨True.intro, ⟨false, True.intro⟩, ?_⟩
  rintro ⟨w, _, hw⟩
  have h0 := hw false True.intro
  have h1 := hw true True.intro
  exact Bool.noConfusion (h0.trans h1.symm)
end TruthCore.Results.Logic.StrengthUnique
