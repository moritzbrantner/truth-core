import TruthCore.Isabelle.AFP.GoedelGod
namespace TruthCore.Results.Isabelle.GoedelGod.EmptyPropertyNotEssence
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod

/-- An essence in Scott's sense is had by its bearer (the first conjunct of
`ess`), and nothing has the empty property. -/
theorem emptyPropertyNotEssence {World : Type} {Ind : Type} (F : Frame World) :
    EmptyPropertyNotEssence F Ind :=
  fun _ _ hEssence => hEssence.1
end TruthCore.Results.Isabelle.GoedelGod.EmptyPropertyNotEssence
