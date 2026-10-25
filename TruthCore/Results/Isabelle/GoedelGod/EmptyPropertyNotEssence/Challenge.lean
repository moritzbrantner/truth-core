import TruthCore.Isabelle.AFP.GoedelGod
namespace TruthCore.Results.Isabelle.GoedelGod.EmptyPropertyNotEssence
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod
/-- Scott's essence (AFP `GoedelGod.thy`, definition `ess`): the empty property
is an essence of no individual at any world, from the definition alone. -/
theorem emptyPropertyNotEssence {World : Type} {Ind : Type} (F : Frame World) :
    EmptyPropertyNotEssence F Ind := by
  sorry
end TruthCore.Results.Isabelle.GoedelGod.EmptyPropertyNotEssence
